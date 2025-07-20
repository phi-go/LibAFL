/*
   american fuzzy lop++ - LLVM CmpLog instrumentation
   --------------------------------------------------

   Written by Andrea Fioraldi <andreafioraldi@gmail.com>

   Copyright 2015, 2016 Google Inc. All rights reserved.
   Copyright 2019-2020 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

*/

#include <stdio.h>
#include <stdlib.h>
#ifndef _WIN32
  #include <unistd.h>
  #include <sys/time.h>
#endif

#include <list>
#include <string>
#include <fstream>

#include "common-llvm.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/ValueTracking.h"

#include "llvm/IR/Verifier.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/Support/xxhash.h"

#include <set>
#include <unordered_map>
#include <vector>

using namespace llvm;
static cl::opt<bool> CmplogExtended("cmplog_instructions_extended",
                                    cl::desc("Uses extended header"),
                                    cl::init(false), cl::NotHidden);

// Debug information structure for cmplog locations
struct CmplogDebugInfo {
  uint32_t id;         // Deterministic hash-based ID
  uint32_t file_path_index; // Index into string table for source file path
  uint32_t line;       // Source line number
  uint16_t column;     // Source column number
  uint16_t func_hash;  // Hash of function name
  uint8_t  cmp_type;   // Type of comparison (0=ICmp, 1=FCmp, 2=Switch)
  uint8_t  reserved;   // Future use
  uint64_t instruction_addr; // Runtime address of the comparison instruction

  CmplogDebugInfo()
      : id(0),
        file_path_index(0),
        line(0),
        column(0),
        func_hash(0),
        cmp_type(0),
        reserved(0),
        instruction_addr(0) {
  }
};

namespace {

class CmpLogInstructions : public PassInfoMixin<CmpLogInstructions> {
 public:
  CmpLogInstructions() {
  }

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);

 private:
  bool            hookInstrs(Module &M);
  CmplogDebugInfo collectDebugInfo(const Instruction *inst, uint8_t cmp_type);
  uint32_t        generateDeterministicId(const CmplogDebugInfo &debug_info);
  uint32_t        hashString(const StringRef &str);
  void            createDebugInfoTable(Module &M);
  uint32_t        getOrCreateFilePathIndex(const std::string &file_path);
  void            createStringTable(Module &M);
  bool            be_quiet = true;

  // Storage for debug information collected during instrumentation
  std::vector<CmplogDebugInfo>         debug_entries;
  std::unordered_map<uint32_t, size_t> id_to_index;
  // String table for source file paths
  std::vector<std::string>             file_path_strings;
  std::unordered_map<std::string, uint32_t> file_path_to_index;
};

}  // namespace

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "CmpLogInstructions", "v0.1",
          [](PassBuilder &PB) {
#if LLVM_VERSION_MAJOR >= 20
            PB.registerPipelineStartEPCallback(
#else
            PB.registerOptimizerEarlyEPCallback(
#endif
                [](ModulePassManager &MPM, OptimizationLevel OL) {
                  MPM.addPass(CmpLogInstructions());
                });
          }};
}

template <class Iterator>
Iterator Unique(Iterator first, Iterator last) {
  while (first != last) {
    Iterator next(first);
    last = std::remove(++next, last, *first);
    first = next;
  }

  return last;
}

// Hash a string using xxHash for deterministic IDs
uint32_t CmpLogInstructions::hashString(const StringRef &str) {
  return static_cast<uint32_t>(xxHash64(str));
}

// Get or create an index for a file path in the string table
uint32_t CmpLogInstructions::getOrCreateFilePathIndex(const std::string &file_path) {
  auto it = file_path_to_index.find(file_path);
  if (it != file_path_to_index.end()) {
    return it->second;
  }
  
  uint32_t index = static_cast<uint32_t>(file_path_strings.size());
  file_path_strings.push_back(file_path);
  file_path_to_index[file_path] = index;
  return index;
}

// Collect debug information from an instruction
CmplogDebugInfo CmpLogInstructions::collectDebugInfo(const Instruction *inst,
                                                     uint8_t cmp_type) {
  CmplogDebugInfo debug_info;
  debug_info.cmp_type = cmp_type;

  // Store the instruction address for decompilation analysis
  // Note: This will be resolved to actual runtime address at link time
  debug_info.instruction_addr = reinterpret_cast<uint64_t>(inst);

  // Get debug location information
  if (const DILocation *loc = inst->getDebugLoc()) {
    debug_info.line = loc->getLine();
    debug_info.column = loc->getColumn();

    // Store the actual filename in string table
    StringRef filename = loc->getFilename();
    debug_info.file_path_index = getOrCreateFilePathIndex(filename.str());
  }

  // Get function name information
  if (const Function *func = inst->getFunction()) {
    StringRef func_name = func->getName();
    debug_info.func_hash = hashString(func_name);
  }

  // Generate deterministic ID based on collected info
  debug_info.id = generateDeterministicId(debug_info);

  return debug_info;
}

// Generate a deterministic ID from debug information
uint32_t CmpLogInstructions::generateDeterministicId(
    const CmplogDebugInfo &debug_info) {
  uint64_t hash = 0;

  // Combine all debug information into a single hash
  hash ^= static_cast<uint64_t>(debug_info.file_path_index);
  hash ^= static_cast<uint64_t>(debug_info.line) << 16;
  hash ^= static_cast<uint64_t>(debug_info.column) << 8;
  hash ^= static_cast<uint64_t>(debug_info.func_hash) << 24;
  hash ^= static_cast<uint64_t>(debug_info.cmp_type);

  // Use xxHash for final mixing - convert to StringRef for LLVM 19
  // compatibility
  StringRef hash_data(reinterpret_cast<const char *>(&hash), sizeof(hash));
  return static_cast<uint32_t>(xxHash64(hash_data));
}

// Create embedded debug information table in the module
void CmpLogInstructions::createDebugInfoTable(Module &M) {
  if (debug_entries.empty()) return;

  LLVMContext &C = M.getContext();

  // Create struct type for CmplogDebugInfo
  std::vector<Type *> struct_fields = {
      Type::getInt32Ty(C),  // id
      Type::getInt32Ty(C),  // file_path_index
      Type::getInt32Ty(C),  // line
      Type::getInt16Ty(C),  // column
      Type::getInt16Ty(C),  // func_hash
      Type::getInt8Ty(C),   // cmp_type
      Type::getInt8Ty(C),   // reserved
      Type::getInt64Ty(C)   // instruction_addr
  };

  StructType *debug_struct_type =
      StructType::create(C, struct_fields, "CmplogDebugInfo");

  // Convert debug_entries to LLVM constants
  std::vector<Constant *> debug_constants;
  for (const auto &entry : debug_entries) {
    std::vector<Constant *> field_values = {
        ConstantInt::get(Type::getInt32Ty(C), entry.id),
        ConstantInt::get(Type::getInt32Ty(C), entry.file_path_index),
        ConstantInt::get(Type::getInt32Ty(C), entry.line),
        ConstantInt::get(Type::getInt16Ty(C), entry.column),
        ConstantInt::get(Type::getInt16Ty(C), entry.func_hash),
        ConstantInt::get(Type::getInt8Ty(C), entry.cmp_type),
        ConstantInt::get(Type::getInt8Ty(C), entry.reserved),
        ConstantInt::get(Type::getInt64Ty(C), entry.instruction_addr)};
    debug_constants.push_back(
        ConstantStruct::get(debug_struct_type, field_values));
  }

  // Create array type and global variable
  ArrayType *array_type =
      ArrayType::get(debug_struct_type, debug_entries.size());
  Constant *debug_array = ConstantArray::get(array_type, debug_constants);

  GlobalVariable *debug_table =
      new GlobalVariable(M, array_type, true, GlobalValue::ExternalLinkage,
                         debug_array, "__libafl_cmplog_debug_table");
  debug_table->setVisibility(GlobalValue::DefaultVisibility);
  debug_table->setDSOLocal(false);
  // Don't set a custom section - keep it in a standard section for better visibility
  
  // Also create a size variable
  GlobalVariable *debug_table_size = new GlobalVariable(
      M, Type::getInt32Ty(C), true, GlobalValue::ExternalLinkage,
      ConstantInt::get(Type::getInt32Ty(C), debug_entries.size()),
      "__libafl_cmplog_debug_table_size");
  debug_table_size->setVisibility(GlobalValue::DefaultVisibility);
  debug_table_size->setDSOLocal(false);
}

// Create embedded string table for file paths
void CmpLogInstructions::createStringTable(Module &M) {
  if (file_path_strings.empty()) return;

  LLVMContext &C = M.getContext();

  // Create a null-terminated string containing all file paths
  std::string combined_strings;
  std::vector<uint32_t> string_offsets;
  
  for (const auto &file_path : file_path_strings) {
    string_offsets.push_back(static_cast<uint32_t>(combined_strings.size()));
    combined_strings += file_path;
    combined_strings += '\0';  // null terminator
  }

  // Create global string constant
  Constant *string_data = ConstantDataArray::getString(C, combined_strings, false);
  GlobalVariable *string_table = new GlobalVariable(
      M, string_data->getType(), true, GlobalValue::ExternalLinkage,
      string_data, "__libafl_cmplog_string_table");
  string_table->setVisibility(GlobalValue::DefaultVisibility);
  string_table->setDSOLocal(false);

  // Create offset table
  std::vector<Constant *> offset_constants;
  for (uint32_t offset : string_offsets) {
    offset_constants.push_back(ConstantInt::get(Type::getInt32Ty(C), offset));
  }

  ArrayType *offset_array_type = ArrayType::get(Type::getInt32Ty(C), string_offsets.size());
  Constant *offset_array = ConstantArray::get(offset_array_type, offset_constants);
  
  GlobalVariable *offset_table = new GlobalVariable(
      M, offset_array_type, true, GlobalValue::ExternalLinkage,
      offset_array, "__libafl_cmplog_string_offsets");
  offset_table->setVisibility(GlobalValue::DefaultVisibility);
  offset_table->setDSOLocal(false);

  // Create string count variable
  GlobalVariable *string_count = new GlobalVariable(
      M, Type::getInt32Ty(C), true, GlobalValue::ExternalLinkage,
      ConstantInt::get(Type::getInt32Ty(C), file_path_strings.size()),
      "__libafl_cmplog_string_count");
  string_count->setVisibility(GlobalValue::DefaultVisibility);
  string_count->setDSOLocal(false);
}

bool CmpLogInstructions::hookInstrs(Module &M) {
  std::vector<Instruction *> icomps;
  std::vector<SwitchInst *>  switches;
  LLVMContext               &C = M.getContext();

  Type        *VoidTy = Type::getVoidTy(C);
  IntegerType *Int8Ty = IntegerType::getInt8Ty(C);
  IntegerType *Int16Ty = IntegerType::getInt16Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  IntegerType *Int128Ty = IntegerType::getInt128Ty(C);

  // Traditional hook functions (for backward compatibility)
  FunctionCallee cmplogHookIns1;
  FunctionCallee cmplogHookIns2;
  FunctionCallee cmplogHookIns4;
  FunctionCallee cmplogHookIns8;
#ifndef _WIN32
  FunctionCallee cmplogHookIns16;
  FunctionCallee cmplogHookInsN;
#endif

  // New hook functions with deterministic ID parameter
  FunctionCallee cmplogHookIns1WithId;
  FunctionCallee cmplogHookIns2WithId;
  FunctionCallee cmplogHookIns4WithId;
  FunctionCallee cmplogHookIns8WithId;
#ifndef _WIN32
  FunctionCallee cmplogHookIns16WithId;
  FunctionCallee cmplogHookInsNWithId;
#endif
  if (CmplogExtended) {
    cmplogHookIns1 = M.getOrInsertFunction("__cmplog_ins_hook1_extended",
                                           VoidTy, Int8Ty, Int8Ty, Int8Ty);
  } else {
    cmplogHookIns1 = M.getOrInsertFunction("__cmplog_ins_hook1", VoidTy, Int8Ty,
                                           Int8Ty, Int8Ty);
  }

  if (CmplogExtended) {
    cmplogHookIns2 = M.getOrInsertFunction("__cmplog_ins_hook2_extended",
                                           VoidTy, Int16Ty, Int16Ty, Int8Ty);
  } else {
    cmplogHookIns2 = M.getOrInsertFunction("__cmplog_ins_hook2", VoidTy,
                                           Int16Ty, Int16Ty, Int8Ty);
  }

  if (CmplogExtended) {
    cmplogHookIns4 = M.getOrInsertFunction("__cmplog_ins_hook4_extended",
                                           VoidTy, Int32Ty, Int32Ty, Int8Ty);
  } else {
    cmplogHookIns4 = M.getOrInsertFunction("__cmplog_ins_hook4", VoidTy,
                                           Int32Ty, Int32Ty, Int8Ty);
  }

  if (CmplogExtended) {
    cmplogHookIns8 = M.getOrInsertFunction("__cmplog_ins_hook8_extended",
                                           VoidTy, Int64Ty, Int64Ty, Int8Ty);
  } else {
    cmplogHookIns8 = M.getOrInsertFunction("__cmplog_ins_hook8", VoidTy,
                                           Int64Ty, Int64Ty, Int8Ty);
  }

#ifndef _WIN32
  if (CmplogExtended) {
    cmplogHookIns16 = M.getOrInsertFunction("__cmplog_ins_hook16_extended",
                                            VoidTy, Int128Ty, Int128Ty, Int8Ty);
  } else {
    cmplogHookIns16 = M.getOrInsertFunction("__cmplog_ins_hook16", VoidTy,
                                            Int128Ty, Int128Ty, Int8Ty);
  }

  if (CmplogExtended) {
    cmplogHookInsN = M.getOrInsertFunction("__cmplog_ins_hookN_extended",
                                           VoidTy, Int128Ty, Int128Ty, Int8Ty);
  } else {
    cmplogHookInsN = M.getOrInsertFunction("__cmplog_ins_hookN", VoidTy,
                                           Int128Ty, Int128Ty, Int8Ty);
  }
#endif

  // Declare new hook functions that accept deterministic IDs as first parameter
  // We'll use the constant-aware versions
  cmplogHookIns1WithId = M.getOrInsertFunction(
      "__cmplog_ins_hook1_with_id_const", VoidTy, Int32Ty, Int8Ty, Int8Ty, Int8Ty);

  cmplogHookIns2WithId = M.getOrInsertFunction(
      "__cmplog_ins_hook2_with_id_const", VoidTy, Int32Ty, Int16Ty, Int16Ty, Int8Ty);

  cmplogHookIns4WithId = M.getOrInsertFunction(
      "__cmplog_ins_hook4_with_id_const", VoidTy, Int32Ty, Int32Ty, Int32Ty, Int8Ty);

  cmplogHookIns8WithId = M.getOrInsertFunction(
      "__cmplog_ins_hook8_with_id_const", VoidTy, Int32Ty, Int64Ty, Int64Ty, Int8Ty);

#ifndef _WIN32
  cmplogHookIns16WithId = M.getOrInsertFunction(
      "__cmplog_ins_hook16_with_id_const", VoidTy, Int32Ty, Int128Ty, Int128Ty, Int8Ty);

  cmplogHookInsNWithId = M.getOrInsertFunction(
      "__cmplog_ins_hookN_with_id_const", VoidTy, Int32Ty, Int128Ty, Int128Ty, Int8Ty, Int8Ty);
#endif

  Constant *Null = Constant::getNullValue(PointerType::get(Int8Ty, 0));

  /* iterate over all functions, bbs and instruction and add suitable calls */
  for (auto &F : M) {
    if (isIgnoreFunction(&F)) { continue; }

    for (auto &BB : F) {
      for (auto &IN : BB) {
        CmpInst *selectcmpInst = nullptr;
        if ((selectcmpInst = dyn_cast<CmpInst>(&IN))) {
          icomps.push_back(selectcmpInst);
        }
      }
    }

    for (auto &BB : F) {
      SwitchInst *switchInst = nullptr;
      if ((switchInst = dyn_cast<SwitchInst>(BB.getTerminator()))) {
        if (switchInst->getNumCases() > 1) { switches.push_back(switchInst); }
      }
    }
  }

  switches.erase(Unique(switches.begin(), switches.end()), switches.end());
  if (icomps.size()) {
    // if (!be_quiet) errs() << "Hooking " << icomps.size() <<
    //                          " cmp instructions\n";

    for (auto &selectcmpInst : icomps) {
      IRBuilder<> IRB(selectcmpInst->getParent());
      IRB.SetInsertPoint(selectcmpInst);

      // Collect debug information for this comparison instruction
      uint8_t  cmp_type = 0;  // Will be set based on instruction type
      CmpInst *cmpInst = dyn_cast<CmpInst>(selectcmpInst);
      if (!cmpInst) { continue; }

      // Determine comparison type (ICmp vs FCmp)
      if (selectcmpInst->getOpcode() == Instruction::FCmp) {
        cmp_type = 1;  // FCmp
      } else {
        cmp_type = 0;  // ICmp
      }

      // We'll collect debug info later, after we know this comparison will be instrumented
      uint32_t deterministic_id = 0;  // Will be set later

      Value *op0 = selectcmpInst->getOperand(0);
      Value *op1 = selectcmpInst->getOperand(1);
      Value *op0_saved = op0, *op1_saved = op1;
      auto   ty0 = op0->getType();
      auto   ty1 = op1->getType();

      IntegerType *intTyOp0 = NULL;
      IntegerType *intTyOp1 = NULL;
      unsigned     max_size = 0, cast_size = 0;
      unsigned     attr = 0, vector_cnt = 0, is_fp = 0;

      switch (cmpInst->getPredicate()) {
        case CmpInst::ICMP_NE:
        case CmpInst::FCMP_UNE:
        case CmpInst::FCMP_ONE:
          break;
        case CmpInst::ICMP_EQ:
        case CmpInst::FCMP_UEQ:
        case CmpInst::FCMP_OEQ:
          attr += 1;
          break;
        case CmpInst::ICMP_UGT:
        case CmpInst::ICMP_SGT:
        case CmpInst::FCMP_OGT:
        case CmpInst::FCMP_UGT:
          attr += 2;
          break;
        case CmpInst::ICMP_UGE:
        case CmpInst::ICMP_SGE:
        case CmpInst::FCMP_OGE:
        case CmpInst::FCMP_UGE:
          attr += 3;
          break;
        case CmpInst::ICMP_ULT:
        case CmpInst::ICMP_SLT:
        case CmpInst::FCMP_OLT:
        case CmpInst::FCMP_ULT:
          attr += 4;
          break;
        case CmpInst::ICMP_ULE:
        case CmpInst::ICMP_SLE:
        case CmpInst::FCMP_OLE:
        case CmpInst::FCMP_ULE:
          attr += 5;
          break;
        default:
          break;
      }

      if (selectcmpInst->getOpcode() == Instruction::FCmp) {
        if (ty0->isVectorTy()) {
          VectorType *tt = dyn_cast<VectorType>(ty0);
          if (!tt) {
            fprintf(stderr, "Warning: cmplog cmp vector is not a vector!\n");
            continue;
          }

          vector_cnt = tt->getElementCount().getKnownMinValue();
          ty0 = tt->getElementType();
        }

        if (ty0->isHalfTy() || ty0->isBFloatTy())
          max_size = 16;
        else if (ty0->isFloatTy())
          max_size = 32;
        else if (ty0->isDoubleTy())
          max_size = 64;
        else if (ty0->isX86_FP80Ty())
          max_size = 80;
        else if (ty0->isFP128Ty() || ty0->isPPC_FP128Ty())
          max_size = 128;
        else if (ty0->getTypeID() != llvm::Type::PointerTyID && !be_quiet)
          fprintf(stderr, "Warning: unsupported cmp type for cmplog: %u!\n",
                  ty0->getTypeID());

        attr += 8;
        is_fp = 1;
        // fprintf(stderr, "HAVE FP %u!\n", vector_cnt);

      } else {
        if (ty0->isVectorTy()) {
          VectorType *tt = dyn_cast<VectorType>(ty0);
          if (!tt) {
            fprintf(stderr, "Warning: cmplog cmp vector is not a vector!\n");
            continue;
          }

          vector_cnt = tt->getElementCount().getKnownMinValue();
          ty1 = ty0 = tt->getElementType();
        }

        intTyOp0 = dyn_cast<IntegerType>(ty0);
        intTyOp1 = dyn_cast<IntegerType>(ty1);

        if (intTyOp0 && intTyOp1) {
          max_size = intTyOp0->getBitWidth() > intTyOp1->getBitWidth()
                         ? intTyOp0->getBitWidth()
                         : intTyOp1->getBitWidth();

        } else {
          if (ty0->getTypeID() != llvm::Type::PointerTyID && !be_quiet) {
            fprintf(stderr, "Warning: unsupported cmp type for cmplog: %u\n",
                    ty0->getTypeID());
          }
        }
      }

      if (!max_size || max_size < 8) {
        continue;
      }

      if (max_size % 8) { max_size = (((max_size / 8) + 1) * 8); }

      if (max_size > 128) {
        if (!be_quiet) {
          fprintf(stderr,
                  "Cannot handle this compare bit size: %u (truncating)\n",
                  max_size);
        }

        max_size = 128;
      }

      // do we need to cast?
      switch (max_size) {
        case 8:
        case 16:
        case 32:
        case 64:
        case 128:
          cast_size = max_size;
          break;
        default:
          cast_size = 128;
      }

      // XXX FIXME BUG TODO
      if (is_fp && vector_cnt) { continue; }

      // Now we know this comparison will be instrumented - collect debug info
      CmplogDebugInfo debug_info = collectDebugInfo(selectcmpInst, cmp_type);

      // Apply the same mask that will be used at runtime (CMPLOG_MAP_W - 1)
      const uint32_t CMPLOG_MAP_W = 65536;
      debug_info.id = debug_info.id & (CMPLOG_MAP_W - 1);

      // Check for duplicate IDs and handle collisions
      if (id_to_index.find(debug_info.id) == id_to_index.end()) {
        id_to_index[debug_info.id] = debug_entries.size();
        debug_entries.push_back(debug_info);
      }

      deterministic_id = debug_info.id;

      uint64_t cur = 0, last_val0 = 0, last_val1 = 0, cur_val;

      while (1) {
        std::vector<Value *> args;
        bool                 skip = false;

        if (vector_cnt) {
          op0 = IRB.CreateExtractElement(op0_saved, cur);
          op1 = IRB.CreateExtractElement(op1_saved, cur);
          /*
          std::string errMsg;
          raw_string_ostream os(errMsg);
          op0_saved->print(os);
          fprintf(stderr, "X: %s\n", os.str().c_str());
          */
          if (is_fp) {
            /*
                        ConstantFP *i0 = dyn_cast<ConstantFP>(op0);
                        ConstantFP *i1 = dyn_cast<ConstantFP>(op1);
                        // BUG FIXME TODO: this is null ... but why?
                        // fprintf(stderr, "%p %p\n", i0, i1);
                        if (i0) {

                          cur_val = (uint64_t)i0->getValue().convertToDouble();
                          if (last_val0 && last_val0 == cur_val) { skip = true;

               } last_val0 = cur_val;

                        }

                        if (i1) {

                          cur_val = (uint64_t)i1->getValue().convertToDouble();
                          if (last_val1 && last_val1 == cur_val) { skip = true;

               } last_val1 = cur_val;

                        }

            */

          } else {
            ConstantInt *i0 = dyn_cast<ConstantInt>(op0);
            ConstantInt *i1 = dyn_cast<ConstantInt>(op1);
            if (i0 && i0->uge(0xffffffffffffffff) == false) {
              cur_val = i0->getZExtValue();
              if (last_val0 && last_val0 == cur_val) { skip = true; }
              last_val0 = cur_val;
            }

            if (i1 && i1->uge(0xffffffffffffffff) == false) {
              cur_val = i1->getZExtValue();
              if (last_val1 && last_val1 == cur_val) { skip = true; }
              last_val1 = cur_val;
            }
          }
        }

        if (!skip) {
          // errs() << "[CMPLOG] cmp  " << *cmpInst << "(in function " <<
          // cmpInst->getFunction()->getName() << ")\n";

          // Add deterministic ID as first parameter
          Value *id_arg = ConstantInt::get(Int32Ty, deterministic_id);
          args.push_back(id_arg);

          // Check if operands are constants and normalize so constant is first
          uint8_t arg1_is_const = 0;
          Value *first_op = op0;
          Value *second_op = op1;
          Type *first_ty = ty0;
          Type *second_ty = ty1;
          
          bool op0_is_const = isa<Constant>(op0) && !isa<ConstantExpr>(op0);
          bool op1_is_const = isa<Constant>(op1) && !isa<ConstantExpr>(op1);
          
          // If only the second operand is constant, swap operands
          if (!op0_is_const && op1_is_const) {
            first_op = op1;
            second_op = op0;
            first_ty = ty1;
            second_ty = ty0;
            arg1_is_const = 1;
          } else if (op0_is_const) {
            // First operand is already constant, keep as is
            arg1_is_const = 1;
          }

          // first bitcast to integer type of the same bitsize as the original
          // type (this is a nop, if already integer)
          Value *op0_i = IRB.CreateBitCast(
              first_op, IntegerType::get(C, first_ty->getPrimitiveSizeInBits()));
          // then create a int cast, which does zext, trunc or bitcast. In our
          // case usually zext to the next larger supported type (this is a nop
          // if already the right type)
          Value *V0 =
              IRB.CreateIntCast(op0_i, IntegerType::get(C, cast_size), false);
          args.push_back(V0);
          Value *op1_i = IRB.CreateBitCast(
              second_op, IntegerType::get(C, second_ty->getPrimitiveSizeInBits()));
          Value *V1 =
              IRB.CreateIntCast(op1_i, IntegerType::get(C, cast_size), false);
          args.push_back(V1);

          // errs() << "[CMPLOG] casted parameters:\n0: " << *V0 << "\n1: " <<
          // *V1
          // << "\n";

          if (CmplogExtended) {
            // Only do this when using extended header
            ConstantInt *attribute = ConstantInt::get(Int8Ty, attr);
            args.push_back(attribute);
          }
#ifndef _WIN32
          if (cast_size != max_size) {
            ConstantInt *bitsize = ConstantInt::get(Int8Ty, (max_size / 8) - 1);
            args.push_back(bitsize);
          }
#endif

          // Add the constant flag as the final parameter
          ConstantInt *arg1_is_const_arg = ConstantInt::get(Int8Ty, arg1_is_const);
          args.push_back(arg1_is_const_arg);

          // fprintf(stderr, "_ExtInt(%u) castTo %u with attr %u didcast %u\n",
          //         max_size, cast_size, attr);

          switch (cast_size) {
            case 8:
              IRB.CreateCall(cmplogHookIns1WithId, args);
              break;
            case 16:
              IRB.CreateCall(cmplogHookIns2WithId, args);
              break;
            case 32:
              IRB.CreateCall(cmplogHookIns4WithId, args);
              break;
            case 64:
              IRB.CreateCall(cmplogHookIns8WithId, args);
              break;
#ifndef _WIN32
            case 128:
              if (max_size == 128) {
                IRB.CreateCall(cmplogHookIns16WithId, args);

              } else {
                IRB.CreateCall(cmplogHookInsNWithId, args);
              }

              break;
#endif
          }
        }

        /* else fprintf(stderr, "skipped\n"); */

        ++cur;
        if (cur >= vector_cnt) { break; }
      }
    }
  }

  if (switches.size()) {
    for (auto &SI : switches) {
      // We'll collect debug info later, after we know this switch will be instrumented
      uint32_t deterministic_id = 0;  // Will be set later

      Value        *Val = SI->getCondition();
      unsigned int  max_size = Val->getType()->getIntegerBitWidth();
      unsigned int  cast_size;
      unsigned char do_cast = 0;

      if (!SI->getNumCases() || max_size < 16) {
        // skipping trivial switch
        continue;
      }

      if (max_size % 8) {
        max_size = (((max_size / 8) + 1) * 8);
        do_cast = 1;
      }

      if (max_size > 128) {
        // can't handle this

        max_size = 128;
        do_cast = 1;
      }

      // Now we know this switch will be instrumented - collect debug info
      CmplogDebugInfo debug_info = collectDebugInfo(SI, 2);  // Switch type = 2

      // Apply the same mask that will be used at runtime (CMPLOG_MAP_W - 1)
      const uint32_t CMPLOG_MAP_W = 65536;
      debug_info.id = debug_info.id & (CMPLOG_MAP_W - 1);

      // Check for duplicate IDs and handle collisions
      if (id_to_index.find(debug_info.id) == id_to_index.end()) {
        id_to_index[debug_info.id] = debug_entries.size();
        debug_entries.push_back(debug_info);
      }

      deterministic_id = debug_info.id;

      IRBuilder<> IRB(SI->getParent());
      IRB.SetInsertPoint(SI);

      switch (max_size) {
        case 8:
        case 16:
        case 32:
        case 64:
        case 128:
          cast_size = max_size;
          break;
        default:
          cast_size = 128;
          do_cast = 1;
      }

      // The predicate of the switch clause
      Value *CompareTo = Val;
      if (do_cast) {
        CompareTo =
            IRB.CreateIntCast(CompareTo, IntegerType::get(C, cast_size), false);
      }

      for (SwitchInst::CaseIt i = SI->case_begin(), e = SI->case_end(); i != e;
           ++i) {
        // Who uses LLVM Major < 5?? :p
        ConstantInt *cint = i->getCaseValue();

        if (cint) {
          std::vector<Value *> args;

          // Add deterministic ID as first parameter
          Value *id_arg = ConstantInt::get(Int32Ty, deterministic_id);
          args.push_back(id_arg);

          // For switch instructions, put the constant first (case value)
          Value *new_param = cint;
          if (do_cast) {
            new_param =
                IRB.CreateIntCast(cint, IntegerType::get(C, cast_size), false);
          }

          if (new_param) {
            // Add constant case value as first operand
            args.push_back(new_param);
            // Add switch value as second operand
            args.push_back(CompareTo);
            
            // Case constant is always constant and is now the first operand
            uint8_t arg1_is_const = 1;
            
            if (CmplogExtended) {
              ConstantInt *attribute = ConstantInt::get(Int8Ty, 1);
              args.push_back(attribute);
            }
            if (cast_size != max_size) {
              // not 8, 16, 32, 64, 128.
              ConstantInt *bitsize =
                  ConstantInt::get(Int8Ty, (max_size / 8) - 1);
              args.push_back(bitsize);  // we have the arg for size in hookinsN
            }
            
            // Add the constant flag as the final parameter
            ConstantInt *arg1_is_const_arg = ConstantInt::get(Int8Ty, arg1_is_const);
            args.push_back(arg1_is_const_arg);

            switch (cast_size) {
              case 8:
                IRB.CreateCall(cmplogHookIns1WithId, args);
                break;
              case 16:
                IRB.CreateCall(cmplogHookIns2WithId, args);
                break;
              case 32:
                IRB.CreateCall(cmplogHookIns4WithId, args);
                break;
              case 64:
                IRB.CreateCall(cmplogHookIns8WithId, args);
                break;
              case 128:
#ifdef WORD_SIZE_64
                if (max_size == 128) {
                  IRB.CreateCall(cmplogHookIns16WithId, args);

                } else {
                  IRB.CreateCall(cmplogHookInsNWithId, args);
                }

#endif
                break;
              default:
                break;
            }
          }
        }
      }
    }
  }

  // Create the embedded debug information table and string table
  createStringTable(M);
  createDebugInfoTable(M);

  return true;
}

PreservedAnalyses CmpLogInstructions::run(Module                &M,
                                          ModuleAnalysisManager &MAM) {
  hookInstrs(M);

  auto PA = PreservedAnalyses::all();
  verifyModule(M);

  return PA;
}
