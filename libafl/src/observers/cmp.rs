//! The `CmpObserver` provides access to the logged values of CMP instructions
use alloc::{
    borrow::Cow,
    string::{String, ToString},
    vec::Vec,
};
use core::{
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use arbitrary_int::{u1, u4, u5, u6};
use bitbybit::bitfield;
use hashbrown::HashMap;
use libafl_bolts::{AsSlice, HasLen, Named, ownedref::OwnedRefMut};
use serde::{Deserialize, Serialize};

use crate::{Error, HasMetadata, executors::ExitKind, observers::Observer};

/// Debug information for a cmplog location
#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
#[repr(C)]
pub struct CmplogDebugInfo {
    /// Deterministic hash-based ID
    pub id: u32,
    /// Index into string table for source file path
    pub file_path_index: u32,
    /// Source line number
    pub line: u32,
    /// Source column number
    pub column: u16,
    /// Index into function name string table
    pub func_name_index: u32,
    /// Type of comparison (0=ICmp, 1=FCmp, 2=Switch)
    pub cmp_type: u8,
    /// Reserved for future use
    pub reserved: u8,
    /// Runtime address of the comparison instruction
    pub instruction_addr: u64,
}

impl CmplogDebugInfo {
    /// Create a new debug info entry
    pub fn new(
        id: u32,
        file_path_index: u32,
        line: u32,
        column: u16,
        func_name_index: u32,
        cmp_type: u8,
        instruction_addr: u64,
    ) -> Self {
        Self {
            id,
            file_path_index,
            line,
            column,
            func_name_index,
            cmp_type,
            reserved: 0,
            instruction_addr,
        }
    }

    /// Get the comparison type as a string
    pub fn cmp_type_str(&self) -> &'static str {
        match self.cmp_type {
            0 => "ICmp",
            1 => "FCmp",
            2 => "Switch",
            _ => "Unknown",
        }
    }
}

/// Debug resolver for looking up cmplog debug information at runtime
#[derive(Debug, Clone)]
pub struct CmplogDebugResolver {
    debug_table: HashMap<u32, CmplogDebugInfo>,
    file_paths: Vec<String>,
    function_names: HashMap<u32, String>,
}

impl Default for CmplogDebugResolver {
    fn default() -> Self {
        Self::new()
    }
}

impl CmplogDebugResolver {
    /// Create a new debug resolver
    pub fn new() -> Self {
        Self {
            debug_table: HashMap::new(),
            file_paths: Vec::new(),
            function_names: HashMap::new(),
        }
    }

    /// Load debug information from embedded executable section
    #[cfg(target_os = "linux")]
    pub fn load_from_executable() -> Result<Self, Error> {
        use core::ptr;

        let mut resolver = Self::new();

        // Try to load debug information using dlsym to check for symbol existence
        // This avoids weak linkage issues and works on stable Rust
        #[cfg(feature = "std")]
        unsafe {
            use std::ffi::CString;

            // Helper function to load symbols from a library handle
            let load_symbols = |lib_handle: *mut std::ffi::c_void| -> (
                Option<*mut std::ffi::c_void>,
                Option<*mut std::ffi::c_void>,
                Option<*mut std::ffi::c_void>,
                Option<*mut std::ffi::c_void>,
                Option<*mut std::ffi::c_void>,
                Option<*mut std::ffi::c_void>,
                Option<*mut std::ffi::c_void>,
                Option<*mut std::ffi::c_void>,
            ) {
                let table_name = CString::new("__libafl_cmplog_debug_table").unwrap();
                let size_name = CString::new("__libafl_cmplog_debug_table_size").unwrap();
                let string_table_name = CString::new("__libafl_cmplog_string_table").unwrap();
                let string_offsets_name = CString::new("__libafl_cmplog_string_offsets").unwrap();
                let string_count_name = CString::new("__libafl_cmplog_string_count").unwrap();
                let function_name_table_name =
                    CString::new("__libafl_cmplog_function_name_table").unwrap();
                let function_name_offsets_name =
                    CString::new("__libafl_cmplog_function_name_offsets").unwrap();
                let function_name_count_name =
                    CString::new("__libafl_cmplog_function_name_count").unwrap();

                let table_ptr = libc::dlsym(lib_handle, table_name.as_ptr());
                let size_ptr = libc::dlsym(lib_handle, size_name.as_ptr());
                let string_table_ptr = libc::dlsym(lib_handle, string_table_name.as_ptr());
                let string_offsets_ptr = libc::dlsym(lib_handle, string_offsets_name.as_ptr());
                let string_count_ptr = libc::dlsym(lib_handle, string_count_name.as_ptr());
                let function_name_table_ptr =
                    libc::dlsym(lib_handle, function_name_table_name.as_ptr());
                let function_name_offsets_ptr =
                    libc::dlsym(lib_handle, function_name_offsets_name.as_ptr());
                let function_name_count_ptr =
                    libc::dlsym(lib_handle, function_name_count_name.as_ptr());

                (
                    if table_ptr.is_null() {
                        None
                    } else {
                        Some(table_ptr)
                    },
                    if size_ptr.is_null() {
                        None
                    } else {
                        Some(size_ptr)
                    },
                    if string_table_ptr.is_null() {
                        None
                    } else {
                        Some(string_table_ptr)
                    },
                    if string_offsets_ptr.is_null() {
                        None
                    } else {
                        Some(string_offsets_ptr)
                    },
                    if string_count_ptr.is_null() {
                        None
                    } else {
                        Some(string_count_ptr)
                    },
                    if function_name_table_ptr.is_null() {
                        None
                    } else {
                        Some(function_name_table_ptr)
                    },
                    if function_name_offsets_ptr.is_null() {
                        None
                    } else {
                        Some(function_name_offsets_ptr)
                    },
                    if function_name_count_ptr.is_null() {
                        None
                    } else {
                        Some(function_name_count_ptr)
                    },
                )
            };

            // Try multiple approaches to get the symbols
            let (
                mut table_ptr,
                mut size_ptr,
                mut string_table_ptr,
                mut string_offsets_ptr,
                mut string_count_ptr,
                mut function_name_table_ptr,
                mut function_name_offsets_ptr,
                mut function_name_count_ptr,
            );

            // First try: RTLD_DEFAULT
            let lib_handle = libc::RTLD_DEFAULT as *mut std::ffi::c_void;
            (
                table_ptr,
                size_ptr,
                string_table_ptr,
                string_offsets_ptr,
                string_count_ptr,
                function_name_table_ptr,
                function_name_offsets_ptr,
                function_name_count_ptr,
            ) = load_symbols(lib_handle);

            // Second try: current executable
            if table_ptr.is_none() || size_ptr.is_none() {
                // Get current executable path and open it
                let exe_path = std::fs::read_link("/proc/self/exe")
                    .unwrap_or_else(|_| std::path::PathBuf::from(""));

                if !exe_path.as_os_str().is_empty() {
                    let exe_cstr = CString::new(exe_path.to_string_lossy().as_ref()).unwrap();
                    let lib_handle = libc::dlopen(exe_cstr.as_ptr(), libc::RTLD_LAZY);

                    if !lib_handle.is_null() {
                        (
                            table_ptr,
                            size_ptr,
                            string_table_ptr,
                            string_offsets_ptr,
                            string_count_ptr,
                            function_name_table_ptr,
                            function_name_offsets_ptr,
                            function_name_count_ptr,
                        ) = load_symbols(lib_handle);
                        libc::dlclose(lib_handle);
                    }
                }
            }

            // Check if symbols were found
            if table_ptr.is_none() || size_ptr.is_none() {
                // No debug information embedded
                eprintln!("debug symbols not found");
                return Ok(resolver);
            }

            let table_ptr = table_ptr.unwrap();
            let size_ptr = size_ptr.unwrap();

            // Load string table if available
            if let (Some(string_table_ptr), Some(string_offsets_ptr), Some(string_count_ptr)) =
                (string_table_ptr, string_offsets_ptr, string_count_ptr)
            {
                let string_count = ptr::read(string_count_ptr as *const u32) as usize;
                if string_count > 0 {
                    eprintln!("Found {} file path strings", string_count);

                    let string_data_ptr = string_table_ptr as *const u8;
                    let offsets_ptr = string_offsets_ptr as *const u32;

                    for i in 0..string_count {
                        let offset = ptr::read(offsets_ptr.add(i)) as isize;
                        let str_ptr = string_data_ptr.offset(offset);

                        // Read null-terminated string
                        let mut len = 0;
                        while ptr::read(str_ptr.add(len)) != 0 {
                            len += 1;
                        }

                        let str_bytes = core::slice::from_raw_parts(str_ptr, len);
                        if let Ok(file_path) = std::str::from_utf8(str_bytes) {
                            resolver.add_file_path(file_path.to_string());
                        }
                    }
                }
            }

            // Load function name table if available
            if let (
                Some(function_name_table_ptr),
                Some(function_name_offsets_ptr),
                Some(function_name_count_ptr),
            ) = (
                function_name_table_ptr,
                function_name_offsets_ptr,
                function_name_count_ptr,
            ) {
                let function_name_count = ptr::read(function_name_count_ptr as *const u32) as usize;
                if function_name_count > 0 {
                    eprintln!("Found {} function names", function_name_count);

                    let function_name_data_ptr = function_name_table_ptr as *const u8;
                    let function_name_offsets_ptr = function_name_offsets_ptr as *const u32;

                    for i in 0..function_name_count {
                        let offset = ptr::read(function_name_offsets_ptr.add(i)) as isize;
                        let str_ptr = function_name_data_ptr.offset(offset);

                        // Read null-terminated string
                        let mut len = 0;
                        while ptr::read(str_ptr.add(len)) != 0 {
                            len += 1;
                        }

                        let str_bytes = core::slice::from_raw_parts(str_ptr, len);
                        if let Ok(function_name) = std::str::from_utf8(str_bytes) {
                            resolver.add_function_name(i as u32, function_name.to_string());
                        }
                    }
                }
            }

            // The table_size_ptr actually contains the number of entries, not bytes
            let num_entries = ptr::read(size_ptr as *const u32) as usize;
            if num_entries == 0 {
                eprintln!("zero entries");
                // No debug information embedded
                return Ok(resolver);
            }

            eprintln!("Found {} debug entries", num_entries);
            let debug_table_ptr = table_ptr as *const CmplogDebugInfo;

            // Read each debug entry from the embedded table
            for i in 0..num_entries {
                let entry_ptr = debug_table_ptr.add(i);
                let entry = ptr::read(entry_ptr);
                resolver.add_debug_info(entry);
            }
        }

        Ok(resolver)
    }

    /// Load debug information from embedded executable section
    #[cfg(not(target_os = "linux"))]
    pub fn load_from_executable() -> Result<Self, Error> {
        // Platform not yet supported
        Ok(Self::new())
    }

    /// Add a debug info entry manually (useful for testing)
    pub fn add_debug_info(&mut self, debug_info: CmplogDebugInfo) {
        self.debug_table.insert(debug_info.id, debug_info);
    }

    /// Load file paths from the string table
    pub fn load_file_paths(&mut self, file_paths: Vec<String>) {
        self.file_paths = file_paths;
    }

    /// Add a file path by index
    pub fn add_file_path(&mut self, path: String) {
        self.file_paths.push(path);
    }

    /// Add a function name mapping
    pub fn add_function_name(&mut self, index: u32, name: String) {
        self.function_names.insert(index, name);
    }

    /// Resolve debug information for a comparison ID
    pub fn resolve(&self, cmp_id: u32) -> Option<&CmplogDebugInfo> {
        self.debug_table.get(&cmp_id)
    }

    /// Resolve debug information for a masked comparison ID (CmpValuesId)
    /// CmpValuesId = deterministic_id & (CMPLOG_MAP_W - 1)
    pub fn resolve_masked(&self, masked_cmp_id: u32) -> Option<&CmplogDebugInfo> {
        const CMPLOG_MAP_W: u32 = 65536; // Default value from libafl_targets
        let mask = CMPLOG_MAP_W - 1;

        // Find the debug entry whose ID when masked matches the given masked_cmp_id
        for debug_info in self.debug_table.values() {
            if (debug_info.id & mask) == masked_cmp_id {
                return Some(debug_info);
            }
        }
        None
    }

    /// Get the file path for a file path index
    pub fn get_file_path(&self, file_path_index: u32) -> Option<&str> {
        self.file_paths
            .get(file_path_index as usize)
            .map(|s| s.as_str())
    }

    /// Get the instruction address for a comparison ID
    pub fn get_instruction_addr(&self, cmp_id: u32) -> Option<u64> {
        self.debug_table
            .get(&cmp_id)
            .map(|info| info.instruction_addr)
    }

    /// Get the function name for a function name index
    pub fn get_function_name(&self, func_name_index: u32) -> Option<&str> {
        self.function_names
            .get(&func_name_index)
            .map(|s| s.as_str())
    }

    /// Get full debug information for a comparison ID including resolved names
    /// Uses direct resolution since both CmpValuesId and debug IDs are already masked
    pub fn resolve_full(&self, cmp_id: u32) -> Option<CmplogDebugLocation> {
        let debug_info = self.resolve(cmp_id)?;

        Some(CmplogDebugLocation {
            id: debug_info.id,
            line: debug_info.line,
            column: debug_info.column,
            cmp_type: debug_info.cmp_type,
            file_name: self
                .get_file_path(debug_info.file_path_index)
                .map(|s| s.to_string()),
            function_name: self
                .get_function_name(debug_info.func_name_index)
                .map(|s| s.to_string()),
        })
    }

    /// Get all debug information entries
    pub fn all_entries(&self) -> impl Iterator<Item = (&u32, &CmplogDebugInfo)> {
        self.debug_table.iter()
    }

    /// Get the number of debug entries
    pub fn len(&self) -> usize {
        self.debug_table.len()
    }

    /// Check if the resolver is empty
    pub fn is_empty(&self) -> bool {
        self.debug_table.is_empty()
    }
}

/// Full debug location information with resolved names
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CmplogDebugLocation {
    /// Deterministic hash-based ID
    pub id: u32,
    /// Source line number
    pub line: u32,
    /// Source column number
    pub column: u16,
    /// Type of comparison (0=ICmp, 1=FCmp, 2=Switch)
    pub cmp_type: u8,
    /// Resolved file name (if available)
    pub file_name: Option<String>,
    /// Resolved function name (if available)
    pub function_name: Option<String>,
}

impl CmplogDebugLocation {
    /// Get the comparison type as a string
    pub fn cmp_type_str(&self) -> &'static str {
        match self.cmp_type {
            0 => "ICmp",
            1 => "FCmp",
            2 => "Switch",
            _ => "Unknown",
        }
    }

    /// Format as a human-readable string
    pub fn format(&self) -> String {
        let file = self.file_name.as_deref().unwrap_or("<unknown>");
        let func = self.function_name.as_deref().unwrap_or("<unknown>");
        format!(
            "{}:{} in {} ({}:{})",
            file,
            self.line,
            func,
            self.cmp_type_str(),
            self.id
        )
    }
}

/// A bytes string for cmplog with up to 32 elements.
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub struct CmplogBytes {
    buf: [u8; 32],
    len: u8,
}

impl CmplogBytes {
    /// Creates a new [`CmplogBytes`] object from the provided buf and length.
    /// Lengths above 32 are illegal but will be ignored.
    #[must_use]
    pub fn from_buf_and_len(buf: [u8; 32], len: u8) -> Self {
        debug_assert!(len <= 32, "Len too big: {len}, max: 32");
        CmplogBytes { buf, len }
    }
}

impl<'a> AsSlice<'a> for CmplogBytes {
    type Entry = u8;

    type SliceRef = &'a [u8];

    fn as_slice(&'a self) -> Self::SliceRef {
        &self.buf[0..(self.len as usize)]
    }
}

impl HasLen for CmplogBytes {
    fn len(&self) -> usize {
        self.len as usize
    }
}

/// Compare values collected during a run
#[derive(Eq, PartialEq, Debug, Serialize, Deserialize, Clone)]
pub enum CmpValues {
    /// (side 1 of comparison, side 2 of comparison, side 1 value is const)
    U8((u8, u8, bool, usize)),
    /// (side 1 of comparison, side 2 of comparison, side 1 value is const)
    U16((u16, u16, bool, usize)),
    /// (side 1 of comparison, side 2 of comparison, side 1 value is const)
    U32((u32, u32, bool, usize)),
    /// (side 1 of comparison, side 2 of comparison, side 1 value is const)
    U64((u64, u64, bool, usize)),
    /// Two vecs of u8 values/byte
    Bytes((CmplogBytes, CmplogBytes, usize)),
}

impl CmpValues {
    /// Returns if the values are numericals
    #[must_use]
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
            CmpValues::U8(_) | CmpValues::U16(_) | CmpValues::U32(_) | CmpValues::U64(_)
        )
    }

    /// Converts the value to a u64 tuple
    #[must_use]
    pub fn to_u64_tuple(&self) -> Option<(u64, u64, bool, usize)> {
        match self {
            CmpValues::U8(t) => Some((u64::from(t.0), u64::from(t.1), t.2, t.3)),
            CmpValues::U16(t) => Some((u64::from(t.0), u64::from(t.1), t.2, t.3)),
            CmpValues::U32(t) => Some((u64::from(t.0), u64::from(t.1), t.2, t.3)),
            CmpValues::U64(t) => Some(*t),
            CmpValues::Bytes(_) => None,
        }
    }

    /// Extract the ID from this comparison value
    pub fn get_id(&self) -> u32 {
        match self {
            CmpValues::U8((_, _, _, id)) => *id as u32,
            CmpValues::U16((_, _, _, id)) => *id as u32,
            CmpValues::U32((_, _, _, id)) => *id as u32,
            CmpValues::U64((_, _, _, id)) => *id as u32,
            CmpValues::Bytes((_, _, id)) => *id as u32,
        }
    }
}

/// A state metadata holding a list of values logged from comparisons
#[derive(Debug, Default, Serialize, Deserialize)]
#[cfg_attr(
    any(not(feature = "serdeany_autoreg"), miri),
    expect(clippy::unsafe_derive_deserialize)
)] // for SerdeAny
pub struct CmpValuesMetadata {
    /// A `list` of values.
    #[serde(skip)]
    pub list: Vec<CmpValues>,
}

libafl_bolts::impl_serdeany!(CmpValuesMetadata);

impl Deref for CmpValuesMetadata {
    type Target = [CmpValues];
    fn deref(&self) -> &[CmpValues] {
        &self.list
    }
}

impl DerefMut for CmpValuesMetadata {
    fn deref_mut(&mut self) -> &mut [CmpValues] {
        &mut self.list
    }
}

impl CmpValuesMetadata {
    /// Creates a new [`struct@CmpValuesMetadata`]
    #[must_use]
    pub fn new() -> Self {
        Self { list: vec![] }
    }

    /// Add comparisons to a metadata from a `CmpObserver`. `cmp_map` is mutable in case
    /// it is needed for a custom map, but this is not utilized for `CmpObserver` or
    /// `AflppCmpLogObserver`.
    pub fn add_from<CM>(&mut self, usable_count: usize, cmp_map: &mut CM)
    where
        CM: CmpMap,
    {
        self.list.clear();
        let count = usable_count;
        for i in 0..count {
            let execs = cmp_map.usable_executions_for(i);
            if execs > 0 {
                // Recongize loops and discard if needed
                if execs > 4 {
                    let mut increasing_v0 = 0;
                    let mut increasing_v1 = 0;
                    let mut decreasing_v0 = 0;
                    let mut decreasing_v1 = 0;

                    let mut last: Option<CmpValues> = None;
                    for j in 0..execs {
                        if let Some(val) = cmp_map.values_of(i, j) {
                            if let Some(l) = last.and_then(|x| x.to_u64_tuple()) {
                                if let Some(v) = val.to_u64_tuple() {
                                    if l.0.wrapping_add(1) == v.0 {
                                        increasing_v0 += 1;
                                    }
                                    if l.1.wrapping_add(1) == v.1 {
                                        increasing_v1 += 1;
                                    }
                                    if l.0.wrapping_sub(1) == v.0 {
                                        decreasing_v0 += 1;
                                    }
                                    if l.1.wrapping_sub(1) == v.1 {
                                        decreasing_v1 += 1;
                                    }
                                }
                            }
                            last = Some(val);
                        }
                    }
                    // We check for execs-2 because the logged execs may wrap and have something like
                    // 8 9 10 3 4 5 6 7
                    if increasing_v0 >= execs - 2
                        || increasing_v1 >= execs - 2
                        || decreasing_v0 >= execs - 2
                        || decreasing_v1 >= execs - 2
                    {
                        continue;
                    }
                }
                for j in 0..execs {
                    if let Some(val) = cmp_map.values_of(i, j) {
                        self.list.push(val);
                    }
                }
            }
        }
    }

    /// Extract all unique comparison IDs from the collected values
    pub fn get_cmp_ids(&self) -> Vec<u32> {
        let mut ids = Vec::new();
        for cmp_value in &self.list {
            let id = match cmp_value {
                CmpValues::U8((_, _, _, id)) => *id as u32,
                CmpValues::U16((_, _, _, id)) => *id as u32,
                CmpValues::U32((_, _, _, id)) => *id as u32,
                CmpValues::U64((_, _, _, id)) => *id as u32,
                CmpValues::Bytes((_, _, id)) => *id as u32,
            };
            if !ids.contains(&id) {
                ids.push(id);
            }
        }
        ids
    }

    /// Get debug information for all comparisons using a debug resolver
    pub fn resolve_debug_info(
        &self,
        resolver: &CmplogDebugResolver,
    ) -> Vec<(u32, Option<CmplogDebugLocation>)> {
        self.get_cmp_ids()
            .into_iter()
            .map(|id| (id, resolver.resolve_full(id)))
            .collect()
    }

    /// Print debug information for all comparisons
    pub fn print_debug_info(&self, resolver: &CmplogDebugResolver) {
        let debug_info = self.resolve_debug_info(resolver);

        println!("Cmplog Debug Information:");
        println!("========================");

        for (id, location) in debug_info {
            match location {
                Some(loc) => {
                    println!("ID {}: {}", id, loc.format());
                }
                None => {
                    println!("ID {}: <no debug info available>", id);
                }
            }
        }

        if self.list.is_empty() {
            println!("No comparison values recorded.");
        } else {
            println!("\nTotal comparisons: {}", self.list.len());
            println!("Unique comparison locations: {}", self.get_cmp_ids().len());
        }
    }

    /// Get comparison values grouped by their debug location
    pub fn group_by_location(
        &self,
        resolver: &CmplogDebugResolver,
    ) -> HashMap<u32, (Option<CmplogDebugLocation>, Vec<&CmpValues>)> {
        let mut groups: HashMap<u32, (Option<CmplogDebugLocation>, Vec<&CmpValues>)> =
            HashMap::new();

        for cmp_value in &self.list {
            let id = match cmp_value {
                CmpValues::U8((_, _, _, id)) => *id as u32,
                CmpValues::U16((_, _, _, id)) => *id as u32,
                CmpValues::U32((_, _, _, id)) => *id as u32,
                CmpValues::U64((_, _, _, id)) => *id as u32,
                CmpValues::Bytes((_, _, id)) => *id as u32,
            };

            let entry = groups
                .entry(id)
                .or_insert_with(|| (resolver.resolve_full(id), Vec::new()));
            entry.1.push(cmp_value);
        }

        groups
    }

    /// Helper function to enable debug information collection for the current fuzzing session
    /// This should be called after the fuzzer has been initialized to load embedded debug info
    pub fn enable_debug_analysis(&mut self) -> Result<CmplogDebugResolver, Error> {
        CmplogDebugResolver::load_from_executable()
    }
}

/// A [`CmpMap`] traces comparisons during the current execution
pub trait CmpMap: Debug {
    /// Get the number of cmps
    fn len(&self) -> usize;

    /// Get if it is empty
    #[must_use]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the number of executions for a cmp
    fn executions_for(&self, idx: usize) -> usize;

    /// Get the number of logged executions for a cmp
    fn usable_executions_for(&self, idx: usize) -> usize;

    /// Get the logged values for a cmp
    fn values_of(&self, idx: usize, execution: usize) -> Option<CmpValues>;

    /// Reset the state
    fn reset(&mut self) -> Result<(), Error>;
}

/// A [`CmpObserver`] observes the traced comparisons during the current execution using a [`CmpMap`]
pub trait CmpObserver {
    /// The underlying map
    type Map;
    /// Get the number of usable cmps (all by default)
    fn usable_count(&self) -> usize;

    /// Get the `CmpMap`
    fn cmp_map(&self) -> &Self::Map;

    /// Get the mut `CmpMap`
    fn cmp_map_mut(&mut self) -> &mut Self::Map;
}

/// A standard [`CmpObserver`] observer
#[derive(Serialize, Deserialize, Debug)]
#[serde(bound = "CM: serde::de::DeserializeOwned + Serialize")]
pub struct StdCmpObserver<'a, CM> {
    cmp_map: OwnedRefMut<'a, CM>,
    size: Option<OwnedRefMut<'a, usize>>,
    name: Cow<'static, str>,
    add_meta: bool,
}

impl<CM> CmpObserver for StdCmpObserver<'_, CM>
where
    CM: HasLen,
{
    type Map = CM;

    /// Get the number of usable cmps (all by default)
    fn usable_count(&self) -> usize {
        match &self.size {
            None => self.cmp_map.as_ref().len(),
            Some(o) => *o.as_ref(),
        }
    }

    fn cmp_map(&self) -> &Self::Map {
        self.cmp_map.as_ref()
    }

    fn cmp_map_mut(&mut self) -> &mut Self::Map {
        self.cmp_map.as_mut()
    }
}

impl<CM, I, S> Observer<I, S> for StdCmpObserver<'_, CM>
where
    CM: Serialize + CmpMap + HasLen,
    S: HasMetadata,
{
    fn pre_exec(&mut self, _state: &mut S, _input: &I) -> Result<(), Error> {
        self.cmp_map.as_mut().reset()?;
        Ok(())
    }

    fn post_exec(&mut self, state: &mut S, _input: &I, _exit_kind: &ExitKind) -> Result<(), Error> {
        if self.add_meta {
            let meta = state.metadata_or_insert_with(CmpValuesMetadata::new);

            meta.add_from(self.usable_count(), self.cmp_map_mut());
        }
        Ok(())
    }
}

impl<CM> Named for StdCmpObserver<'_, CM> {
    fn name(&self) -> &Cow<'static, str> {
        &self.name
    }
}

impl<'a, CM> StdCmpObserver<'a, CM>
where
    CM: CmpMap,
{
    /// Creates a new [`StdCmpObserver`] with the given name and map.
    #[must_use]
    pub fn new(name: &'static str, map: OwnedRefMut<'a, CM>, add_meta: bool) -> Self {
        Self {
            name: Cow::from(name),
            size: None,
            cmp_map: map,
            add_meta,
        }
    }

    /// Creates a new [`StdCmpObserver`] with the given name, map and reference to variable size.
    #[must_use]
    pub fn with_size(
        name: &'static str,
        cmp_map: OwnedRefMut<'a, CM>,
        add_meta: bool,
        size: OwnedRefMut<'a, usize>,
    ) -> Self {
        Self {
            name: Cow::from(name),
            size: Some(size),
            cmp_map,
            add_meta,
        }
    }
}

/* From AFL++ cmplog.h

#define CMP_MAP_W 65536
#define CMP_MAP_H 32
#define CMP_MAP_RTN_H (CMP_MAP_H / 4)

struct cmp_header {

  unsigned hits : 24;
  unsigned id : 24;
  unsigned shape : 5;
  unsigned type : 2;
  unsigned attribute : 4;
  unsigned overflow : 1;
  unsigned reserved : 4;

} __attribute__((packed));

struct cmp_operands {

  u64 v0;
  u64 v1;
  u64 v0_128;
  u64 v1_128;

} __attribute__((packed));

struct cmpfn_operands {

  u8 v0[31];
  u8 v0_len;
  u8 v1[31];
  u8 v1_len;

} __attribute__((packed));

typedef struct cmp_operands cmp_map_list[CMP_MAP_H];

struct cmp_map {

  struct cmp_header   headers[CMP_MAP_W];
  struct cmp_operands log[CMP_MAP_W][CMP_MAP_H];

};
*/

/// A state metadata holding a list of values logged from comparisons. AFL++ RQ version.
#[derive(Debug, Default, Serialize, Deserialize)]
#[cfg_attr(
    any(not(feature = "serdeany_autoreg"), miri),
    expect(clippy::unsafe_derive_deserialize)
)] // for SerdeAny
pub struct AflppCmpValuesMetadata {
    /// The first map of `AflppCmpLogVals` retrieved by running the un-mutated input
    #[serde(skip)]
    pub orig_cmpvals: HashMap<usize, Vec<CmpValues>>,
    /// The second map of `AflppCmpLogVals` retrieved by runnning the mutated input
    #[serde(skip)]
    pub new_cmpvals: HashMap<usize, Vec<CmpValues>>,
    /// The list of logged idx and headers retrieved by runnning the mutated input
    #[serde(skip)]
    pub headers: Vec<(usize, AflppCmpLogHeader)>,
}

libafl_bolts::impl_serdeany!(AflppCmpValuesMetadata);

impl AflppCmpValuesMetadata {
    /// Constructor for `AflppCmpValuesMetadata`
    #[must_use]
    pub fn new() -> Self {
        Self {
            orig_cmpvals: HashMap::new(),
            new_cmpvals: HashMap::new(),
            headers: Vec::new(),
        }
    }

    /// Getter for `orig_cmpvals`
    #[must_use]
    pub fn orig_cmpvals(&self) -> &HashMap<usize, Vec<CmpValues>> {
        &self.orig_cmpvals
    }

    /// Getter for `new_cmpvals`
    #[must_use]
    pub fn new_cmpvals(&self) -> &HashMap<usize, Vec<CmpValues>> {
        &self.new_cmpvals
    }

    /// Getter for `headers`
    #[must_use]
    pub fn headers(&self) -> &Vec<(usize, AflppCmpLogHeader)> {
        &self.headers
    }
}

/// Comparison header, used to describe a set of comparison values efficiently.
///
/// # Bitfields
///
/// - hits:      The number of hits of a particular comparison
/// - id:        Unused by ``LibAFL``, a unique ID for a particular comparison
/// - shape:     Whether a comparison is u8/u8, u16/u16, etc.
/// - type_:     Whether the comparison value represents an instruction (like a `cmp`) or function
///              call arguments
/// - attribute: OR-ed bitflags describing whether the comparison is <, >, =, <=, >=, or transform
/// - overflow:  Whether the comparison overflows
/// - reserved:  Reserved for future use
#[bitfield(u16)]
#[derive(Debug)]
pub struct AflppCmpLogHeader {
    /// The number of hits of a particular comparison
    ///
    /// 6 bits up to 63 entries, we have CMP_MAP_H = 32 (so using half of it)
    #[bits(0..=5, r)]
    hits: u6,
    /// Whether a comparison is u8/u8, u16/u16, etc.
    ///
    /// 31 + 1 bytes max
    #[bits(6..=10, r)]
    shape: u5,
    /// Whether the comparison value represents an instruction (like a `cmp`) or function call
    /// arguments
    ///
    /// 2: cmp, rtn
    #[bit(11, r)]
    type_: u1,
    /// OR-ed bitflags describing whether the comparison is <, >, =, <=, >=, or transform
    ///
    /// 16 types for arithmetic comparison types
    #[bits(12..=15, r)]
    attribute: u4,
}
