pub mod elf;
pub mod mips;
pub mod ppc;

use std::{collections::BTreeMap, path::PathBuf};

use filetime::FileTime;
use flagset::{flags, FlagSet};

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ObjSectionKind {
    Code,
    Data,
    Bss,
}
flags! {
    pub enum ObjSymbolFlags: u8 {
        Global,
        Local,
        Weak,
        Common,
        Hidden,
    }
}
#[derive(Debug, Copy, Clone, Default)]
pub struct ObjSymbolFlagSet(pub(crate) FlagSet<ObjSymbolFlags>);
#[derive(Debug, Clone)]
pub struct ObjSection {
    pub name: String,
    pub kind: ObjSectionKind,
    pub address: u64,
    pub size: u64,
    pub data: Vec<u8>,
    pub index: usize,
    pub symbols: Vec<ObjSymbol>,
    pub relocations: Vec<ObjReloc>,

    // Diff
    pub data_diff: Vec<ObjDataDiff>,
    pub match_percent: f32,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ObjInsArg {
    PpcArg(ppc750cl::Argument),
    MipsArg(String),
    MipsArgWithBase(String),
    Reloc,
    RelocWithBase,
    BranchOffset(i32),
}

impl ObjInsArg {
    pub fn loose_eq(&self, other: &ObjInsArg) -> bool {
        match (self, other) {
            (ObjInsArg::PpcArg(a), ObjInsArg::PpcArg(b)) => {
                a == b
                    || match (a, b) {
                        // Consider Simm and Offset equivalent
                        (ppc750cl::Argument::Simm(simm), ppc750cl::Argument::Offset(off))
                        | (ppc750cl::Argument::Offset(off), ppc750cl::Argument::Simm(simm)) => {
                            simm.0 == off.0
                        }
                        // Consider Uimm and Offset equivalent
                        (ppc750cl::Argument::Uimm(uimm), ppc750cl::Argument::Offset(off))
                        | (ppc750cl::Argument::Offset(off), ppc750cl::Argument::Uimm(uimm)) => {
                            uimm.0 == off.0 as u16
                        }
                        // Consider Uimm and Simm equivalent
                        (ppc750cl::Argument::Uimm(uimm), ppc750cl::Argument::Simm(simm))
                        | (ppc750cl::Argument::Simm(simm), ppc750cl::Argument::Uimm(uimm)) => {
                            uimm.0 == simm.0 as u16
                        }
                        _ => false,
                    }
            }
            (ObjInsArg::MipsArg(a), ObjInsArg::MipsArg(b)) => a == b,
            (ObjInsArg::MipsArgWithBase(a), ObjInsArg::MipsArgWithBase(b)) => a == b,
            (ObjInsArg::Reloc, ObjInsArg::Reloc) => true,
            (ObjInsArg::RelocWithBase, ObjInsArg::RelocWithBase) => true,
            (ObjInsArg::BranchOffset(a), ObjInsArg::BranchOffset(b)) => a == b,
            _ => false,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ObjInsArgDiff {
    /// Incrementing index for coloring
    pub idx: usize,
}
#[derive(Debug, Clone)]
pub struct ObjInsBranchFrom {
    /// Source instruction indices
    pub ins_idx: Vec<usize>,
    /// Incrementing index for coloring
    pub branch_idx: usize,
}
#[derive(Debug, Clone)]
pub struct ObjInsBranchTo {
    /// Target instruction index
    pub ins_idx: usize,
    /// Incrementing index for coloring
    pub branch_idx: usize,
}
#[derive(Debug, Copy, Clone, Eq, PartialEq, Default)]
pub enum ObjInsDiffKind {
    #[default]
    None,
    OpMismatch,
    ArgMismatch,
    Replace,
    Delete,
    Insert,
}
#[derive(Debug, Clone)]
pub struct ObjIns {
    pub address: u32,
    pub code: u32,
    pub op: u8,
    pub mnemonic: String,
    pub args: Vec<ObjInsArg>,
    pub reloc: Option<ObjReloc>,
    pub branch_dest: Option<u32>,
    /// Line info
    pub line: Option<u64>,
    /// Original (unsimplified) instruction
    pub orig: Option<String>,
}
#[derive(Debug, Clone, Default)]
pub struct ObjInsDiff {
    pub ins: Option<ObjIns>,
    /// Diff kind
    pub kind: ObjInsDiffKind,
    /// Branches from instruction
    pub branch_from: Option<ObjInsBranchFrom>,
    /// Branches to instruction
    pub branch_to: Option<ObjInsBranchTo>,
    /// Arg diffs
    pub arg_diff: Vec<Option<ObjInsArgDiff>>,
}
#[derive(Debug, Copy, Clone, Eq, PartialEq, Default)]
pub enum ObjDataDiffKind {
    #[default]
    None,
    Replace,
    Delete,
    Insert,
}
#[derive(Debug, Clone, Default)]
pub struct ObjDataDiff {
    pub data: Vec<u8>,
    pub kind: ObjDataDiffKind,
    pub len: usize,
    pub symbol: String,
}
#[derive(Debug, Clone)]
pub struct ObjSymbol {
    pub name: String,
    pub demangled_name: Option<String>,
    pub address: u64,
    pub section_address: u64,
    pub size: u64,
    pub size_known: bool,
    pub flags: ObjSymbolFlagSet,
    pub addend: i64,

    // Diff
    pub diff_symbol: Option<String>,
    pub instructions: Vec<ObjInsDiff>,
    pub match_percent: Option<f32>,
}
#[derive(Debug, Copy, Clone)]
pub enum ObjArchitecture {
    PowerPc,
    Mips,
}
#[derive(Debug, Clone)]
pub struct ObjInfo {
    pub architecture: ObjArchitecture,
    pub path: PathBuf,
    pub timestamp: FileTime,
    pub sections: Vec<ObjSection>,
    pub common: Vec<ObjSymbol>,
    pub line_info: Option<BTreeMap<u64, u64>>,
}
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ObjRelocKind {
    Absolute,
    PpcAddr16Hi,
    PpcAddr16Ha,
    PpcAddr16Lo,
    // PpcAddr32,
    // PpcRel32,
    // PpcAddr24,
    PpcRel24,
    // PpcAddr14,
    PpcRel14,
    PpcEmbSda21,
    Mips26,
    MipsHi16,
    MipsLo16,
    MipsGot16,
    MipsCall16,
    MipsGpRel16,
    MipsGpRel32,
}
#[derive(Debug, Clone)]
pub struct ObjReloc {
    pub kind: ObjRelocKind,
    pub address: u64,
    pub target: ObjSymbol,
    pub target_section: Option<String>,
}
