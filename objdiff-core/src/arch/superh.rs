use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};
use core::cmp::Ordering;

use anyhow::{Result, bail};
use object::elf;

use crate::{
    arch::Arch,
    diff::{DiffObjConfig, display::InstructionPart},
    obj::{
        InstructionRef, Relocation, RelocationFlags, ResolvedInstructionRef, ResolvedRelocation,
        ScannedInstruction,
    },
};

#[derive(Debug)]
pub struct ArchSuperH {}

impl ArchSuperH {
    pub fn new(_file: &object::File) -> Result<Self> { Ok(Self {}) }
}

use std::collections::HashMap;


struct DataLabel {
    size: u32,
    label: String,
    source: u32,
}

fn match_ni_f(
    _v_addr: u32,
    op: u32,
    _mode: bool,
    string: &mut String,
    _data_labels: &HashMap<u32, DataLabel>,
    _branch_labels: &HashMap<u32, String>,
) {
    match op & 0xf000 {
        0x7000 => string.push_str(&format!("add #0x{:02X}, r{}", op & 0xff, (op >> 8) & 0xf)),
        0xe000 => string.push_str(&format!("mov #{}, r{}", op & 0xff, (op >> 8) & 0xf)),
        // unknown
        _ => string.push_str(&format!(".word 0x{:04X} /* unknown instruction */", op)),
    }
}

fn match_i_f(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xff00 {
        0xcd00 => string.push_str(&format!("and.b #0x{:02X}, @(r0, gbr)", op & 0xff)),
        0xcf00 => string.push_str(&format!("or.b #0x{:02X}, @(r0, gbr)", op & 0xff)),
        0xcc00 => string.push_str(&format!("tst.b #0x{:02X}, @(r0, gbr)", op & 0xff)),
        0xce00 => string.push_str(&format!("xor.b #0x{:02X}, @(r0, gbr)", op & 0xff)),
        0xc900 => string.push_str(&format!("and #0x{:02X}, r0", op & 0xff)),
        0x8800 => string.push_str(&format!("cmp/eq #0x{:02X}, r0", op & 0xff)),
        0xcb00 => string.push_str(&format!("or #0x{:02X}, r0", op & 0xff)),
        0xc800 => string.push_str(&format!("tst #0x{:02X}, r0", op & 0xff)),
        0xca00 => string.push_str(&format!("xor #0x{:02X}, r0", op & 0xff)),
        0xc300 => string.push_str(&format!("trapa #0x{:X}", op & 0xff)),
        _ => match_ni_f(v_addr, op, mode, string, data_labels, branch_labels),
    }
}

fn match_nd8_f(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xf000 {
        0x9000 => {
            // "mov.w @(0x%03X, pc), r%d"
            let thing = (op & 0xff) * 2 + 4 + v_addr;

            if data_labels.contains_key(&thing) {
                if let Some(value) = data_labels.get(&thing) {
                    // Use the label
                    string.push_str(&format!(
                        "mov.w @({}, pc), r{}",
                        value.label,
                        (op >> 8) & 0xf
                    ));
                }
            } else {
                // use an address
                string.push_str(&format!(
                    "mov.w @(0x{:03X}, pc), r{}",
                    (op & 0xff) * 2 + 4,
                    (op >> 8) & 0xf
                ));
            }
        }
        0xd000 => {
            // "mov.l @(0x%03X, pc), r%d"
            let v_addr_aligned = (v_addr & 0xfffffffc) == 0;
            // this post explains part of issue. https://dcemulation.org/phpBB/viewtopic.php?style=41&t=105661
            let mut target_a = (op & 0xff) * 4 + 4;
            let target_b = ((op & 0xff) * 4 + 4 + v_addr) & 0xfffffffc;
            let test = (op & 0xff) * 4 + 4 + v_addr;

            // gas alignment issue.
            if (test & 3) == 2 {
                // subtract 2 from target_a
                target_a -= 2;

                let thing = test - 2;

                if data_labels.contains_key(&thing) {
                    if let Some(value) = data_labels.get(&thing) {
                        // Use the label
                        string.push_str(&format!(
                            "mov.l @({}, pc), r{}",
                            value.label,
                            (op >> 8) & 0xf
                        ));
                    }
                } else {
                    // use an address
                    string.push_str(&format!(
                        "mov.l @(0x{:03X}, pc), r{}",
                        target_a,
                        (op >> 8) & 0xf
                    ));
                }
            } else {
                if data_labels.contains_key(&test) {
                    if let Some(value) = data_labels.get(&test) {
                        // Use the label
                        string.push_str(&format!(
                            "mov.l @({}, pc), r{}",
                            value.label,
                            (op >> 8) & 0xf
                        ));
                    }
                } else {
                    // use an address
                    string.push_str(&format!(
                        "mov.l @(0x{:03X}, pc), r{}",
                        target_a,
                        (op >> 8) & 0xf
                    ));
                }
            }
        }
        _ => match_i_f(v_addr, op, mode, string, data_labels, branch_labels),
    }
}

fn match_d12_f(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xf000 {
        0xa000 => {
            if (op & 0x800) == 0x800 {
                let addr = ((op & 0xfff) + 0xfffff000)
                    .wrapping_mul(2)
                    .wrapping_add(v_addr)
                    .wrapping_add(4);
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bra {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bra 0x{:08X}", addr));
                }
            } else {
                let addr = (op & 0xfff) * 2 + v_addr + 4;
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bra {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bra 0x{:08X}", addr));
                }
            }
        }
        0xb000 => {
            if (op & 0x800) == 0x800 {
                let addr = ((op & 0xfff) + 0xfffff000).wrapping_mul(2).wrapping_add(v_addr) + 4;
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bsr {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bsr 0x{:08X}", addr));
                }
            } else {
                let addr = (op & 0xfff) * 2 + v_addr + 4;
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bsr {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bsr 0x{:08X}", addr));
                }
            }
        }
        _ => match_nd8_f(v_addr, op, mode, string, data_labels, branch_labels),
    }
}

fn match_d_f(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xff00 {
        0xc000 => string.push_str(&format!("mov.b r0, @(0x{:03X}, gbr)", (op & 0xff) * 1)),
        0xc100 => string.push_str(&format!("mov.w r0, @(0x{:03X}, gbr)", (op & 0xff) * 2)),
        0xc200 => string.push_str(&format!("mov.l r0, @(0x{:03X}, gbr)", (op & 0xff) * 4)),
        0xc400 => string.push_str(&format!("mov.b @(0x{:03X}, gbr), r0", (op & 0xff) * 1)),
        0xc500 => string.push_str(&format!("mov.w @(0x{:03X}, gbr), r0", (op & 0xff) * 2)),
        0xc600 => string.push_str(&format!("mov.l @(0x{:03X}, gbr), r0", (op & 0xff) * 4)),

        // mova
        0xc600 => {}
        0x8b00 => {
            if (op & 0x80) == 0x80 {
                let addr = (((op & 0xff) + 0xffffff00).wrapping_mul(2))
                    .wrapping_add(v_addr)
                    .wrapping_add(4);

                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bf {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bf 0x{:08X}", addr));
                }
            } else {
                let addr = ((op & 0xff) * 2) + v_addr + 4;

                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bf {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bf 0x{:08X}", addr));
                }
            }
        }
        0x8f00 => {
            if (op & 0x80) == 0x80 {
                let addr = (((op & 0xff) + 0xffffff00).wrapping_mul(2))
                    .wrapping_add(v_addr)
                    .wrapping_add(4);
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bf.s {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bf.s 0x{:08X}", addr));
                }
            } else {
                let addr = ((op & 0xff) * 2) + v_addr + 4;
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bf.s {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bf.s 0x{:08X}", addr));
                }
            }
        }
        0x8900 => {
            if (op & 0x80) == 0x80 {
                let addr = (((op & 0xff) + 0xffffff00).wrapping_mul(2))
                    .wrapping_add(v_addr)
                    .wrapping_add(4);

                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bt {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bt 0x{:08X}", addr));
                }
            } else {
                let addr = ((op & 0xff) * 2) + v_addr + 4;
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bt {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bt 0x{:08X}", addr));
                }
            }
        }
        0x8d00 => {
            if (op & 0x80) == 0x80 {
                let addr = (((op & 0xff) + 0xffffff00).wrapping_mul(2))
                    .wrapping_add(v_addr)
                    .wrapping_add(4);
                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bt.s {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bt.s 0x{:08X}", addr));
                }
            } else {
                let addr = ((op & 0xff) * 2) + v_addr + 4;

                if branch_labels.contains_key(&addr) {
                    if let Some(value) = branch_labels.get(&addr) {
                        // Use the label
                        string.push_str(&format!("bt.s {}", value));
                    }
                } else {
                    // use an address
                    string.push_str(&format!("bt.s 0x{:08X}", addr));
                }
            }
        }
        _ => match_d12_f(v_addr, op, mode, string, data_labels, branch_labels),
    }
}

fn match_nmd_f(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xf000 {
        0x1000 => string.push_str(&format!(
            "mov.l r{}, @(0x{:03X}, r{})",
            (op >> 4) & 0xf,
            (op & 0xf) * 4,
            (op >> 8) & 0xf
        )),
        0x5000 => string.push_str(&format!(
            "mov.l @(0x{:03X}, r{}), r{}",
            (op & 0xf) * 4,
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        _ => match_d_f(v_addr, op, mode, string, data_labels, branch_labels),
    }
}
fn match_ff00(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xff00 {
        0x8400 => {
            if (op & 0x100) == 0x100 {
                string.push_str(&format!(
                    "mov.b @(0x{:03X}, r{}), r0",
                    (op & 0xf) * 2,
                    (op >> 4) & 0xf
                ))
            } else {
                string.push_str(&format!(
                    "mov.b @(0x{:03X}, r{}), r0",
                    op & 0xf,
                    (op >> 4) & 0xf
                ))
            }
        }
        0x8500 => {
            if (op & 0x100) == 0x100 {
                string.push_str(&format!(
                    "mov.w @(0x{:03X}, r{}), r0",
                    (op & 0xf) * 2,
                    (op >> 4) & 0xf
                ))
            } else {
                string.push_str(&format!(
                    "mov.w @(0x{:03X}, r{}), r0",
                    op & 0xf,
                    (op >> 4) & 0xf
                ))
            }
        }
        0x8000 => {
            if (op & 0x100) == 0x100 {
                string.push_str(&format!(
                    "mov.b r0, @(0x{:03X}, r{})",
                    (op & 0xf) * 2,
                    (op >> 4) & 0xf
                ))
            } else {
                string.push_str(&format!(
                    "mov.b r0, @(0x{:03X}, r{})",
                    op & 0xf,
                    (op >> 4) & 0xf
                ))
            }
        }
        0x8100 => {
            if (op & 0x100) == 0x100 {
                string.push_str(&format!(
                    "mov.w r0, @(0x{:03X}, r{})",
                    (op & 0xf) * 2,
                    (op >> 4) & 0xf
                ))
            } else {
                string.push_str(&format!(
                    "mov.w r0, @(0x{:03X}, r{})",
                    op & 0xf,
                    (op >> 4) & 0xf
                ))
            }
        }
        _ => match_nmd_f(v_addr, op, mode, string, data_labels, branch_labels),
    }
}

fn match_f00f(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xf00f {
        0x300c => string.push_str(&format!("add r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x300e => string.push_str(&format!("addc r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x300f => string.push_str(&format!("addv r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x2009 => string.push_str(&format!("and r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x3000 => string.push_str(&format!(
            "cmp/eq r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x3002 => string.push_str(&format!(
            "cmp/hs r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x3003 => string.push_str(&format!(
            "cmp/ge r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x3006 => string.push_str(&format!(
            "cmp/hi r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x3007 => string.push_str(&format!(
            "cmp/gt r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x200c => string.push_str(&format!(
            "cmp/str r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x3004 => string.push_str(&format!("div1 r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x2007 => string.push_str(&format!("div0s r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x300d => string.push_str(&format!(
            "dmuls.l r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x3005 => string.push_str(&format!(
            "dmulu.l r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x600e => string.push_str(&format!(
            "exts.b r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x600f => string.push_str(&format!(
            "exts.w r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x600c => string.push_str(&format!(
            "extu.b r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x600d => string.push_str(&format!(
            "extu.w r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x6003 => string.push_str(&format!("mov r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x0007 => string.push_str(&format!("mul.l r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x200f => string.push_str(&format!("muls r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x200e => string.push_str(&format!("mulu r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x600b => string.push_str(&format!("neg r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x600a => string.push_str(&format!("negc r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x6007 => string.push_str(&format!("not r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x200b => string.push_str(&format!("or r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x3008 => string.push_str(&format!("sub r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x300a => string.push_str(&format!("subc r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x300b => string.push_str(&format!("subv r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x6008 => string.push_str(&format!(
            "swap.b r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x6009 => string.push_str(&format!(
            "swap.w r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x2008 => string.push_str(&format!("tst r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x200a => string.push_str(&format!("xor r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x200d => string.push_str(&format!("xtrct r{}, r{}", (op >> 4) & 0xf, (op >> 8) & 0xf)),
        0x2000 => string.push_str(&format!(
            "mov.b r{}, @r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x2001 => string.push_str(&format!(
            "mov.w r{}, @r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x2002 => string.push_str(&format!(
            "mov.l r{}, @r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x6000 => string.push_str(&format!(
            "mov.b @r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x6001 => string.push_str(&format!(
            "mov.w @r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x6002 => string.push_str(&format!(
            "mov.l @r{}, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x000f => string.push_str(&format!(
            "mac.l @r{}+, @r{}+",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf,
        )),
        0x400f => string.push_str(&format!(
            "mac.w @r{}+, @r{}+",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf,
        )),
        0x6004 => string.push_str(&format!(
            "mov.b @r{}+, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x6005 => string.push_str(&format!(
            "mov.w @r{}+, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x6006 => string.push_str(&format!(
            "mov.l @r{}+, r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x2004 => string.push_str(&format!(
            "mov.b r{}, @-r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x2005 => string.push_str(&format!(
            "mov.w r{}, @-r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x2006 => string.push_str(&format!(
            "mov.l r{}, @-r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x0004 => string.push_str(&format!(
            "mov.b r{}, @(r0, r{})",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x0005 => string.push_str(&format!(
            "mov.w r{}, @(r0, r{})",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x0006 => string.push_str(&format!(
            "mov.l r{}, @(r0, r{})",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x000c => string.push_str(&format!(
            "mov.b @(r0, r{}), r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x000d => string.push_str(&format!(
            "mov.w @(r0, r{}), r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        0x000e => string.push_str(&format!(
            "mov.l @(r0, r{}), r{}",
            (op >> 4) & 0xf,
            (op >> 8) & 0xf
        )),
        _ => match_ff00(v_addr, op, mode, string, data_labels, branch_labels),
    }
}
fn match_f0ff(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xf0ff {
        0x4015 => string.push_str(&format!("cmp/pl r{}", (op >> 8) & 0xf)),
        0x4011 => string.push_str(&format!("cmp/pz r{}", (op >> 8) & 0xf)),
        0x4010 => string.push_str(&format!("dt r{}", (op >> 8) & 0xf)),
        0x0029 => string.push_str(&format!("movt r{}", (op >> 8) & 0xf)),
        0x4004 => string.push_str(&format!("rotl r{}", (op >> 8) & 0xf)),
        0x4005 => string.push_str(&format!("rotr r{}", (op >> 8) & 0xf)),
        0x4024 => string.push_str(&format!("rotcl r{}", (op >> 8) & 0xf)),
        0x4025 => string.push_str(&format!("rotcr r{}", (op >> 8) & 0xf)),
        0x4020 => string.push_str(&format!("shal r{}", (op >> 8) & 0xf)),
        0x4021 => string.push_str(&format!("shar r{}", (op >> 8) & 0xf)),
        0x4000 => string.push_str(&format!("shll r{}", (op >> 8) & 0xf)),
        0x4001 => string.push_str(&format!("shlr r{}", (op >> 8) & 0xf)),
        0x4008 => string.push_str(&format!("shll2 r{}", (op >> 8) & 0xf)),
        0x4009 => string.push_str(&format!("shlr2 r{}", (op >> 8) & 0xf)),
        0x4018 => string.push_str(&format!("shll8 r{}", (op >> 8) & 0xf)),
        0x4019 => string.push_str(&format!("shlr8 r{}", (op >> 8) & 0xf)),
        0x4028 => string.push_str(&format!("shll16 r{}", (op >> 8) & 0xf)),
        0x4029 => string.push_str(&format!("shlr16 r{}", (op >> 8) & 0xf)),
        0x0002 => string.push_str(&format!("stc sr, r{}", (op >> 8) & 0xf)),
        0x0012 => string.push_str(&format!("stc gbr, r{}", (op >> 8) & 0xf)),
        0x0022 => string.push_str(&format!("stc vbr, r{}", (op >> 8) & 0xf)),
        0x000a => string.push_str(&format!("sts mach, r{}", (op >> 8) & 0xf)),
        0x001a => string.push_str(&format!("sts macl, r{}", (op >> 8) & 0xf)),
        0x402a => string.push_str(&format!("sts pr, r{}", (op >> 8) & 0xf)),
        0x401b => string.push_str(&format!("tas.b r{}", (op >> 8) & 0xf)),
        0x4003 => string.push_str(&format!("stc.l sr, @-r{}", (op >> 8) & 0xf)),
        0x4013 => string.push_str(&format!("stc.l gbr, @-r{}", (op >> 8) & 0xf)),
        0x4023 => string.push_str(&format!("stc.l vbr, @-r{}", (op >> 8) & 0xf)),
        0x4002 => string.push_str(&format!("sts.l mach, @-r{}", (op >> 8) & 0xf)),
        0x4012 => string.push_str(&format!("sts.l macl, @-r{}", (op >> 8) & 0xf)),
        0x4022 => string.push_str(&format!("sts.l pr, @-r{}", (op >> 8) & 0xf)),
        0x400e => string.push_str(&format!("ldc r{}, sr", (op >> 8) & 0xf)),
        0x401e => string.push_str(&format!("ldc r{}, gbr", (op >> 8) & 0xf)),
        0x402e => string.push_str(&format!("ldc r{}, vbr", (op >> 8) & 0xf)),
        0x400a => string.push_str(&format!("lds r{}, mach", (op >> 8) & 0xf)),
        0x401a => string.push_str(&format!("lds r{}, macl", (op >> 8) & 0xf)),
        0x402a => string.push_str(&format!("lds r{}, pr", (op >> 8) & 0xf)),
        0x402b => string.push_str(&format!("jmp @r{}", (op >> 8) & 0xf)),
        0x400b => string.push_str(&format!("jsr @r{}", (op >> 8) & 0xf)),
        0x4007 => string.push_str(&format!("ldc.l @r{}+, sr", (op >> 8) & 0xf)),
        0x4017 => string.push_str(&format!("ldc.l @r{}+, gbr", (op >> 8) & 0xf)),
        0x4027 => string.push_str(&format!("ldc.l @r{}+, vbr", (op >> 8) & 0xf)),
        0x4006 => string.push_str(&format!("lds.l @r{}+, mach", (op >> 8) & 0xf)),
        0x4016 => string.push_str(&format!("lds.l @r{}+, macl", (op >> 8) & 0xf)),
        0x4026 => string.push_str(&format!("lds.l @r{}+, pr", (op >> 8) & 0xf)),
        0x0023 => string.push_str(&format!("braf r{}", (op >> 8) & 0xf)),
        0x0003 => string.push_str(&format!("bsrf r{}", (op >> 8) & 0xf)),
        _ => {
            match_f00f(v_addr, op, mode, string, data_labels, branch_labels);
        }
    }
}

fn sh2_disasm(
    v_addr: u32,
    op: u32,
    mode: bool,
    string: &mut String,
    data_labels: &HashMap<u32, DataLabel>,
    branch_labels: &HashMap<u32, String>,
) {
    match op & 0xffff {
        0x0008 => string.push_str("clrt"),
        0x0028 => string.push_str("clrmac"),
        0x0019 => string.push_str("div0u"),
        0x0009 => string.push_str("nop"),
        0x002b => string.push_str("rte"),
        0x000b => string.push_str("rts"),
        0x0018 => string.push_str("sett"),
        0x001b => string.push_str("sleep"),
        _ => {
            match_f0ff(v_addr, op, mode, string, data_labels, branch_labels);
        }
    }
}
use std::backtrace::Backtrace;

impl Arch for ArchSuperH {
    fn scan_instructions(
        &self,
        address: u64,
        code: &[u8],
        _section_index: usize,
        _relocations: &[Relocation],
        _diff_config: &DiffObjConfig,
    ) -> Result<Vec<ScannedInstruction>> {
        let start_address = address;
        let mut ops = Vec::<ScannedInstruction>::with_capacity(code.len() / 4);
        let mut offset = address;
        let mut data_labels: HashMap<u32, DataLabel> = Default::default();
        let mut branch_labels: HashMap<u32, String> = Default::default();
        for chunk in code.chunks_exact(2) {
            // let code = self.endianness.read_u16_bytes(chunk.try_into()?);
            let opcode = u16::from_be_bytes(chunk.try_into().unwrap());
            let mut op_str: String = "".to_string();
            sh2_disasm(offset.try_into().unwrap(), opcode.into(), true, & mut op_str, &mut data_labels, &mut branch_labels);
            let ins_ref = InstructionRef { address: offset.try_into().unwrap(), size: 2, opcode };
            let branch_dest = Some(0);//branch_dest(ins_ref, &code[offset as usize..offset as usize + 4]);
            ops.push(ScannedInstruction { ins_ref, branch_dest });
            // println!("{:08X} {}", offset, op_str);
            offset += 2;
        }

        Ok(ops)
    }

    fn display_instruction(
        &self,
        resolved: ResolvedInstructionRef,
        _diff_config: &DiffObjConfig,
        cb: &mut dyn FnMut(InstructionPart) -> Result<()>,
    ) -> Result<()> {
        if let Some(reloc) = resolved.relocation
        {
            if let Some(addr) = reloc.symbol.virtual_address
            {
                println!("display_instruction {}", addr);
            }
        }
        let mut data_labels: HashMap<u32, DataLabel> = Default::default();
        let mut branch_labels: HashMap<u32, String> = Default::default();
        let mut op_str: String = "".to_string();
        let opcode = u16::from_be_bytes(resolved.code.try_into().unwrap());

        sh2_disasm(0, opcode.into(), true, & mut op_str, &mut data_labels, &mut branch_labels);

        cb(InstructionPart::opcode(op_str, opcode))?;

        Ok(())
    }

    fn implcit_addend(
        &self,
        _file: &object::File<'_>,
        _section: &object::Section,
        address: u64,
        _relocation: &object::Relocation,
        flags: RelocationFlags,
    ) -> Result<i64> {
        bail!("Unsupported ARM64 implicit relocation {:#x}:{:?}", address, flags)
    }

    fn demangle(&self, name: &str) -> Option<String> {
        cpp_demangle::Symbol::new(name)
            .ok()
            .and_then(|s| s.demangle(&cpp_demangle::DemangleOptions::default()).ok())
    }

    fn reloc_name(&self, flags: RelocationFlags) -> Option<&'static str> {
        match flags {
            RelocationFlags::Elf(r_type) => match r_type {
                elf::R_SH_NONE => Some("R_SH_NONE"),
                elf::R_SH_DIR32 => Some("R_SH_DIR32"),
                elf::R_SH_REL32 => Some("R_SH_REL32"),
                elf::R_SH_DIR8WPN => Some("R_SH_DIR8WPN"),
                elf::R_SH_IND12W => Some("R_SH_IND12W"),
                elf::R_SH_DIR8WPL => Some("R_SH_DIR8WPL"),
                elf::R_SH_DIR8WPZ => Some("R_SH_DIR8WPZ"),
                elf::R_SH_DIR8BP => Some("R_SH_DIR8BP"),
                elf::R_SH_DIR8W => Some("R_SH_DIR8W"),
                elf::R_SH_DIR8L => Some("R_SH_DIR8L"),
                elf::R_SH_SWITCH16 => Some("R_SH_SWITCH16"),
                elf::R_SH_SWITCH32 => Some("R_SH_SWITCH32"),
                elf::R_SH_USES => Some("R_SH_USES"),
                elf::R_SH_COUNT => Some("R_SH_COUNT"),
                elf::R_SH_ALIGN => Some("R_SH_ALIGN"),
                elf::R_SH_CODE => Some("R_SH_CODE"),
                elf::R_SH_DATA => Some("R_SH_DATA"),
                elf::R_SH_LABEL => Some("R_SH_LABEL"),
                elf::R_SH_SWITCH8 => Some("R_SH_SWITCH8"),
                elf::R_SH_GNU_VTINHERIT => Some("R_SH_GNU_VTINHERIT"),
                elf::R_SH_GNU_VTENTRY => Some("R_SH_GNU_VTENTRY"),
                elf::R_SH_TLS_GD_32 => Some("R_SH_TLS_GD_32"),
                elf::R_SH_TLS_LD_32 => Some("R_SH_TLS_LD_32"),
                elf::R_SH_TLS_LDO_32 => Some("R_SH_TLS_LDO_32"),
                elf::R_SH_TLS_IE_32 => Some("R_SH_TLS_IE_32"),
                elf::R_SH_TLS_LE_32 => Some("R_SH_TLS_LE_32"),
                elf::R_SH_TLS_DTPMOD32 => Some("R_SH_TLS_DTPMOD32"),
                elf::R_SH_TLS_DTPOFF32 => Some("R_SH_TLS_DTPOFF32"),
                elf::R_SH_TLS_TPOFF32 => Some("R_SH_TLS_TPOFF32"),
                elf::R_SH_GOT32 => Some("R_SH_GOT32"),
                elf::R_SH_PLT32 => Some("R_SH_PLT32"),
                elf::R_SH_COPY => Some("R_SH_COPY"),
                elf::R_SH_GLOB_DAT => Some("R_SH_GLOB_DAT"),
                elf::R_SH_JMP_SLOT => Some("R_SH_JMP_SLOT"),
                elf::R_SH_RELATIVE => Some("R_SH_RELATIVE"),
                elf::R_SH_GOTOFF => Some("R_SH_GOTOFF"),
                elf::R_SH_GOTPC => Some("R_SH_GOTPC"),
                _ => None,
            },
            _ => None,
        }
    }

    fn data_reloc_size(&self, flags: RelocationFlags) -> usize {
        match flags {
            RelocationFlags::Elf(r_type) => match r_type {
                // ???
                _ => 1,
            },
            _ => 1,
        }
    }
}
