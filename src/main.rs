use std::{
    collections::HashMap,
    env::{self, args},
    fs::read, slice::SplitInclusiveMut,
};

use capstone::{
    prelude::{ArchDetail, BuildsCapstone, BuildsCapstoneSyntax},
    Capstone, Insn, InsnDetail, InsnGroupId, Instructions, RegId,
};
use elf::{
    endian::AnyEndian,
    file::{self, Elf64_Ehdr},
    ElfBytes, ElfStream,
};
use iced_x86::*;
use queues::*;

extern crate capstone;
extern crate queues;

fn reg_names(cs: &Capstone, regs: &[RegId]) -> String {
    let names: Vec<String> = regs.iter().map(|&x| cs.reg_name(x).unwrap()).collect();
    names.join(", ")
}

/// Print instruction group names
fn group_names(cs: &Capstone, regs: &[InsnGroupId]) -> String {
    let names: Vec<String> = regs.iter().map(|&x| cs.group_name(x).unwrap()).collect();
    names.join(", ")
}

/*
    Since we know the entry point of the binary, we can locate the __libc_start_main hook.
    After that, we reverve 5-bytes backwards to locate the main function which is located in the
    %rdi register
*/
fn locate_main(code: &[u8], addr: u64, handler: &Capstone) -> u64 {
    let mut main_address_loader_rip: u64 = 0;
    let mut instr_size: usize = 0;
    let instructions = handler.disasm_all(code, addr).unwrap();

    for ins in instructions.as_ref() {
        let byte_representation = ins.bytes();
        //Hook for __libc_start_main
        if (byte_representation[0] == 0xff && byte_representation[1] == 0x15) {
            main_address_loader_rip = ins.address();
            instr_size = ins.len();
            break;
        }
    }

    //the address of the instruction that passes the address of "main" to __libc_start_main
    let instr_addr_main_to_rdi: u64 = main_address_loader_rip - (instr_size as u64);
    // the instruction that loads the main's address to the %rdi
    let dis = handler
        .disasm_count(
            &code[(instr_addr_main_to_rdi - 1 - addr as u64) as usize
                ..(instr_addr_main_to_rdi + 10 - addr as u64) as usize],
            instr_addr_main_to_rdi - 1,
            1,
        )
        .expect("Instructions not found");

    let main_addr = (dis.as_ref()[0].bytes()[4] as u64 * 16 * 16)
        + (dis.as_ref()[0].bytes()[3] as u64)
        + dis.as_ref()[0].address();
    return main_addr;
}

/**
 * Since we have found the main function, we need to find the main function defined by the user
 */
fn locate_user_main(code: &[u8], addr: u64, handler: &Capstone) -> u64 {
    let instructions: Instructions;
    let mut mut_code = code;
    let mut offset = 0;

    while handler
        .disasm_all(mut_code, addr + offset as u64)
        .unwrap()
        .len()
        < 2
    {
        mut_code = &code[offset..code.len()];
        offset += 1;
    }

    instructions = handler.disasm_all(mut_code, addr + offset as u64).unwrap();

    for ins in instructions.as_ref() {
        let byte_array = ins.bytes();
        if (byte_array[0] == 0x48 && byte_array[1] == 0x8d && byte_array[2] == 0x3d) {
            return (ins.address() as i32
                + ((byte_array[3] as u64
                    + byte_array[4] as u64 * 16 * 16
                    + byte_array[5] as u64 * 16 * 16 * 16 * 16
                    + byte_array[6] as u64 * 16 * 16 * 16 * 16 * 16 * 16)
                    as i32))
                .try_into()
                .unwrap();
        }
    }
    0xffffffff
}

fn flags(rf: u32) -> String {
    fn append(sb: &mut String, s: &str) {
        if !sb.is_empty() {
            sb.push_str(", ");
        }
        sb.push_str(s);
    }

    let mut sb = String::new();
    if (rf & RflagsBits::OF) != 0 {
        append(&mut sb, "OF");
    }
    if (rf & RflagsBits::SF) != 0 {
        append(&mut sb, "SF");
    }
    if (rf & RflagsBits::ZF) != 0 {
        append(&mut sb, "ZF");
    }
    if (rf & RflagsBits::AF) != 0 {
        append(&mut sb, "AF");
    }
    if (rf & RflagsBits::CF) != 0 {
        append(&mut sb, "CF");
    }
    if (rf & RflagsBits::PF) != 0 {
        append(&mut sb, "PF");
    }
    if (rf & RflagsBits::DF) != 0 {
        append(&mut sb, "DF");
    }
    if (rf & RflagsBits::IF) != 0 {
        append(&mut sb, "IF");
    }
    if (rf & RflagsBits::AC) != 0 {
        append(&mut sb, "AC");
    }
    if (rf & RflagsBits::UIF) != 0 {
        append(&mut sb, "UIF");
    }
    if sb.is_empty() {
        sb.push_str("<empty>");
    }
    sb
}

fn find_traits(code: &[u8], addr: u64) {
    //Must then check all the calls for possible trait objects
    let mut instruction_queue = Vec::new();
    let mut function_call_queue: Queue<(u64, Instruction)> = queue![];
    let mut function_arguments: HashMap<u64, &[u64]> = HashMap::new();

    let mut decoder = Decoder::with_ip(64, code, addr, DecoderOptions::NONE);
    let mut info_factory = InstructionInfoFactory::new();
    let mut instr = Instruction::default();
    let mut formatter = GasFormatter::new();
    let mut output = String::new();

    // let mut rsi_reg_val: (u64, Instruction) = (0, Instruction::new());
    // let mut rcx_reg_val: (u64, Instruction) = (0, Instruction::new());
    // let mut rdi_reg_val: u64 = 0;

    while decoder.can_decode() {
        decoder.decode_out(&mut instr);

        // Gets offsets in the instruction of the displacement and immediates and their sizes.
        // This can be useful if there are relocations in the binary. The encoder has a similar
        // method. This method must be called after decode() and you must pass in the last
        // instruction decode() returned.
        output.clear();
        formatter.format(&instr, &mut output);

        let offsets = decoder.get_constant_offsets(&instr);
        instruction_queue.push(instr);

        // For quick hacks, it's fine to use the Display trait to format an instruction,
        // but for real code, use a formatter, eg. MasmFormatter. See other examples.
        println!("{:016X} {}", instr.ip(), output);

        let op_code = instr.op_code();
        // let info = info_factory.info(&instr);
        let fpu_info = instr.fpu_stack_increment_info();

        if (instr.mnemonic() == Mnemonic::Call) {
            function_call_queue.add((instr.ip(), instr));

            for i in (instruction_queue.len()-5 .. instruction_queue.len()-1).rev(){
                let ins = &instruction_queue[i];
                let ins_op_code = ins.op_code();
                let ins_info = info_factory.info(ins);
                let mut trait_object_call = false;
                for reg_info in ins_info.used_registers() {
                    
        
                    if (reg_info.access() == OpAccess::Write) {
                        if (reg_info.register() == Register::RSI) {
                            println!("    V-Table Address: {:x}", ins.memory_displacement64());
                            println!("TRAIT OBJECT");
                            trait_object_call = true;
                            break;
                            // rsi_reg_val = (ins.memory_displacement64(), *ins);
                        }
                        if (reg_info.register() == Register::RCX) {
                            println!("    V-Table Address: {:x}", ins.memory_displacement64());
                            println!("TRAIT OBJECT");
                            trait_object_call = true;
                            break;
                            // rcx_reg_val = (ins.memory_displacement64(), ins);
                        }
                    }
                }

                if(trait_object_call){
                    break;
                }
            }

            // for ins in &instruction_queue[instruction_queue.len() - 5..instruction_queue.len()]{
            //     let ins_op_code = ins.op_code();
            //     let ins_info = info_factory.info(ins);
            //     let mut trait_object_call = false;
            //     for reg_info in ins_info.used_registers() {
                    
        
            //         if (reg_info.access() == OpAccess::Write) {
            //             if (reg_info.register() == Register::RSI) {
            //                 println!("    V-Table Address: {:x}", ins.memory_displacement64());
            //                 println!("TRAIT OBJECT");
            //                 trait_object_call = true;
            //                 break;
            //                 // rsi_reg_val = (ins.memory_displacement64(), *ins);
            //             }
            //             if (reg_info.register() == Register::RCX) {
            //                 println!("    V-Table Address: {:x}", ins.memory_displacement64());
            //                 println!("TRAIT OBJECT");
            //                 trait_object_call = true;
            //                 break;
            //                 // rcx_reg_val = (ins.memory_displacement64(), ins);
            //             }
            //         }
            //     }

            //     if(trait_object_call){
            //         break;
            //     }

            // }

            
        }

        println!("    OpCode: {}", op_code.op_code_string());
        println!("    Instruction: {}", op_code.instruction_string());
        println!("    Encoding: {:?}", instr.encoding());
        println!("    Mnemonic: {:?}", instr.mnemonic());
        println!("    Code: {:?}", instr.code());
        println!(
            "    CpuidFeature: {}",
            instr
                .cpuid_features()
                .iter()
                .map(|&a| format!("{:?}", a))
                .collect::<Vec<String>>()
                .join(" and ")
        );
        println!("    FlowControl: {:?}", instr.flow_control());
        if fpu_info.writes_top() {
            if fpu_info.increment() == 0 {
                println!("    FPU TOP: the instruction overwrites TOP");
            } else {
                println!("    FPU TOP inc: {}", fpu_info.increment());
            }
            println!(
                "    FPU TOP cond write: {}",
                if fpu_info.conditional() {
                    "true"
                } else {
                    "false"
                }
            );
        }
        if offsets.has_displacement() {
            println!(
                "    Displacement offset = {}, size = {}",
                offsets.displacement_offset(),
                offsets.displacement_size()
            );
        }
        if offsets.has_immediate() {
            println!(
                "    Immediate offset = {}, size = {}",
                offsets.immediate_offset(),
                offsets.immediate_size()
            );
        }
        if offsets.has_immediate2() {
            println!(
                "    Immediate #2 offset = {}, size = {}",
                offsets.immediate_offset2(),
                offsets.immediate_size2()
            );
        }
        if instr.is_stack_instruction() {
            println!("    SP Increment: {}", instr.stack_pointer_increment());
        }
        if instr.condition_code() != ConditionCode::None {
            println!("    Condition code: {:?}", instr.condition_code());
        }
        if instr.rflags_read() != RflagsBits::NONE {
            println!("    RFLAGS Read: {}", flags(instr.rflags_read()));
        }
        if instr.rflags_written() != RflagsBits::NONE {
            println!("    RFLAGS Written: {}", flags(instr.rflags_written()));
        }
        if instr.rflags_cleared() != RflagsBits::NONE {
            println!("    RFLAGS Cleared: {}", flags(instr.rflags_cleared()));
        }
        if instr.rflags_set() != RflagsBits::NONE {
            println!("    RFLAGS Set: {}", flags(instr.rflags_set()));
        }
        if instr.rflags_undefined() != RflagsBits::NONE {
            println!("    RFLAGS Undefined: {}", flags(instr.rflags_undefined()));
        }
        if instr.rflags_modified() != RflagsBits::NONE {
            println!("    RFLAGS Modified: {}", flags(instr.rflags_modified()));
        }
        if instr.op_kinds().any(|op_kind| op_kind == OpKind::Memory) {
            let size = instr.memory_size().size();
            if size != 0 {
                println!("    Memory size: {}", size);
            }
        }
        // for i in 0..instr.op_count() {
        //     println!("    Op{}Access: {:?}", i, info.op_access(i));
        // }
        // for i in 0..op_code.op_count() {
        //     println!("    Op{}: {:?}", i, op_code.op_kind(i));
        // }
        // for reg_info in info.used_registers() {
        //     println!("    Used reg: {:?}", reg_info);

        //     if (reg_info.access() == OpAccess::Write) {
        //         if (reg_info.register() == Register::RSI) {
        //             println!("    V-Table Address: {:x}", instr.memory_displacement64());

        //             rsi_reg_val = (instr.memory_displacement64(), instr);
        //         }
        //         if (reg_info.register() == Register::RCX) {
        //             println!("    V-Table Address: {:x}", instr.memory_displacement64());

        //             rcx_reg_val = (instr.memory_displacement64(), instr);
        //         }
        //     }
        // }
        // for mem_info in info.used_memory() {
        //     println!("    Used mem: {:?}", mem_info);
        // }
    }

    // let instructions = handler.disasm_all(code, addr).unwrap();

    // for counter in 0.. instructions.as_ref().len(){

    //     let i = &instructions[counter];

    //     let detail: InsnDetail = handler.insn_detail(&i).expect("Failed to get insn detail");
    //     let arch_detail: ArchDetail = detail.arch_detail();
    //     let ops = arch_detail.operands();

    //     println!();
    //     println!("{}", i);
    //     let output: &[(&str, String)] = &[
    //         ("insn id:", format!("{:?}", i.id().0)),
    //         ("bytes:", format!("{:?}", i.bytes())),
    //         ("read regs:", reg_names(&handler, detail.regs_read())),
    //         ("write regs:", reg_names(&handler, detail.regs_write())),
    //         ("insn groups:", group_names(&handler, detail.groups())),
    //         ("mnemonic:",i.mnemonic().unwrap().to_string()),
    //     ];

    //     let reg = RegId::from(55);

    //     if(group_names(handler, detail.groups()).contains("call")){
    //         function_call_queue.add((i.address(),i));
    //         function_arguments.insert(i.address(), &[0x89,0x87]);
    //     }

    //     for &(ref name, ref message) in output.iter() {
    //         println!("{:4}{:12} {}", "", name, message);
    //     }

    //     println!("{:4}operands: {}", "", ops.len());

    //     for op in ops {
    //         println!("{:8}{:?}", "", op);

    //     }
}

// print!("{:x?}",function_queue);

fn main() {
    //1: filename 2: entry point
    let args: Vec<String> = env::args().collect();

    let binary =
        read(args.get(1).expect("Please enter the name of the file")).expect("Error reading file");
    let entry_point_string = args
        .get(2)
        .expect("Please enter the entry point of the binary")
        .trim_start_matches("0x");
    let entry_point_address = u64::from_str_radix(entry_point_string, 16).unwrap();
    print!("{:x}\n", entry_point_address);

    // let binary = read("shapes_mixed_stripped").expect("Error reading file");
    let f_slice = binary.as_slice();
    let elf_file = ElfBytes::<AnyEndian>::minimal_parse(f_slice).expect("Incorrect file format");

    let (sct_headers, str_tab) = elf_file
        .section_headers_with_strtab()
        .expect("Section headers error");

    let (shdr, strtab) = (
        sct_headers.expect("section headers not found"),
        str_tab.expect("no string table"),
    );

    // let shstrndx = elf_file.ehdr.e_shstrndx;

    let mut text_section_addr = 0;
    //find .text to start disas
    for header in shdr {
        let strname = strtab
            .get(header.sh_name.try_into().expect("Can not read header"))
            .unwrap();
        if (strname == ".text") {
            text_section_addr = header.sh_addr;
            print!("{:#?} {:x}\n", strname, text_section_addr);
            let text_bytes = elf_file.section_data(&header);
        }
    }

    let cs = Capstone::new()
        .x86()
        .mode(capstone::arch::x86::ArchMode::Mode64)
        .syntax(capstone::arch::x86::ArchSyntax::Att)
        .detail(true)
        .build()
        .expect("Unable to build capstone");

    // let data=&binary[0x51d50 as usize .. 0x51d70 as usize];
    // print!("{:?}",data);

    let main_address = locate_main(
        &binary[entry_point_address as usize..(entry_point_address + 0xff) as usize],
        entry_point_address,
        &cs,
    );
    // +7 to the main_address to locate "main"
    let user_main = locate_user_main(
        &binary[(main_address + 7) as usize..(main_address + 0xff) as usize],
        main_address + 7,
        &cs,
    );

    print!("Main: {:x}\n", main_address + 7);
    print!("User Main: {:x}\n", user_main + 7);

    find_traits(
        &binary[(user_main + 7) as usize..(main_address + 7) as usize],
        user_main + 7,
    );
}
