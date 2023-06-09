// Add a vector of function addresses using nuclues
// Since we know the range of each function's body we can disassemble only that portion
// How the fuck do i add nucleus?????????
// AND HOW DO I MAKE NUCLEUS WORK????????????????????

use std::{
    collections::{HashMap, VecDeque},
    env::{self, args},
    fs::{read, File},
    io::{BufRead, BufReader},
    slice::SplitInclusiveMut,
};

use capstone::{
    prelude::{ArchDetail, BuildsCapstone, BuildsCapstoneSyntax},
    Capstone, Insn, InsnDetail, InsnGroupId, Instructions, RegId,
};
use elf::{endian::AnyEndian, ElfBytes};
use iced_x86::*;

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

    let main_addr = (dis.as_ref()[0].bytes()[5] as u64 * 16 * 16 * 16 * 16)
        + (dis.as_ref()[0].bytes()[4] as u64 * 16 * 16)
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


/**
 * ----------------
 * |   destructor |
 * ----------------
 * |    size      |
 * ----------------
 * |    allign    |
 * ----------------
 */
fn valid_vtable(addr: u64, text_section_address:u64, text_section_size:u64 ,data_rel_addr: u64, data_rel_size: u64,data_rel_section:&[u8]) -> bool{

    if addr>data_rel_addr+data_rel_size || addr<data_rel_addr{
        print!("\n Addr: {:x} not in data rel ro\n",addr);
        return false;
    }

    println!();
    
    let index = addr-data_rel_addr;
    let base:u64 = 16;

    //check entry
    let mut entry:u64=0;

    for (i,bytes) in data_rel_section[index as usize .. (index+8)as usize].iter().enumerate(){
        let mult = base.pow(2*i as u32);
        
        entry = entry + (*bytes as u64 * mult ) as u64;
    }

    if entry<text_section_address || entry>text_section_address+text_section_size{
        print!("\n Entry: {:x} not in text\n",entry);

        return false;
    }

    return true;
}

fn find_traits(
    binary: &[u8],
    addr: u64,
    data_rel_addr: u64,
    data_rel_size: u64,
    function_entries: &mut HashMap<u64, (u64, bool)>,
    data_rel_section:&[u8],
    text_section_address:u64,
    text_section_size:u64
) {
    let function_size = function_entries
        .get(&addr)
        .expect("Address not found in the function entries file")
        .0;

    function_entries.insert(addr, (function_size, true));

    println!("\nAnalyzing function at {:x}", addr);
    let code = &binary[(addr) as usize..(addr + function_size) as usize];

    //Must then check all the calls for possible trait objects
    let mut instruction_queue = Vec::new();
    let mut function_call_queue: VecDeque<(u64)> = VecDeque::new();
    // let mut function_arguments: HashMap<u64, &[u64]> = HashMap::new();

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

        instruction_queue.push(instr);

        // For quick hacks, it's fine to use the Display trait to format an instruction,
        // but for real code, use a formatter, eg. MasmFormatter. See other examples.
        println!("{:016X} {}", instr.ip(), output);

        if instruction_queue.len() < 5 {
            continue;
        }

        if instr.mnemonic() == Mnemonic::Call
            && !instr.is_call_far_indirect()
            && !instr.is_call_near_indirect()
        {
            //Did nucleus find the address?
            if function_entries.contains_key(&instr.memory_displacement64()) {
                //if we havent visited that address
                if (!function_call_queue.contains(&instr.memory_displacement64())
                    && !function_entries
                        .get(&instr.memory_displacement64())
                        .unwrap()
                        .1)
                {
                    function_call_queue.push_back(instr.memory_displacement64());

                    //mark the function as visited
                    function_entries.insert(
                        instr.memory_displacement64(),
                        (
                            function_entries
                                .get(&instr.memory_displacement64())
                                .unwrap()
                                .0,
                            true,
                        ),
                    );
                }

                //Trait call checker needs expansion
                //need a way to check instruction queue length
                for i in (instruction_queue.len() - 5..instruction_queue.len() - 1).rev() {
                    let ins = &instruction_queue[i];
                    // let ins_op_code = ins.op_code();
                    let ins_info = info_factory.info(ins);
                    let mut trait_object_call = false;
                    for reg_info in ins_info.used_registers() {
                        //This is not always right
                        if reg_info.access() == OpAccess::Write {
                            if reg_info.register() == Register::RSI {
                                if ins.memory_displacement64() >= data_rel_addr
                                    && ins.memory_displacement64() <= data_rel_addr + data_rel_size 
                                    && valid_vtable(ins.memory_displacement64(), text_section_address, text_section_size, data_rel_addr, data_rel_size, data_rel_section)
                                {
                                    println!(
                                        "    V-Table Address: {:x}",
                                        ins.memory_displacement64()
                                    );
                                    println!("TRAIT OBJECT");
                                    trait_object_call = true;
                                    break;
                                }
                                // rsi_reg_val = (ins.memory_displacement64(), *ins);
                            }
                            if reg_info.register() == Register::RCX {
                                if ins.memory_displacement64() >= data_rel_addr
                                    && ins.memory_displacement64() <= data_rel_addr + data_rel_size
                                    && valid_vtable(ins.memory_displacement64(), text_section_address, text_section_size, data_rel_addr, data_rel_size, data_rel_section)
                                {
                                    println!(
                                        "    V-Table Address: {:x}",
                                        ins.memory_displacement64()
                                    );
                                    println!("TRAIT OBJECT");
                                    trait_object_call = true;
                                    break;
                                }
                                // rcx_reg_val = (ins.memory_displacement64(), ins);
                            }
                        }
                    }

                    if (trait_object_call) {
                        break;
                    }
                }
            }
        }
    }

    println!(
        "\n Function call queue at function {:x}: {:x?}",
        addr, function_call_queue
    );

    while function_call_queue.len() > 0 {
        let next_function = *function_call_queue.get(0).unwrap();
        function_call_queue.remove(0);

        find_traits(
            binary,
            next_function,
            data_rel_addr,
            data_rel_size,
            function_entries,
            data_rel_section,
            text_section_address,
            text_section_size,
        );
    }

    // There are not any more functions to check.
    if function_call_queue.len() < 1 {
        return;
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

fn read_function_entries_file(filename: &str) -> HashMap<u64, (u64, bool)> {
    let file = File::open(filename).unwrap();
    let reader = BufReader::new(file);
    let mut map = HashMap::new();

    for line in reader.lines() {
        let line = line.unwrap();
        let parts: Vec<&str> = line.split('\t').collect();
        let address = u64::from_str_radix(parts[0].trim_start_matches("0x"), 16).unwrap();
        let size = parts[1].parse().unwrap();
        map.insert(address, (size, false));
    }

    map
}

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

    // Create a HashMap with the addresses and sizes for each function
    let mut function_entries = read_function_entries_file("exa_functionEntries");

    let (sct_headers, str_tab) = elf_file
        .section_headers_with_strtab()
        .expect("Section headers error");

    let (shdr, strtab) = (
        sct_headers.expect("section headers not found"),
        str_tab.expect("no string table"),
    );

    // let shstrndx = elf_file.ehdr.e_shstrndx;

    // data.rel.ro bytes stored for v-table extraction
    let mut data_rel_data: &[u8] = &[0];
    let mut data_rel_section = 0;
    let mut data_rel_size = 0;
    let mut text_section: u64 = 0;
    let mut text_section_size: u64 = 0;
    //find .data.rel.ro -> where v-tables are stored
    for header in shdr {
        let strname = strtab
            .get(header.sh_name.try_into().expect("Can not read header"))
            .unwrap();
        if (strname == ".data.rel.ro") {
            data_rel_section = header.sh_addr;
            data_rel_size = header.sh_size;
            println!(
                "{:#?} {:x} size: {:x}\n",
                strname, data_rel_section, data_rel_size
            );
            data_rel_data = elf_file.section_data(&header).unwrap().0;
        }
        if (strname == ".text") {
            text_section = header.sh_addr;
            text_section_size = header.sh_size;
            println!(
                "{:#?} {:x} size: {:x}\n",
                strname, text_section, text_section_size
            );
        }
    }

    let cs = Capstone::new()
        .x86()
        .mode(capstone::arch::x86::ArchMode::Mode64)
        .syntax(capstone::arch::x86::ArchSyntax::Att)
        .detail(true)
        .build()
        .expect("Unable to build capstone");

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
        &binary,
        user_main + 7,
        data_rel_section,
        data_rel_size,
        &mut function_entries,
        data_rel_data,
        text_section,
        text_section_size
    );
}
