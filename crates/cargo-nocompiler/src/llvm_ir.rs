//! Structured LLVM IR capture using the C ABI of the pinned rustc toolchain.
use crate::Result;
use libloading::Library;
use std::{
    collections::BTreeMap,
    ffi::{c_char, c_int, c_uint, c_void},
    path::Path,
    ptr,
};

type Ref = *mut c_void;
type Id = usize;

macro_rules! llvm_api {
    ($($field:ident : $name:ident($($arg:ty),*) -> $ret:ty),* $(,)?) => {
        struct Api {
            $($field: unsafe extern "C" fn($($arg),*) -> $ret,)*
            _library: Library,
        }

        impl Api {
            fn load(path: &Path) -> Result<Self> {
                // The caller supplies the shared library of the same pinned
                // toolchain that emitted the IR. Keep it loaded for all calls.
                unsafe {
                    let library = Library::new(path)?;
                    Ok(Self {
                        $($field: *library.get(concat!(stringify!($name), "\0").as_bytes())?,)*
                        _library: library,
                    })
                }
            }
        }
    };
}

llvm_api! {
    context: LLVMContextCreate() -> Ref,
    dispose_context: LLVMContextDispose(Ref) -> (),
    buffer: LLVMCreateMemoryBufferWithMemoryRangeCopy(*const c_char, usize, *const c_char) -> Ref,
    parse: LLVMParseIRInContext(Ref, Ref, *mut Ref, *mut *mut c_char) -> c_int,
    dispose_module: LLVMDisposeModule(Ref) -> (),
    name: LLVMGetValueName2(Ref, *mut usize) -> *const c_char,
    first_function: LLVMGetFirstFunction(Ref) -> Ref,
    next_function: LLVMGetNextFunction(Ref) -> Ref,
    call_conv: LLVMGetFunctionCallConv(Ref) -> c_uint,
    function_type: LLVMGlobalGetValueType(Ref) -> Ref,
    return_type: LLVMGetReturnType(Ref) -> Ref,
    is_var_arg: LLVMIsFunctionVarArg(Ref) -> c_int,
    count_params: LLVMCountParams(Ref) -> c_uint,
    param: LLVMGetParam(Ref, c_uint) -> Ref,
    value_type: LLVMTypeOf(Ref) -> Ref,
    type_kind: LLVMGetTypeKind(Ref) -> c_uint,
    int_width: LLVMGetIntTypeWidth(Ref) -> c_uint,
    first_block: LLVMGetFirstBasicBlock(Ref) -> Ref,
    next_block: LLVMGetNextBasicBlock(Ref) -> Ref,
    terminator: LLVMGetBasicBlockTerminator(Ref) -> Ref,
    first_instr: LLVMGetFirstInstruction(Ref) -> Ref,
    next_instr: LLVMGetNextInstruction(Ref) -> Ref,
    opcode: LLVMGetInstructionOpcode(Ref) -> c_uint,
    count_successors: LLVMGetNumSuccessors(Ref) -> c_uint,
    successor: LLVMGetSuccessor(Ref, c_uint) -> Ref,
    count_operands: LLVMGetNumOperands(Ref) -> c_int,
    operand: LLVMGetOperand(Ref, c_uint) -> Ref,
    count_incoming: LLVMCountIncoming(Ref) -> c_uint,
    incoming: LLVMGetIncomingValue(Ref, c_uint) -> Ref,
    allocated: LLVMGetAllocatedType(Ref) -> Ref,
    is_const_int: LLVMIsAConstantInt(Ref) -> Ref,
    signed_const: LLVMConstIntGetSExtValue(Ref) -> i64,
}

struct Module<'a> {
    api: &'a Api,
    context: Ref,
    module: Ref,
}

impl Drop for Module<'_> {
    fn drop(&mut self) {
        // The module belongs to the context, which must outlive it.
        unsafe {
            if !self.module.is_null() {
                (self.api.dispose_module)(self.module);
            }
            (self.api.dispose_context)(self.context);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Word,
    Pointer,
    Other,
}

pub struct Parameter {
    pub id: Id,
    pub name: String,
    pub ty: Type,
}

#[derive(Clone, Copy)]
pub enum Operand {
    Constant(i128),
    Value(Id),
}

pub enum Instruction {
    Return(Operand),
    Alloca(Id),
    Load(Id, Id),
    Store(Operand, Id),
    Phi(Id, Vec<Operand>),
    Add(Id, Operand, Operand),
    Sub(Id, Operand, Operand),
    Mul(Id, Operand, Operand),
    Shift(Id, Operand, Operand),
    Clobber,
}

pub struct Block {
    pub id: Id,
    pub successors: Vec<Id>,
    pub instructions: Vec<Instruction>,
}

pub struct Function {
    pub parameters: Vec<Parameter>,
    pub result: Type,
    pub blocks: Vec<Block>,
    pub value_names: BTreeMap<Id, String>,
}

impl Api {
    // Every reference passed to these helpers is owned by the live module
    // being traversed in capture and has the kind checked by its caller.
    unsafe fn read_type(&self, ty: Ref) -> Type {
        unsafe {
            match (self.type_kind)(ty) {
                8 if (self.int_width)(ty) == 64 => Type::Word,
                12 => Type::Pointer,
                _ => Type::Other,
            }
        }
    }

    unsafe fn value_name(&self, value: Ref) -> String {
        unsafe {
            let mut length = 0;
            let name = (self.name)(value, &mut length);
            if length == 0 || name.is_null() {
                return String::new();
            }
            String::from_utf8_lossy(std::slice::from_raw_parts(name.cast(), length)).into_owned()
        }
    }

    unsafe fn read_operand(&self, value: Ref) -> Operand {
        unsafe {
            if !(self.is_const_int)(value).is_null()
                && (self.int_width)((self.value_type)(value)) <= 64
            {
                Operand::Constant(i128::from((self.signed_const)(value)))
            } else {
                Operand::Value(value as Id)
            }
        }
    }

    unsafe fn read_instruction(&self, instr: Ref) -> Option<Instruction> {
        use Instruction::*;
        // Opcode numbers are LLVMOpcode's stable public C ABI values.
        unsafe {
            let id = instr as Id;
            let count = (self.count_operands)(instr);
            let raw = |i| (self.operand)(instr, i);
            let operand = |i| self.read_operand(raw(i));
            let word = || self.read_type((self.value_type)(instr)) == Type::Word;
            match (self.opcode)(instr) {
                1 if count == 1 => Some(Return(operand(0))),
                26 if count == 1
                    && self.read_type((self.allocated)(instr)) == Type::Word
                    && matches!(operand(0), Operand::Constant(1)) =>
                {
                    Some(Alloca(id))
                }
                27 if count == 1 && word() => Some(Load(id, raw(0) as Id)),
                28 if count == 2 && self.read_type((self.value_type)(raw(0))) == Type::Word => {
                    Some(Store(operand(0), raw(1) as Id))
                }
                44 if word() => Some(Phi(
                    id,
                    (0..(self.count_incoming)(instr))
                        .map(|i| self.read_operand((self.incoming)(instr, i)))
                        .collect(),
                )),
                8 if count == 2 && word() => Some(Add(id, operand(0), operand(1))),
                10 if count == 2 && word() => Some(Sub(id, operand(0), operand(1))),
                12 if count == 2 && word() => Some(Mul(id, operand(0), operand(1))),
                20 if count == 2 && word() => Some(Shift(id, operand(0), operand(1))),
                5 | 28 | 45 | 56 | 57 | 67 => Some(Clobber),
                _ => None,
            }
        }
    }
}

pub fn capture(sysroot: &Path, ir: &str) -> Result<BTreeMap<String, Function>> {
    let library = std::fs::read_dir(sysroot.join("lib"))?
        .filter_map(|item| item.ok())
        .map(|item| item.path())
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("libLLVM.so.") && name.contains("-rust-"))
        })
        .ok_or("pinned rustc LLVM shared library was not found")?;
    let api = Api::load(&library)?;
    // We own all handles until Module drops. LLVMParseIRInContext takes
    // ownership of the memory buffer, which holds a copy of the IR.
    unsafe {
        let mut module = Module {
            api: &api,
            context: (api.context)(),
            module: ptr::null_mut(),
        };
        let buffer = (api.buffer)(ir.as_ptr().cast(), ir.len(), c"rustc.ll".as_ptr());
        if (api.parse)(module.context, buffer, &mut module.module, ptr::null_mut()) != 0
            || module.module.is_null()
        {
            return Err("pinned LLVM rejected generated IR".into());
        }
        let mut functions = BTreeMap::new();
        let mut function = (api.first_function)(module.module);
        while !function.is_null() {
            let current = function;
            function = (api.next_function)(current);
            let mut block = (api.first_block)(current);
            let ty = (api.function_type)(current);
            let count = (api.count_params)(current);
            if block.is_null()
                || count > 8
                || (api.call_conv)(current) != 0
                || (api.is_var_arg)(ty) != 0
            {
                continue;
            }
            let mut unnamed = 0;
            let parameters = (0..count)
                .map(|i| {
                    let parameter = (api.param)(current, i);
                    let mut name = api.value_name(parameter);
                    if name.is_empty() {
                        name = unnamed.to_string();
                        unnamed += 1;
                    }
                    Parameter {
                        id: parameter as Id,
                        name,
                        ty: api.read_type((api.value_type)(parameter)),
                    }
                })
                .collect();
            let result = api.read_type((api.return_type)(ty));
            let mut blocks = Vec::new();
            let mut value_names = BTreeMap::new();
            while !block.is_null() {
                let terminal = (api.terminator)(block);
                if terminal.is_null() {
                    blocks.clear();
                    break;
                }
                let successors = (0..(api.count_successors)(terminal))
                    .map(|i| (api.successor)(terminal, i) as Id)
                    .collect();
                let mut instructions = Vec::new();
                let mut instr = (api.first_instr)(block);
                let mut instruction_index = 0;
                while !instr.is_null() {
                    if let Some(value) = api.read_instruction(instr) {
                        let mut name = api.value_name(instr);
                        if name.is_empty() {
                            name = format!("block{}:instruction{instruction_index}", blocks.len());
                        }
                        value_names.insert(instr as Id, name);
                        instructions.push(value);
                    }
                    instruction_index += 1;
                    instr = (api.next_instr)(instr);
                }
                blocks.push(Block {
                    id: block as Id,
                    successors,
                    instructions,
                });
                block = (api.next_block)(block);
            }
            functions.insert(
                api.value_name(current),
                Function {
                    parameters,
                    result,
                    blocks,
                    value_names,
                },
            );
        }
        Ok(functions)
    }
}
