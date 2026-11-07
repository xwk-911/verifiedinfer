//! Typed frontend data for strict word, exact-real scalar and async subsets.
//!
//! Parsing/type validation and Lean serialization are separate operations. These
//! types retain widths and register declarations; they do not constitute a proof
//! that parsing or compilation preserves PTX semantics.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Width {
    W32,
    W64,
}

impl Width {
    pub fn bits(self) -> u32 {
        match self {
            Self::W32 => 32,
            Self::W64 => 64,
        }
    }

    pub fn registers(self) -> &'static [RegisterType] {
        match self {
            Self::W32 => &[RegisterType::U32, RegisterType::S32, RegisterType::B32],
            Self::W64 => &[RegisterType::U64, RegisterType::B64],
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegisterType {
    U32,
    S32,
    U64,
    B32,
    B64,
    Pred,
    F32,
}

impl RegisterType {
    pub fn emit(self) -> &'static str {
        match self {
            Self::U32 => ".u32",
            Self::S32 => ".s32",
            Self::U64 => ".u64",
            Self::B32 => ".b32",
            Self::B64 => ".b64",
            Self::Pred => ".pred",
            Self::F32 => ".f32",
        }
    }

    pub fn parse(source: &str) -> Option<Self> {
        match source {
            ".u32" => Some(Self::U32),
            ".s32" => Some(Self::S32),
            ".u64" => Some(Self::U64),
            ".b32" => Some(Self::B32),
            ".b64" => Some(Self::B64),
            ".pred" => Some(Self::Pred),
            ".f32" => Some(Self::F32),
            _ => None,
        }
    }

    pub fn emit_scalar(self) -> String {
        match self {
            Self::F32 => "(.floating .f32)".into(),
            ty => format!("(.integer {})", ty.emit()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FloatOperand {
    Register(Register),
    // Exact f32 source literal bits, never an in-memory reinterpretation.
    Literal(u32),
}

impl FloatOperand {
    fn emit(&self) -> String {
        match self {
            Self::Register(reg) => format!("(.reg {})", quote(&reg.name)),
            Self::Literal(bits) => format!(
                "(.literal {{ bits := {bits}, bounded := by decide, finite := by decide }})"
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatBinary {
    AddRn,
    SubRn,
    MulRn,
    DivRn,
    Max,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Axis {
    X,
    Y,
    Z,
}

impl Axis {
    fn emit(self) -> &'static str {
        match self {
            Self::X => "x",
            Self::Y => "y",
            Self::Z => "z",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecialRegister {
    Tid(Axis),
    Ctaid(Axis),
    Ntid(Axis),
}

impl SpecialRegister {
    pub fn parse(source: &str) -> Option<Self> {
        let (name, axis) = source.rsplit_once('.')?;
        let axis = match axis {
            "x" => Axis::X,
            "y" => Axis::Y,
            "z" => Axis::Z,
            _ => return None,
        };
        match name {
            "%tid" => Some(Self::Tid(axis)),
            "%ctaid" => Some(Self::Ctaid(axis)),
            "%ntid" => Some(Self::Ntid(axis)),
            _ => None,
        }
    }

    fn emit(self) -> String {
        let (kind, axis) = match self {
            Self::Tid(axis) => ("tid", axis),
            Self::Ctaid(axis) => ("ctaid", axis),
            Self::Ntid(axis) => ("ntid", axis),
        };
        format!("(.{kind} .{})", axis.emit())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FloatInstruction {
    SetpGt {
        dst: Register,
        a: FloatOperand,
        b: FloatOperand,
    },
    Mov {
        dst: Register,
        src: FloatOperand,
    },
    Binary {
        op: FloatBinary,
        dst: Register,
        a: FloatOperand,
        b: FloatOperand,
    },
    Fma {
        dst: Register,
        a: FloatOperand,
        b: FloatOperand,
        c: FloatOperand,
    },
    Ex2Approx {
        dst: Register,
        src: FloatOperand,
    },
    Load {
        space: Space,
        dst: Register,
        address: Address,
    },
    Store {
        space: Space,
        address: Address,
        value: FloatOperand,
    },
}

impl FloatInstruction {
    fn emit(&self) -> String {
        match self {
            Self::SetpGt { dst, a, b } => format!(
                "(.setpGt .f32 {} {} {})",
                quote(&dst.name),
                a.emit(),
                b.emit()
            ),
            Self::Mov { dst, src } => format!("(.mov .f32 {} {})", quote(&dst.name), src.emit()),
            Self::Binary { op, dst, a, b } => format!(
                "(.{} .f32 {} {} {})",
                match op {
                    FloatBinary::AddRn => "addRn",
                    FloatBinary::SubRn => "subRn",
                    FloatBinary::MulRn => "mulRn",
                    FloatBinary::DivRn => "divRn",
                    FloatBinary::Max => "max",
                },
                quote(&dst.name),
                a.emit(),
                b.emit()
            ),
            Self::Fma { dst, a, b, c } => format!(
                "(.fmaRn .f32 {} {} {} {})",
                quote(&dst.name),
                a.emit(),
                b.emit(),
                c.emit()
            ),
            Self::Ex2Approx { dst, src } => {
                format!("(.ex2Approx {} {})", quote(&dst.name), src.emit())
            }
            Self::Load {
                space,
                dst,
                address,
            } => format!(
                "(.load .f32 .{} {} {})",
                space.emit(),
                quote(&dst.name),
                address.emit()
            ),
            Self::Store {
                space,
                address,
                value,
            } => format!(
                "(.store .f32 .{} {} {})",
                space.emit(),
                address.emit(),
                value.emit()
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Register {
    pub name: String,
    pub ty: RegisterType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Immediate(u64),
    Register(Register),
    TidX,
}

impl Operand {
    fn emit(&self) -> String {
        match self {
            Self::Immediate(value) => format!("(.imm {value})"),
            Self::Register(reg) => format!("(.reg {})", quote(&reg.name)),
            Self::TidX => ".tid".into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Address {
    pub base: Operand,
    pub offset: u64,
}

impl Address {
    fn emit(&self) -> String {
        format!(
            "{{ base := {}, offset := {} }}",
            self.base.emit(),
            self.offset
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Space {
    Global,
    Shared,
}

impl Space {
    fn emit(self) -> &'static str {
        match self {
            Self::Global => "global",
            Self::Shared => "shared",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Shr,
}

impl BinOp {
    fn emit(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Shr => "shr",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Comparison {
    Lt,
    Ge,
    Eq,
}

impl Comparison {
    fn emit(self) -> &'static str {
        match self {
            Self::Lt => "lt",
            Self::Ge => "ge",
            Self::Eq => "eq",
        }
    }
}

/// Fixed CTA-local layout-v0 mbarrier forms. Ordering qualifiers are part of
/// the selected variant, rather than discarded strings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MbarrierInstruction {
    Init {
        address: Address,
        count: Operand,
    },
    Inval {
        address: Address,
    },
    ArriveExpectTx {
        address: Address,
        count: Operand,
    },
    CompleteTx {
        address: Address,
        count: Operand,
    },
    TryWaitParity {
        dst: Register,
        address: Address,
        parity: Operand,
    },
}
impl MbarrierInstruction {
    fn emit(&self) -> String {
        match self {
            Self::Init { address, count } => {
                format!("(.mbarrierInit {} {})", address.emit(), count.emit())
            }
            Self::Inval { address } => format!("(.mbarrierInval {})", address.emit()),
            Self::ArriveExpectTx { address, count } => {
                format!("(.arriveExpectTx {} {})", address.emit(), count.emit())
            }
            Self::CompleteTx { address, count } => {
                format!("(.completeTx {} {})", address.emit(), count.emit())
            }
            Self::TryWaitParity {
                dst,
                address,
                parity,
            } => format!(
                "(.tryWaitParity {} {} {})",
                quote(&dst.name),
                address.emit(),
                parity.emit()
            ),
        }
    }
}

/// Fixed PTX 8.0 2-D tile load; raw cluster addresses are retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TmaInstruction {
    pub dst: Address,
    pub descriptor: Operand,
    pub x: Operand,
    pub y: Operand,
    pub barrier: Address,
}
impl TmaInstruction {
    fn emit(&self) -> String {
        format!(
            "(.tmaLoad2D {} {} {} {} {})",
            self.dst.emit(),
            self.descriptor.emit(),
            self.x.emit(),
            self.y.emit(),
            self.barrier.emit()
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WgmmaInstruction {
    Fence,
    Commit,
    Wait(u64),
    MmaF16 {
        d: Box<[Register; 4]>,
        a: Register,
        b: Register,
        scale_d: Operand,
    },
}

impl WgmmaInstruction {
    fn emit(&self) -> String {
        let body = match self {
            Self::Fence => ".fence".into(),
            Self::Commit => ".commit".into(),
            Self::Wait(keep) => format!("(.wait {keep})"),
            Self::MmaF16 { d, a, b, scale_d } => format!(
                "(.mma ⟨{}⟩ {} {} {})",
                d.iter()
                    .map(|r| quote(&r.name))
                    .collect::<Vec<_>>()
                    .join(","),
                quote(&a.name),
                quote(&b.name),
                scale_d.emit()
            ),
        };
        format!("(.wgmma {body})")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShuffleMode {
    Up,
    Down,
    Bfly,
    Idx,
}

impl ShuffleMode {
    fn emit(self) -> &'static str {
        match self {
            Self::Up => "up",
            Self::Down => "down",
            Self::Bfly => "bfly",
            Self::Idx => "idx",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShuffleInstruction {
    pub mode: ShuffleMode,
    pub dst: Register,
    pub predicate: Option<Register>,
    pub a: Operand,
    pub b: Operand,
    pub c: Operand,
    pub mask: Operand,
}

impl ShuffleInstruction {
    fn emit(&self) -> String {
        let predicate = self.predicate.as_ref().map_or_else(
            || "none".to_string(),
            |register| format!("(some {})", quote(&register.name)),
        );
        format!(
            "(.shfl .{} {} {} {} {} {} {})",
            self.mode.emit(),
            quote(&self.dst.name),
            predicate,
            self.a.emit(),
            self.b.emit(),
            self.c.emit(),
            self.mask.emit()
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemoryScope {
    Cta,
    Gpu,
    Sys,
}

impl MemoryScope {
    fn emit(&self) -> &'static str {
        match self {
            Self::Cta => "cta",
            Self::Gpu => "gpu",
            Self::Sys => "sys",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderedInstruction {
    Load {
        acquire: bool,
        scope: MemoryScope,
        dst: Register,
        address: Address,
    },
    Store {
        release: bool,
        scope: MemoryScope,
        address: Address,
        value: Operand,
    },
}

impl OrderedInstruction {
    fn emit(&self) -> String {
        match self {
            Self::Load {
                acquire,
                scope,
                dst,
                address,
            } => format!(
                "(.load .{} .{} {} {})",
                if *acquire { "acquire" } else { "relaxed" },
                scope.emit(),
                quote(&dst.name),
                address.emit()
            ),
            Self::Store {
                release,
                scope,
                address,
                value,
            } => format!(
                "(.store .{} .{} {} {})",
                if *release { "release" } else { "relaxed" },
                scope.emit(),
                address.emit(),
                value.emit()
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instruction {
    Ordered(Box<OrderedInstruction>),
    Shuffle(Box<ShuffleInstruction>),
    Wgmma(WgmmaInstruction),
    Tma(TmaInstruction),
    ProxyFenceAsyncShared,
    Mbarrier(MbarrierInstruction),
    Async(AsyncInstruction),
    Tensor(TensorInstruction),
    Float(FloatInstruction),
    AtomicAddU32 {
        dst: Register,
        address: Address,
        increment: Operand,
    },
    ReadSpecial {
        dst: Register,
        source: SpecialRegister,
    },
    Mov {
        width: Width,
        dst: Register,
        src: Operand,
    },
    Param {
        width: Width,
        dst: Register,
        name: String,
    },
    Bin {
        op: BinOp,
        input: Width,
        output: Width,
        dst: Register,
        a: Operand,
        b: Operand,
    },
    Setp {
        cmp: Comparison,
        dst: Register,
        a: Operand,
        b: Operand,
    },
    Load {
        space: Space,
        dst: Register,
        address: Address,
    },
    Store {
        space: Space,
        address: Address,
        value: Operand,
    },
    Branch {
        predicate: Register,
        positive: bool,
        target: usize,
    },
    Jump(usize),
    Barrier(u64),
    Ret,
}

impl Instruction {
    pub fn emit(&self) -> String {
        match self {
            Self::Ordered(instruction) => instruction.emit(),
            Self::Shuffle(instruction) => instruction.emit(),
            Self::Wgmma(instruction) => instruction.emit(),
            Self::Tma(instruction) => instruction.emit(),
            Self::ProxyFenceAsyncShared => ".proxyFenceAsyncShared".into(),
            Self::Mbarrier(instruction) => instruction.emit(),
            Self::Async(instruction) => instruction.emit(),
            Self::Tensor(instruction) => instruction.emit(),
            Self::Float(instruction) => instruction.emit(),
            Self::AtomicAddU32 {
                dst,
                address,
                increment,
            } => format!(
                "(.atomAddU32 {} {} {})",
                quote(&dst.name),
                address.emit(),
                increment.emit()
            ),
            Self::ReadSpecial { dst, source } => {
                format!("(.readSpecial {} {})", quote(&dst.name), source.emit())
            }
            Self::Mov { width, dst, src } => {
                format!(
                    "(.mov {} {} {})",
                    width.bits(),
                    quote(&dst.name),
                    src.emit()
                )
            }
            Self::Param { width, dst, name } => {
                format!(
                    "(.param {} {} {})",
                    width.bits(),
                    quote(&dst.name),
                    quote(name)
                )
            }
            Self::Bin {
                op,
                input,
                output,
                dst,
                a,
                b,
            } => format!(
                "(.bin .{} {} {} {} {} {})",
                op.emit(),
                input.bits(),
                output.bits(),
                quote(&dst.name),
                a.emit(),
                b.emit()
            ),
            Self::Setp { cmp, dst, a, b } => format!(
                "(.setp .{} {} {} {})",
                cmp.emit(),
                quote(&dst.name),
                a.emit(),
                b.emit()
            ),
            Self::Load {
                space,
                dst,
                address,
            } => format!(
                "(.load .{} {} {})",
                space.emit(),
                quote(&dst.name),
                address.emit()
            ),
            Self::Store {
                space,
                address,
                value,
            } => format!(
                "(.store .{} {} {})",
                space.emit(),
                address.emit(),
                value.emit()
            ),
            Self::Branch {
                predicate,
                positive,
                target,
            } => {
                format!("(.branch {} {positive} {target})", quote(&predicate.name))
            }
            Self::Jump(target) => format!("(.jump {target})"),
            Self::Barrier(id) => format!("(.barrier {id})"),
            Self::Ret => ".ret".into(),
        }
    }

    pub fn emit_scalar(&self) -> String {
        match self {
            Self::Float(instruction) => instruction.emit(),
            Self::ReadSpecial { .. } | Self::AtomicAddU32 { .. } => self.emit(),
            instruction => format!("(.integer {})", instruction.emit()),
        }
    }

    pub fn emit_shuffle(&self) -> String {
        match self {
            Self::Shuffle(instruction) => instruction.emit(),
            instruction => format!("(.scalar {})", instruction.emit_scalar()),
        }
    }

    pub fn emit_ordered(&self) -> String {
        match self {
            Self::Ordered(instruction) => instruction.emit(),
            instruction => format!("(.scalar {})", instruction.emit_scalar()),
        }
    }

    pub fn requires_ordered(&self) -> bool {
        matches!(self, Self::Ordered(_))
    }

    pub fn requires_shuffle(&self) -> bool {
        matches!(self, Self::Shuffle(_))
    }

    pub fn emit_ampere(&self) -> String {
        match self {
            Self::Async(instruction) => instruction.emit(),
            Self::Tensor(instruction) => instruction.emit(),
            instruction => format!("(.scalar {})", instruction.emit_scalar()),
        }
    }

    pub fn emit_hopper(&self) -> String {
        match self {
            Self::Wgmma(instruction) => instruction.emit(),
            Self::Tma(instruction) => instruction.emit(),
            Self::ProxyFenceAsyncShared => ".proxyFenceAsyncShared".into(),
            Self::Mbarrier(instruction) => instruction.emit(),
            instruction => format!("(.ampere {})", instruction.emit_ampere()),
        }
    }

    pub fn requires_hopper(&self) -> bool {
        matches!(
            self,
            Self::Wgmma(_) | Self::Mbarrier(_) | Self::Tma(_) | Self::ProxyFenceAsyncShared
        )
    }

    pub fn requires_ampere(&self) -> bool {
        matches!(self, Self::Async(_) | Self::Tensor(_))
    }

    pub fn requires_scalar(&self) -> bool {
        matches!(
            self,
            Self::Float(_) | Self::ReadSpecial { .. } | Self::AtomicAddU32 { .. }
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TensorInstruction {
    LoadWord32 {
        space: Space,
        dst: Register,
        address: Address,
    },
    MmaF16 {
        d: Box<[Register; 4]>,
        a: Box<[Register; 4]>,
        b: Box<[Register; 2]>,
        c: Box<[Register; 4]>,
    },
}

impl TensorInstruction {
    fn emit(&self) -> String {
        fn vector<const N: usize>(regs: &[Register; N]) -> String {
            format!(
                "⟨{}⟩",
                regs.iter()
                    .map(|r| quote(&r.name))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        }
        match self {
            Self::LoadWord32 {
                space,
                dst,
                address,
            } => format!(
                "(.loadWord32 .{} {} {})",
                space.emit(),
                quote(&dst.name),
                address.emit()
            ),
            Self::MmaF16 { d, a, b, c } => format!(
                "(.mma {} {} {} {})",
                vector(d),
                vector(a),
                vector(b),
                vector(c)
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CopyCache {
    Ca,
    Cg,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AsyncInstruction {
    Copy {
        cache: CopyCache,
        dst: Address,
        src: Address,
        bytes: u64,
    },
    Commit,
    Wait(u64),
    WaitAll,
}

impl AsyncInstruction {
    fn emit(&self) -> String {
        match self {
            Self::Copy {
                cache,
                dst,
                src,
                bytes,
            } => format!(
                "(.copy .{} {} {} {})",
                match cache {
                    CopyCache::Ca => "ca",
                    CopyCache::Cg => "cg",
                },
                dst.emit(),
                src.emit(),
                bytes
            ),
            Self::Commit => ".commit".into(),
            Self::Wait(keep) => format!("(.wait {keep})"),
            Self::WaitAll => ".waitAll".into(),
        }
    }
}

pub fn quote(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}
