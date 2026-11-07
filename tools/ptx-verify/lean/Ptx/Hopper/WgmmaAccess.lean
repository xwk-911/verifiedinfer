import Ptx.Hopper.Syntax

/-! Explicit register accesses of every accepted ordinary instruction. Pending
WGMMA hazards and later register-fence obligations use these names. Unrelated
address arithmetic/TMA/non-bulk operations need not stall behind a WGMMA. -/
namespace Ptx.Hopper.Wgmma
noncomputable section

def operandNames : Ptx.Operand → List String | .reg r => [r] | .imm _ | .tid => []
def addressNames (a : Ptx.Address) : List String := operandNames a.base
def floatNames : Scalar.FloatOperand → List String | .reg r => [r] | .literal _ => []
def integerNames : Ptx.Instr → List String
  | .mov _ d a => d :: operandNames a
  | .param _ d _ => [d]
  | .bin _ _ _ d a b | .setp _ d a b => d :: (operandNames a ++ operandNames b)
  | .load _ d a => d :: addressNames a
  | .store _ a v => addressNames a ++ operandNames v
  | .branch p _ _ => [p]
  | .jump _ | .barrier _ | .ret => []
def scalarNames : Scalar.Instr → List String
  | .integer i => integerNames i
  | .setpGt _ d a b | .addRn _ d a b | .subRn _ d a b | .mulRn _ d a b | .divRn _ d a b | .max _ d a b =>
      d :: (floatNames a ++ floatNames b)
  | .readSpecial d _ => [d]
  | .atomAddU32 d a v => d :: (addressNames a ++ operandNames v)
  | .mov _ d a | .ex2Approx d a => d :: floatNames a
  | .fmaRn _ d a b c => d :: (floatNames a ++ floatNames b ++ floatNames c)
  | .load _ _ d a => d :: addressNames a
  | .store _ _ a v => addressNames a ++ floatNames v
def ampereNames : Ampere.Instr → List String
  | .scalar i => scalarNames i
  | .copy _ d s _ => addressNames d ++ addressNames s
  | .commit | .wait _ | .waitAll => []
  | .loadWord32 _ d a => d :: addressNames a
  | .mma d a b c => d.names ++ a.names ++ b.names ++ c.names
def ordinaryNames : Hopper.Instr → List String
  | .ampere i => ampereNames i
  | .tmaLoad2D dst descriptor x y barrier => addressNames dst ++ operandNames descriptor ++ operandNames x ++ operandNames y ++ addressNames barrier
  | .proxyFenceAsyncShared | .wgmma _ => []
  | .mbarrierInit a n | .arriveExpectTx a n | .completeTx a n => addressNames a ++ operandNames n
  | .mbarrierInval a => addressNames a
  | .tryWaitParity d a p => d :: (addressNames a ++ operandNames p)

end
end Ptx.Hopper.Wgmma
