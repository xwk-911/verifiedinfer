import Ptx.Kernels.AtomicDispatchThread
import Ptx.Scalar.IntegerMemory
import Ptx.Scalar.Regions

/-! Runtime layout/precondition and independent byte-output specification for
two CTAs of one thread each. Allocation, hardware and full PTX correspondence
remain separate; ticket values and consistency are not preconditions. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

structure Config where
  counter : Nat
  x : Nat
  y : Nat
  counterEnd : counter+4 ≤ 2^64
  xEnd : x+4 ≤ 2^64
  yEnd : y+4 ≤ 2^64
  counterAligned : counter % 4 = 0
  xAligned : x % 4 = 0
  yAligned : y % 4 = 0
  counterX : WordsDisjoint counter 1 x 1
  counterY : WordsDisjoint counter 1 y 1
  xy : WordsDisjoint x 1 y 1

def geometry : Geometry := ⟨⟨2,1,1⟩,.one⟩
def id (cta : Nat) : ThreadId := ⟨⟨cta,0,0⟩,.zero⟩
def counterLoc (cfg : Config) : Location := ⟨.global,cfg.counter⟩
def xLoc (cfg : Config) : Location := ⟨.global,cfg.x⟩
def yLoc (cfg : Config) : Location := ⟨.global,cfg.y⟩
def reply (oracle : Scalar.Oracle) : Nat := match oracle 0 with | .integer value => value | .real _ _ => 0
def ticket (oracle : Scalar.Oracle) : Nat := wrap 32 (reply oracle)
def eventsFor (cfg : Config) (oracle : Scalar.Oracle) : List Scalar.Kind :=
  events cfg.counter cfg.x cfg.y (reply oracle)

def Initialized (cfg : Config) (initial : Scalar.ByteMap) : Prop := RepresentsU32 initial (counterLoc cfg) 0
def Pre (cfg : Config) (launch : Scalar.Launch) : Prop :=
  launch.geometry = geometry ∧ Params cfg.counter cfg.x cfg.y launch.params ∧ Initialized cfg launch.initial
def Post (cfg : Config) (initial output : Scalar.ByteMap) (domain : List Location) : Prop :=
  RepresentsU32 output (counterLoc cfg) 2 ∧ RepresentsU32 output (xLoc cfg) 1 ∧ RepresentsU32 output (yLoc cfg) 2 ∧
  ∀ loc ∈ domain, ¬ InWords cfg.counter 1 loc → ¬ InWords cfg.x 1 loc → ¬ InWords cfg.y 1 loc → output loc = initial loc

theorem valid_id {thread : ThreadId} (hv : thread.Valid geometry) : ∃ cta, cta < 2 ∧ thread = id cta := by
  rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid,geometry,Dim3.Within,Dim3.one] at hv
  have hz : cy = 0 ∧ cz = 0 ∧ tx = 0 ∧ ty = 0 ∧ tz = 0 := by omega
  rcases hz with ⟨rfl,rfl,rfl,rfl,rfl⟩
  exact ⟨cx,hv.1.1,rfl⟩

theorem id_valid {cta : Nat} (hc : cta < 2) : (id cta).Valid geometry := by
  simp [ThreadId.Valid,id,geometry,Dim3.Within,Dim3.zero,Dim3.one,hc]

theorem reply_typed {oracle : Scalar.Oracle} {value : Nat} (ho : oracle 0 = .integer value) : reply oracle = value := by
  simp [reply,ho]

theorem ticket_bound (oracle : Scalar.Oracle) : ticket oracle < 2^32 := Nat.mod_lt _ (by decide)

end
end Ptx.AtomicDispatchEvent
