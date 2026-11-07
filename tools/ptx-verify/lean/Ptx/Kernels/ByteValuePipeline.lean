import Ptx.Generated.ByteValuePipeline
import Ptx.Hopper.ByteContentsOrdinary
import Ptx.Iris.ByteContentsSequence

/-! Parameterized actual store/load source. The PTX input is mechanically
translated to the existing integer AST, then embedded instruction-for-instruction
in the unified interpreter. Oracle replies are retained independently so an
incorrect load reply remains source-produced but can fail value admission.
-/
namespace Ptx.Kernels.ByteValuePipeline
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def thread : ThreadId := ⟨.zero,.zero⟩
def writer : Ptx.Event.EventId := ⟨thread,0⟩
def reader : Ptx.Event.EventId := ⟨thread,1⟩
def base : Location := ⟨.global,64⟩
def payload (value : Nat) : List Symbolic.Byte := (encodeU32 (wrap 32 value)).map Symbolic.Byte.bits
def program : List Hopper.Instr := Generated.byte_value_pipeline.program.map (fun i => .ampere (.scalar (.integer i)))
def params (value : Nat) : Bindings := [("Ptr",64),("Value",value)]
def sourceContext (value : Nat) : Scalar.Context := {id := thread,params := params value,block := .one}
def oracle (reply : Nat) : Wgmma.Oracle := {base := {ampere := {scalar := fun _ => .integer reply,bytes := fun _ => []},wait := fun _ => false}}
def result (value reply : Nat) := (Wgmma.run (sourceContext value) (oracle reply) program 5 {}).toOption.getD ({},[])
def trace (value reply : Nat) : Unified.ThreadTrace := {
  id := thread,oracle := oracle reply,count := 5,final := (result value reply).1
  events := [.base (.ampere (.ordinary (.write base (payload value)))),.base (.ampere (.ordinary (.read base (payload reply))))]
}
def candidate (value reply : Nat) : Unified.Candidate := ⟨[trace value reply]⟩
def initial : Location → Symbolic.Byte := fun _ => .bits (byte 0)
def launch (value : Nat) : Scalar.Launch := ⟨⟨.one,.one⟩,params value,initial⟩
def writerControl : Unified.ControlNode := .base (.source writer)
def readerControl : Unified.ControlNode := .base (.source reader)
def writerMemory : Unified.Node := .base (.tma (.source writer))
def readerMemory : Unified.Node := .base (.tma (.source reader))
def context (value reply : Nat) : ByteContentsHeap.Context := ⟨.one,candidate value reply,fun _ => []⟩

theorem source_produced (value reply : Nat) : Unified.Produced program (params value) .one (trace value reply) := by rfl

theorem source_complete (value reply : Nat) : Unified.Complete (candidate value reply) := by
  intro actual ht
  have he : actual = trace value reply := by simpa only [candidate,List.mem_singleton] using ht
  subst actual
  exact ⟨rfl,rfl⟩

theorem loaded_register_is_actual_reply (value reply : Nat) :
    declarationLookup "%r" (trace value reply).final.base.scalar.core.thread.regs = some (wrap 32 reply) := by rfl

theorem valid_thread_unique {who : ThreadId} (hv : who.Valid (launch 0).geometry) : who = thread := by
  rcases who with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid,Dim3.Within,launch,Dim3.one] at hv
  have hcx : cx = 0 := by omega
  have hcy : cy = 0 := by omega
  have hcz : cz = 0 := by omega
  have htx : tx = 0 := by omega
  have hty : ty = 0 := by omega
  have htz : tz = 0 := by omega
  subst_vars
  rfl

theorem source_well_formed (value reply : Nat) : Unified.WellFormed program (launch value) (candidate value reply) := by
  refine ⟨by change (⟨.one,.one⟩ : Geometry).Valid; unfold Geometry.Valid Dim3.Positive; decide,?_,?_,?_⟩
  · change ([thread] : List ThreadId).Nodup
    simp
  · intro actual ht
    have he : actual = trace value reply := by simpa only [candidate,List.mem_singleton] using ht
    subst actual
    exact ⟨by change thread.Valid (⟨.one,.one⟩ : Geometry); unfold ThreadId.Valid Dim3.Within thread Dim3.zero Dim3.one; decide,source_produced value reply⟩
  · intro who hv
    have he := valid_thread_unique hv
    subst who
    exact ⟨trace value reply,by simp [candidate],rfl⟩

theorem writer_lookup (value reply : Nat) : (candidate value reply).eventAt writer = some (.base (.ampere (.ordinary (.write base (payload value))))) := by rfl
theorem reader_lookup (value reply : Nat) : (candidate value reply).eventAt reader = some (.base (.ampere (.ordinary (.read base (payload reply))))) := by rfl
theorem writer_view (value reply : Nat) : (candidate value reply).view.eventAt writer = some (.ampere (.ordinary (.write base (payload value)))) := by rfl
theorem reader_view (value reply : Nat) : (candidate value reply).view.eventAt reader = some (.ampere (.ordinary (.read base (payload reply)))) := by rfl

theorem source_event_shape {value reply id event} (he : (candidate value reply).eventAt id = some event) :
    (id = writer ∧ event = .base (.ampere (.ordinary (.write base (payload value))))) ∨
    (id = reader ∧ event = .base (.ampere (.ordinary (.read base (payload reply))))) := by
  obtain ⟨actual,ht,htid,hindex⟩ := Unified.eventAt_trace he
  have heq : actual = trace value reply := by simpa only [candidate,List.mem_singleton] using ht
  subst actual
  have hbound := (List.getElem?_eq_some_iff.mp hindex).1
  have hb : id.serial < 2 := by simpa only [trace,List.length_cons,List.length_nil] using hbound
  by_cases hz : id.serial = 0
  · have hid : id = writer := by cases id; simp_all [writer,trace]
    subst id
    exact .inl ⟨rfl,(Option.some.inj ((writer_lookup value reply).symm.trans he)).symm⟩
  · have ho : id.serial = 1 := by omega
    have hid : id = reader := by cases id; simp_all [reader,trace]
    subst id
    exact .inr ⟨rfl,(Option.some.inj ((reader_lookup value reply).symm.trans he)).symm⟩

theorem written_and_read_payloads_match (value : Nat) (loc : Location) :
    ByteContents.readByte (candidate value value) readerMemory loc = ByteContents.writeByte (candidate value value) writerMemory loc := by rfl

end
end Ptx.Kernels.ByteValuePipeline
