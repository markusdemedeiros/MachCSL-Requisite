import Experiments.WholeFunction.MemoryModel

namespace Xv6.WholeFunction.Memory
open Iris Iris.BI Iris.ProgramLogic MachCSL LeanRV64D

/-- Only address/value operands independent of hart identity are compiled.
Unsupported instruction shapes fail decoding instead of becoming no-ops. -/
inductive Op where
  | load (imm : BitVec 12) (rd rs : BitVec 5) (base : rs ≠ 4#5) (valid : rdOk rd)
  | store (imm : BitVec 12) (rs rt : BitVec 5) (base : rs ≠ 4#5) (value : rt ≠ 4#5)

def Op.code : Op → instruction
  | .load imm rd rs _ _ => .LOAD (imm, .Regidx rs, .Regidx rd, true, 1)
  | .store imm rs rt _ _ => .STORE (imm, .Regidx rt, .Regidx rs, 1)

def Op.decode (i : instruction) : Option {op : Op // i = op.code} :=
  match i with
  | .LOAD (imm, .Regidx rs, .Regidx rd, true, 1) =>
    if h : rs ≠ 4#5 then
      if hr : rdOk rd then some ⟨.load imm rd rs h hr, rfl⟩ else none
    else none
  | .STORE (imm, .Regidx rt, .Regidx rs, 1) =>
    if h : rs ≠ 4#5 then
      if ht : rt ≠ 4#5 then some ⟨.store imm rs rt h ht, rfl⟩ else none
    else none
  | _ => none

def canonical : CPU := ⟨0, by decide⟩

theorem rget_independent (cpu cpu' : CPU) (k : KCtx) (r : BitVec 5) (free : r ≠ 4#5) :
    k.rget cpu r = k.rget cpu' r := by
  by_cases zero : r = 0#5
  · subst r; simp
  · rw [KCtx.rget_ne cpu k r zero free, KCtx.rget_ne cpu' k r zero free]

def Op.address (op : Op) (k : KCtx) : BitVec 64 :=
  match op with
  | .load imm _ rs _ _ | .store imm rs _ _ _ => k.rget canonical rs + imm.signExtend 64

def Op.canAccess (op : Op) (buffer : Buffer) : Prop :=
  match op with
  | .load .. => True
  | .store .. => buffer.fraction = DFrac.own 1

def Op.Enabled (op : Op) (a : Access) (s : State) : Prop :=
  ∃ buffer byte, s.buffers[a.buffer]? = some buffer ∧ buffer.bytes[a.index]? = some byte ∧
    op.address s.machine.ctx = buffer.base + BitVec.ofNat 64 a.index ∧ op.canAccess buffer

def Op.run (op : Op) (rvc : Bool) (cpu : CPU) (a : Access) (s : State)
    (buffer : Buffer) (byte : BitVec 8) : State :=
  match op with
  | .load _ rd _ _ _ =>
    ⟨⟨s.machine.ctx.setReg rd (byte.setWidth 64), s.machine.pc + instrLen rvc, s.machine.cells⟩, s.buffers⟩
  | .store _ _ rt _ _ =>
    ⟨⟨s.machine.ctx, s.machine.pc + instrLen rvc, s.machine.cells⟩,
      s.buffers.set a.buffer {buffer with bytes := (buffer.bytes.set a.index
        (BitVec.extractLsb' 0 8 (s.machine.ctx.rget cpu rt)))}⟩

def Op.Next (op : Op) (rvc : Bool) (cpu : CPU) (a : Access) (s t : State) : Prop :=
  ∃ buffer byte, s.buffers[a.buffer]? = some buffer ∧ buffer.bytes[a.index]? = some byte ∧
    t = op.run rvc cpu a s buffer byte

theorem Op.next_indices (op : Op) (rvc : Bool) (cpu : CPU) (a : Access) (s t : State)
    (hn : op.Next rvc cpu a s t) :
    t.machine.ctx.sie = s.machine.ctx.sie ∧ t.machine.ctx.proc = s.machine.ctx.proc := by
  obtain ⟨buffer, byte, _, _, rfl⟩ := hn
  cases op <;> simp [Op.run]

theorem Op.next_cells (op : Op) (rvc : Bool) (cpu : CPU) (a : Access) (s t : State)
    (hn : op.Next rvc cpu a s t) : t.machine.cells = s.machine.cells := by
  obtain ⟨buffer, byte, _, _, rfl⟩ := hn
  cases op <;> rfl

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [CurCtx] [KernelGeom] [KernelImage GF]

/-- Buffer selection, byte splitting and reassembly are shared by every
client. The later comes from the actual Sail-derived byte instruction rule. -/
theorem Op.sound (op : Op) (rvc : Bool) (a : Access) (cpu : CPU) (s : State)
    (enabled : op.Enabled a s) :
    instr (GF := GF) s.machine.pc rvc op.code ∗ kctx cpu s.machine.ctx ∗ pcIs cpu s.machine.pc ∗
    owns s.buffers ∗ ▷ wpNext s.machine.ctx.sie s.machine.ctx.proc cpu (fun cpu' => iprop(
      ∀ t, ⌜op.Next rvc cpu' a s t⌝ -∗
        kctx cpu' t.machine.ctx -∗ pcIs cpu' t.machine.pc -∗ owns t.buffers -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  obtain ⟨buffer, byte, found, lookup, address, permission⟩ := enabled
  cases op with
  | load imm rd rs base valid =>
    simp only [Op.code]
    change s.machine.ctx.rget canonical rs + imm.signExtend 64 = _ at address
    have atCpu : s.machine.ctx.rget cpu rs + imm.signExtend 64 =
        buffer.base + BitVec.ofNat 64 a.index := by
      rw [rget_independent cpu canonical s.machine.ctx rs base]
      exact address
    iintro ⟨HI, HK, HPC, Hbuffers, Hnext⟩
    icases buffer_read s.buffers a.buffer buffer found $$ Hbuffers with ⟨Hbuffer, Hbuffers⟩
    irevert Hbuffer
    unfold Buffer.owns
    iintro Hbuffer
    icases byteBuf_acc buffer.base buffer.fraction buffer.bytes a.index byte lookup $$ Hbuffer
      with ⟨Hbyte, Hbuffer⟩
    iapply wp_s_lbu cpu s.machine.ctx s.machine.pc rvc imm rd rs base valid buffer.fraction byte
      $$ [$HI $HK $HPC Hbyte Hbuffer Hbuffers Hnext]
    rw [atCpu]
    iframe Hbyte
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %pin HK HPC Hbyte
    ihave Hbuffer := Hbuffer $$ Hbyte
    ihave Hbuffers := Hbuffers $$ Hbuffer
    ihave Hnext := wpNext_at _ _ _ cpu' _ pin $$ Hnext
    ihave Hnext := Hnext $$ %((Op.load imm rd rs base valid).run rvc cpu' a s buffer byte)
      %(⟨buffer, byte, found, lookup, rfl⟩)
    dsimp only [Op.run]
    iapply Hnext $$ HK HPC Hbuffers
  | store imm rs rt base value =>
    simp only [Op.code]
    change s.machine.ctx.rget canonical rs + imm.signExtend 64 = _ at address
    change buffer.fraction = DFrac.own 1 at permission
    have atCpu : s.machine.ctx.rget cpu rs + imm.signExtend 64 =
        buffer.base + BitVec.ofNat 64 a.index := by
      rw [rget_independent cpu canonical s.machine.ctx rs base]
      exact address
    iintro ⟨HI, HK, HPC, Hbuffers, Hnext⟩
    icases buffer_update s.buffers a.buffer buffer found $$ Hbuffers with ⟨Hbuffer, Hbuffers⟩
    irevert Hbuffer
    unfold Buffer.owns
    rw [permission]
    iintro Hbuffer
    icases byteBuf_upd buffer.base buffer.bytes a.index byte lookup $$ Hbuffer with ⟨Hbyte, Hbuffer⟩
    iapply wp_s_sb cpu s.machine.ctx s.machine.pc rvc imm rs rt base byte
      $$ [$HI $HK $HPC Hbyte Hbuffer Hbuffers Hnext]
    rw [atCpu]
    iframe Hbyte
    inext
    iapply wpNext_intro_pin
    iintro %cpu' %pin HK HPC Hbyte
    ihave Hbuffer := Hbuffer $$ %(BitVec.extractLsb' 0 8 (s.machine.ctx.rget cpu' rt)) Hbyte
    have hf : ({buffer with bytes := (buffer.bytes.set a.index
        (BitVec.extractLsb' 0 8 (s.machine.ctx.rget cpu' rt)))}).fraction = DFrac.own 1 := permission
    ihave Hbuffers := Hbuffers $$ %({buffer with bytes := (buffer.bytes.set a.index
      (BitVec.extractLsb' 0 8 (s.machine.ctx.rget cpu' rt)))}) [Hbuffer]
    · dsimp only
      rw [permission]
      iexact Hbuffer
    ihave Hnext := wpNext_at _ _ _ cpu' _ pin $$ Hnext
    ihave Hnext := Hnext $$ %((Op.store imm rs rt base value).run rvc cpu' a s buffer byte)
      %(⟨buffer, byte, found, lookup, rfl⟩)
    dsimp only [Op.run]
    iapply Hnext $$ HK HPC Hbuffers

end Xv6.WholeFunction.Memory
