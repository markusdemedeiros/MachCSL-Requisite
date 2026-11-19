import Experiments.WholeFunction.BinaryCopy

namespace Xv6.WholeFunction.Binary
open MachCSL Iris BI
set_option maxHeartbeats 0

-- The entry's zero-length path is part of the checked graph.
example : copyin_000.flow = .branch 0x80001720#64 0x8000168a#64 := by binary_rfl

-- Removing the entry is rejected by byte coverage.
example : contiguous copyin.entry copyin.finish copyin.rows.tail = false := by binary_rfl

-- Removing the shared target of the two backwards branches is rejected.
example : closed (copyin.rows.filter (fun r => r.pc != 0x800016b8#64)) = false := by
  binary_rfl

-- Mid-instruction addresses do not acquire code certificates.
example : (copyin.fetch? 0x80001689#64).isNone = true := by binary_rfl

-- Compiler clients need only PC lookup; they do not provide instruction ASTs.
example {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] :
    kernelText (GF := GF) ⊢ instr 0x800016e2#64 copyin_05a.rvc copyin_05a.code :=
  copyin.fetch_instr _ _ (by binary_rfl)

#print axioms copyout
#print axioms copyin
#print axioms copyinstr

end Xv6.WholeFunction.Binary
