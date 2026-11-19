import Experiments.WholeFunction.BinaryCopy
import Experiments.WholeFunction.StrncpyBinary

/-! Actual binary inputs for frame derivation. The fixtures contain decoded
rows only; slot counts, saved-register maps, and gaps are derived by the
frame frontend rather than supplied as semantic assumptions. -/
namespace Xv6.WholeFunction.FrameDerive.Fixtures
open MachCSL Binary
noncomputable section
set_option maxHeartbeats 0

def strncpyPush : Row := Binary.strncpy_000
def strncpySaveRows : List Row := Binary.strncpy.rows.drop 1 |>.take 3
def strncpyReturnRows : List Row := Binary.strncpy.rows.drop 23 |>.take 4

def copyinPush : Row := Binary.copyin_002
def copyinSaveRows : List Row := Binary.copyin.rows.drop 2 |>.take 13
def copyinReturnRows : List Row := Binary.copyin.rows.drop 51 |>.take 14

def copyoutPush : Row := Binary.copyout_002
def copyoutSaveRows : List Row := Binary.copyout.rows.drop 2 |>.take 14
def copyoutReturnRows : List Row := Binary.copyout.rows.drop 66 |>.take 15

/- Consoleread has eight saves in twelve allocated slots. Its unused slot
between s4 and s6 is deliberate: s5 is spilled later in the body. -/
def consoleread_000 : Row := rowAt 0x8000017a#64 (by binary_rfl) (by binary_rfl)
def consoleread_002 : Row := rowAt 0x8000017c#64 (by binary_rfl) (by binary_rfl)
def consoleread_004 : Row := rowAt 0x8000017e#64 (by binary_rfl) (by binary_rfl)
def consoleread_006 : Row := rowAt 0x80000180#64 (by binary_rfl) (by binary_rfl)
def consoleread_008 : Row := rowAt 0x80000182#64 (by binary_rfl) (by binary_rfl)
def consoleread_00a : Row := rowAt 0x80000184#64 (by binary_rfl) (by binary_rfl)
def consoleread_00c : Row := rowAt 0x80000186#64 (by binary_rfl) (by binary_rfl)
def consoleread_00e : Row := rowAt 0x80000188#64 (by binary_rfl) (by binary_rfl)
def consoleread_010 : Row := rowAt 0x8000018a#64 (by binary_rfl) (by binary_rfl)
def consoleread_012 : Row := rowAt 0x8000018c#64 (by binary_rfl) (by binary_rfl)
def consoleread_0ce : Row := rowAt 0x80000248#64 (by binary_rfl) (by binary_rfl)
def consoleread_0d0 : Row := rowAt 0x8000024a#64 (by binary_rfl) (by binary_rfl)
def consoleread_0d2 : Row := rowAt 0x8000024c#64 (by binary_rfl) (by binary_rfl)
def consoleread_0d4 : Row := rowAt 0x8000024e#64 (by binary_rfl) (by binary_rfl)
def consoleread_0d6 : Row := rowAt 0x80000250#64 (by binary_rfl) (by binary_rfl)
def consoleread_0d8 : Row := rowAt 0x80000252#64 (by binary_rfl) (by binary_rfl)
def consoleread_0da : Row := rowAt 0x80000254#64 (by binary_rfl) (by binary_rfl)
def consoleread_0dc : Row := rowAt 0x80000256#64 (by binary_rfl) (by binary_rfl)
def consoleread_0de : Row := rowAt 0x80000258#64 (by binary_rfl) (by binary_rfl)
def consoleread_0e0 : Row := rowAt 0x8000025a#64 (by binary_rfl) (by binary_rfl)

def consolereadPush : Row := consoleread_000
def consolereadSaveRows : List Row :=
  [consoleread_002, consoleread_004, consoleread_006, consoleread_008,
   consoleread_00a, consoleread_00c, consoleread_00e, consoleread_010, consoleread_012]
def consolereadReturnRows : List Row :=
  [consoleread_0ce, consoleread_0d0, consoleread_0d2, consoleread_0d4,
   consoleread_0d6, consoleread_0d8, consoleread_0da, consoleread_0dc,
   consoleread_0de, consoleread_0e0]

/- Kexec allocates 68 slots but initially saves only four registers. Its
word saves/loads are uncompressed; frame-pointer setup and RET are compressed. -/
def kexec_000 : Row := rowAt 0x80004970#64 (by binary_rfl) (by binary_rfl)
def kexec_004 : Row := rowAt 0x80004974#64 (by binary_rfl) (by binary_rfl)
def kexec_008 : Row := rowAt 0x80004978#64 (by binary_rfl) (by binary_rfl)
def kexec_00c : Row := rowAt 0x8000497c#64 (by binary_rfl) (by binary_rfl)
def kexec_010 : Row := rowAt 0x80004980#64 (by binary_rfl) (by binary_rfl)
def kexec_014 : Row := rowAt 0x80004984#64 (by binary_rfl) (by binary_rfl)
def kexec_072 : Row := rowAt 0x800049e2#64 (by binary_rfl) (by binary_rfl)
def kexec_076 : Row := rowAt 0x800049e6#64 (by binary_rfl) (by binary_rfl)
def kexec_07a : Row := rowAt 0x800049ea#64 (by binary_rfl) (by binary_rfl)
def kexec_07e : Row := rowAt 0x800049ee#64 (by binary_rfl) (by binary_rfl)
def kexec_082 : Row := rowAt 0x800049f2#64 (by binary_rfl) (by binary_rfl)
def kexec_086 : Row := rowAt 0x800049f6#64 (by binary_rfl) (by binary_rfl)

def kexecPush : Row := kexec_000
def kexecSaveRows : List Row :=
  [kexec_004, kexec_008, kexec_00c, kexec_010, kexec_014]
def kexecReturnRows : List Row :=
  [kexec_072, kexec_076, kexec_07a, kexec_07e, kexec_082, kexec_086]

end
end Xv6.WholeFunction.FrameDerive.Fixtures
