import Experiments.WholeFunction.Binary

namespace Xv6.WholeFunction.Binary
open MachCSL
noncomputable section
set_option maxHeartbeats 0

def strncpy_000 : Row := rowAt 0x80000e26#64 (by binary_rfl) (by binary_rfl)
def strncpy_002 : Row := rowAt 0x80000e28#64 (by binary_rfl) (by binary_rfl)
def strncpy_004 : Row := rowAt 0x80000e2a#64 (by binary_rfl) (by binary_rfl)
def strncpy_006 : Row := rowAt 0x80000e2c#64 (by binary_rfl) (by binary_rfl)
def strncpy_008 : Row := rowAt 0x80000e2e#64 (by binary_rfl) (by binary_rfl)
def strncpy_00a : Row := rowAt 0x80000e30#64 (by binary_rfl) (by binary_rfl)
def strncpy_00c : Row := rowAt 0x80000e32#64 (by binary_rfl) (by binary_rfl)
def strncpy_00e : Row := rowAt 0x80000e34#64 (by binary_rfl) (by binary_rfl)
def strncpy_012 : Row := rowAt 0x80000e38#64 (by binary_rfl) (by binary_rfl)
def strncpy_016 : Row := rowAt 0x80000e3c#64 (by binary_rfl) (by binary_rfl)
def strncpy_018 : Row := rowAt 0x80000e3e#64 (by binary_rfl) (by binary_rfl)
def strncpy_01a : Row := rowAt 0x80000e40#64 (by binary_rfl) (by binary_rfl)
def strncpy_01e : Row := rowAt 0x80000e44#64 (by binary_rfl) (by binary_rfl)
def strncpy_022 : Row := rowAt 0x80000e48#64 (by binary_rfl) (by binary_rfl)
def strncpy_024 : Row := rowAt 0x80000e4a#64 (by binary_rfl) (by binary_rfl)
def strncpy_026 : Row := rowAt 0x80000e4c#64 (by binary_rfl) (by binary_rfl)
def strncpy_028 : Row := rowAt 0x80000e4e#64 (by binary_rfl) (by binary_rfl)
def strncpy_02c : Row := rowAt 0x80000e52#64 (by binary_rfl) (by binary_rfl)
def strncpy_02e : Row := rowAt 0x80000e54#64 (by binary_rfl) (by binary_rfl)
def strncpy_030 : Row := rowAt 0x80000e56#64 (by binary_rfl) (by binary_rfl)
def strncpy_032 : Row := rowAt 0x80000e58#64 (by binary_rfl) (by binary_rfl)
def strncpy_036 : Row := rowAt 0x80000e5c#64 (by binary_rfl) (by binary_rfl)
def strncpy_03a : Row := rowAt 0x80000e60#64 (by binary_rfl) (by binary_rfl)
def strncpy_03e : Row := rowAt 0x80000e64#64 (by binary_rfl) (by binary_rfl)
def strncpy_040 : Row := rowAt 0x80000e66#64 (by binary_rfl) (by binary_rfl)
def strncpy_042 : Row := rowAt 0x80000e68#64 (by binary_rfl) (by binary_rfl)
def strncpy_044 : Row := rowAt 0x80000e6a#64 (by binary_rfl) (by binary_rfl)

def strncpy : Function where
  entry := KA.«strncpy»
  finish := KA.«safestrcpy»
  rows := [strncpy_000, strncpy_002, strncpy_004, strncpy_006, strncpy_008, strncpy_00a, strncpy_00c, strncpy_00e, strncpy_012, strncpy_016, strncpy_018, strncpy_01a, strncpy_01e, strncpy_022, strncpy_024, strncpy_026, strncpy_028, strncpy_02c, strncpy_02e, strncpy_030, strncpy_032, strncpy_036, strncpy_03a, strncpy_03e, strncpy_040, strncpy_042, strncpy_044]
  covers := by binary_rfl
  localEdges := by binary_rfl

end
end Xv6.WholeFunction.Binary
