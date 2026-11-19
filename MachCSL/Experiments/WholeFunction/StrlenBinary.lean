import Experiments.WholeFunction.Binary

/-! Exact, kernel-checked STRLEN rows from the unchanged xv6 image. -/
namespace Xv6.WholeFunction.Binary
open MachCSL
noncomputable section
set_option maxHeartbeats 0

def strlen_000 : Row := rowAt 0x80000ea2#64 (by binary_rfl) (by binary_rfl)
def strlen_002 : Row := rowAt 0x80000ea4#64 (by binary_rfl) (by binary_rfl)
def strlen_004 : Row := rowAt 0x80000ea6#64 (by binary_rfl) (by binary_rfl)
def strlen_006 : Row := rowAt 0x80000ea8#64 (by binary_rfl) (by binary_rfl)
def strlen_008 : Row := rowAt 0x80000eaa#64 (by binary_rfl) (by binary_rfl)
def strlen_00c : Row := rowAt 0x80000eae#64 (by binary_rfl) (by binary_rfl)
def strlen_00e : Row := rowAt 0x80000eb0#64 (by binary_rfl) (by binary_rfl)
def strlen_012 : Row := rowAt 0x80000eb4#64 (by binary_rfl) (by binary_rfl)
def strlen_014 : Row := rowAt 0x80000eb6#64 (by binary_rfl) (by binary_rfl)
def strlen_016 : Row := rowAt 0x80000eb8#64 (by binary_rfl) (by binary_rfl)
def strlen_01a : Row := rowAt 0x80000ebc#64 (by binary_rfl) (by binary_rfl)
def strlen_01c : Row := rowAt 0x80000ebe#64 (by binary_rfl) (by binary_rfl)
def strlen_020 : Row := rowAt 0x80000ec2#64 (by binary_rfl) (by binary_rfl)
def strlen_022 : Row := rowAt 0x80000ec4#64 (by binary_rfl) (by binary_rfl)
def strlen_024 : Row := rowAt 0x80000ec6#64 (by binary_rfl) (by binary_rfl)
def strlen_026 : Row := rowAt 0x80000ec8#64 (by binary_rfl) (by binary_rfl)
def strlen_028 : Row := rowAt 0x80000eca#64 (by binary_rfl) (by binary_rfl)
def strlen_02a : Row := rowAt 0x80000ecc#64 (by binary_rfl) (by binary_rfl)

def strlen : Function where
  entry := KA.«strlen»
  finish := 0x80000ece#64
  rows := [strlen_000, strlen_002, strlen_004, strlen_006, strlen_008, strlen_00c, strlen_00e, strlen_012, strlen_014, strlen_016, strlen_01a, strlen_01c, strlen_020, strlen_022, strlen_024, strlen_026, strlen_028, strlen_02a]
  covers := by binary_rfl
  localEdges := by binary_rfl

end
end Xv6.WholeFunction.Binary
