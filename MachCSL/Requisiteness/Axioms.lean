import MachCSL.RequisiteAdequacy

/-! Kernel axiom checks for the requisiteness and integration proofs. -/
open Classical

/-- info: 'MachCSL.ExactState.agree' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.ExactState.agree

/-- info: 'MachCSL.ExactState.update' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.ExactState.update

/-- info: 'MachCSL.Requisite.stateSimulation' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.Requisite.stateSimulation

/-- info: 'MachCSL.Requisite.wp_requisiteness' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.Requisite.wp_requisiteness

/-- info: 'MachCSL.Requisite.state_alloc' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.Requisite.state_alloc

/-- info: 'MachCSL.Requisite.wp_alloc_requisiteness' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.Requisite.wp_alloc_requisiteness

/-- info: 'MachCSL.Requisite.wp_adequacy' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.Requisite.wp_adequacy

/-- info: 'MachCSL.Requisite.adequate_iff_wp' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.Requisite.adequate_iff_wp

/-- info: 'MachCSL.resourceInterp_acc' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.resourceInterp_acc

/-- info: 'MachCSL.wp_lift_resource' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms MachCSL.wp_lift_resource
