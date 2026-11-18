import Req

/- These checks fail if a proof acquires sorryAx or any additional axiom. -/

/-- info: 'Req.wp_requisiteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Req.wp_requisiteness

/-- info: 'Req.wp_requisiteness_nofork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Req.wp_requisiteness_nofork

/-- info: 'Req.HeapLang.base_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Req.HeapLang.base_update

/-- info: 'Req.HeapLang.wp_requisiteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Req.HeapLang.wp_requisiteness

/-- info: 'Req.HeapLang.wp_requisiteness_nopre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Req.HeapLang.wp_requisiteness_nopre

/-- info: 'Req.HeapLang.wp_requisiteness_nofork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Req.HeapLang.wp_requisiteness_nofork
