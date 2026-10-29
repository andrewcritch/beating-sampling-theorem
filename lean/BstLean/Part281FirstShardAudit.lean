import BstLean.Part281PilotAudit
import BstLean.Part281FamilyShard1

/-! Guarded axiom audit for the Part 281 proof chain. -/

/-- info: 'BstLean.Part281.frameShard1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part281.frameShard1

/-- info: 'BstLean.Part281.rowShard1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part281.rowShard1

/-- info: 'BstLean.Part281.classifierShard1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part281.classifierShard1

