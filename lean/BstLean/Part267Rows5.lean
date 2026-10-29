import BstLean.Part267Bridge
import BstLean.Part264bFamily
import BstLean.Part261Coverage
import BstLean.Part262ActualCoverage

namespace BstLean.Part267
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part192 BstLean.Part196

theorem energy12326 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12326.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12326, BstLean.Part263.cell12326]

noncomputable def root12326 (t : ℝ) (c : Ret 12326)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12326 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12326) :
    BstLean.Part243.RootInputs 12326 t c BstLean.Part259.agent12326.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12326
    BstLean.Part264b.N12326.sourceNumerics12326
    (by norm_num [BstLean.Part263.scalarRow12326])
    (by norm_num [BstLean.Part263.scalarRow12326])
    (by norm_num [BstLean.Part263.scalarRow12326])
    energy12326 BstLean.Part262.actualCertificate12326 t c hw hc

noncomputable def master12326 :
    MasterCertificate 12326 (BstLean.Part260.worldParameters 12326) BstLean.Part259.agent12326 := by
  rw [BstLean.Part260.parameters12326]
  exact BstLean.Part261.master12326

theorem compatible12326 : BstLean.Part259.agent12326.charge ≤ master12326.retainedCharge := by
  change BstLean.Part259.agent12326.charge ≤ BstLean.Part261.master12326.retainedCharge
  rw [show BstLean.Part261.master12326.retainedCharge =
    BstLean.Part259.scalar12326.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12326]
  norm_num [BstLean.Part259.agent12326, BstLean.Part259.scalar12326]

noncomputable def row12326 : BstLean.Part259.RowInputs 12326 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12326
    master12326 BstLean.Part262.actualCertificate12326
    BstLean.Part264b.N12326.covarianceEvent12326
    (BstLean.Part263.cell BstLean.Part263.scalarRow12326.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12326)
    BstLean.Part264b.N12326.covarianceEvent12326_measurable BstLean.Part264b.N12326.covarianceEvent12326_payment
    BstLean.Part264b.N12326.frame12326 (fun t c hw hc => ⟨root12326 t c hw hc⟩)
    BstLean.Part262.allocation12326 compatible12326

theorem energy12327 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12327.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12327, BstLean.Part263.cell12327]

noncomputable def root12327 (t : ℝ) (c : Ret 12327)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12327 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12327) :
    BstLean.Part243.RootInputs 12327 t c BstLean.Part259.agent12327.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12327
    BstLean.Part264b.N12327.sourceNumerics12327
    (by norm_num [BstLean.Part263.scalarRow12327])
    (by norm_num [BstLean.Part263.scalarRow12327])
    (by norm_num [BstLean.Part263.scalarRow12327])
    energy12327 BstLean.Part262.actualCertificate12327 t c hw hc

noncomputable def master12327 :
    MasterCertificate 12327 (BstLean.Part260.worldParameters 12327) BstLean.Part259.agent12327 := by
  rw [BstLean.Part260.parameters12327]
  exact BstLean.Part261.master12327

theorem compatible12327 : BstLean.Part259.agent12327.charge ≤ master12327.retainedCharge := by
  change BstLean.Part259.agent12327.charge ≤ BstLean.Part261.master12327.retainedCharge
  rw [show BstLean.Part261.master12327.retainedCharge =
    BstLean.Part259.scalar12327.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12327]
  norm_num [BstLean.Part259.agent12327, BstLean.Part259.scalar12327]

noncomputable def row12327 : BstLean.Part259.RowInputs 12327 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12327
    master12327 BstLean.Part262.actualCertificate12327
    BstLean.Part264b.N12327.covarianceEvent12327
    (BstLean.Part263.cell BstLean.Part263.scalarRow12327.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12327)
    BstLean.Part264b.N12327.covarianceEvent12327_measurable BstLean.Part264b.N12327.covarianceEvent12327_payment
    BstLean.Part264b.N12327.frame12327 (fun t c hw hc => ⟨root12327 t c hw hc⟩)
    BstLean.Part262.allocation12327 compatible12327

theorem energy12328 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12328.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12328, BstLean.Part263.cell12328]

noncomputable def root12328 (t : ℝ) (c : Ret 12328)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12328 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12328) :
    BstLean.Part243.RootInputs 12328 t c BstLean.Part259.agent12328.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12328
    BstLean.Part264b.N12328.sourceNumerics12328
    (by norm_num [BstLean.Part263.scalarRow12328])
    (by norm_num [BstLean.Part263.scalarRow12328])
    (by norm_num [BstLean.Part263.scalarRow12328])
    energy12328 BstLean.Part262.actualCertificate12328 t c hw hc

noncomputable def master12328 :
    MasterCertificate 12328 (BstLean.Part260.worldParameters 12328) BstLean.Part259.agent12328 := by
  rw [BstLean.Part260.parameters12328]
  exact BstLean.Part261.master12328

theorem compatible12328 : BstLean.Part259.agent12328.charge ≤ master12328.retainedCharge := by
  change BstLean.Part259.agent12328.charge ≤ BstLean.Part261.master12328.retainedCharge
  rw [show BstLean.Part261.master12328.retainedCharge =
    BstLean.Part259.scalar12328.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12328]
  norm_num [BstLean.Part259.agent12328, BstLean.Part259.scalar12328]

noncomputable def row12328 : BstLean.Part259.RowInputs 12328 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12328
    master12328 BstLean.Part262.actualCertificate12328
    BstLean.Part264b.N12328.covarianceEvent12328
    (BstLean.Part263.cell BstLean.Part263.scalarRow12328.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12328)
    BstLean.Part264b.N12328.covarianceEvent12328_measurable BstLean.Part264b.N12328.covarianceEvent12328_payment
    BstLean.Part264b.N12328.frame12328 (fun t c hw hc => ⟨root12328 t c hw hc⟩)
    BstLean.Part262.allocation12328 compatible12328

theorem energy12329 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12329.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12329, BstLean.Part263.cell12329]

noncomputable def root12329 (t : ℝ) (c : Ret 12329)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12329 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12329) :
    BstLean.Part243.RootInputs 12329 t c BstLean.Part259.agent12329.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12329
    BstLean.Part264b.N12329.sourceNumerics12329
    (by norm_num [BstLean.Part263.scalarRow12329])
    (by norm_num [BstLean.Part263.scalarRow12329])
    (by norm_num [BstLean.Part263.scalarRow12329])
    energy12329 BstLean.Part262.actualCertificate12329 t c hw hc

noncomputable def master12329 :
    MasterCertificate 12329 (BstLean.Part260.worldParameters 12329) BstLean.Part259.agent12329 := by
  rw [BstLean.Part260.parameters12329]
  exact BstLean.Part261.master12329

theorem compatible12329 : BstLean.Part259.agent12329.charge ≤ master12329.retainedCharge := by
  change BstLean.Part259.agent12329.charge ≤ BstLean.Part261.master12329.retainedCharge
  rw [show BstLean.Part261.master12329.retainedCharge =
    BstLean.Part259.scalar12329.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12329]
  norm_num [BstLean.Part259.agent12329, BstLean.Part259.scalar12329]

noncomputable def row12329 : BstLean.Part259.RowInputs 12329 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12329
    master12329 BstLean.Part262.actualCertificate12329
    BstLean.Part264b.N12329.covarianceEvent12329
    (BstLean.Part263.cell BstLean.Part263.scalarRow12329.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12329)
    BstLean.Part264b.N12329.covarianceEvent12329_measurable BstLean.Part264b.N12329.covarianceEvent12329_payment
    BstLean.Part264b.N12329.frame12329 (fun t c hw hc => ⟨root12329 t c hw hc⟩)
    BstLean.Part262.allocation12329 compatible12329

theorem energy12330 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12330.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12330, BstLean.Part263.cell12330]

noncomputable def root12330 (t : ℝ) (c : Ret 12330)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12330 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12330) :
    BstLean.Part243.RootInputs 12330 t c BstLean.Part259.agent12330.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12330
    BstLean.Part264b.N12330.sourceNumerics12330
    (by norm_num [BstLean.Part263.scalarRow12330])
    (by norm_num [BstLean.Part263.scalarRow12330])
    (by norm_num [BstLean.Part263.scalarRow12330])
    energy12330 BstLean.Part262.actualCertificate12330 t c hw hc

noncomputable def master12330 :
    MasterCertificate 12330 (BstLean.Part260.worldParameters 12330) BstLean.Part259.agent12330 := by
  rw [BstLean.Part260.parameters12330]
  exact BstLean.Part261.master12330

theorem compatible12330 : BstLean.Part259.agent12330.charge ≤ master12330.retainedCharge := by
  change BstLean.Part259.agent12330.charge ≤ BstLean.Part261.master12330.retainedCharge
  rw [show BstLean.Part261.master12330.retainedCharge =
    BstLean.Part259.scalar12330.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12330]
  norm_num [BstLean.Part259.agent12330, BstLean.Part259.scalar12330]

noncomputable def row12330 : BstLean.Part259.RowInputs 12330 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12330
    master12330 BstLean.Part262.actualCertificate12330
    BstLean.Part264b.N12330.covarianceEvent12330
    (BstLean.Part263.cell BstLean.Part263.scalarRow12330.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12330)
    BstLean.Part264b.N12330.covarianceEvent12330_measurable BstLean.Part264b.N12330.covarianceEvent12330_payment
    BstLean.Part264b.N12330.frame12330 (fun t c hw hc => ⟨root12330 t c hw hc⟩)
    BstLean.Part262.allocation12330 compatible12330

theorem energy12331 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12331.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12331, BstLean.Part263.cell12331]

noncomputable def root12331 (t : ℝ) (c : Ret 12331)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12331 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12331) :
    BstLean.Part243.RootInputs 12331 t c BstLean.Part259.agent12331.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12331
    BstLean.Part264b.N12331.sourceNumerics12331
    (by norm_num [BstLean.Part263.scalarRow12331])
    (by norm_num [BstLean.Part263.scalarRow12331])
    (by norm_num [BstLean.Part263.scalarRow12331])
    energy12331 BstLean.Part262.actualCertificate12331 t c hw hc

noncomputable def master12331 :
    MasterCertificate 12331 (BstLean.Part260.worldParameters 12331) BstLean.Part259.agent12331 := by
  rw [BstLean.Part260.parameters12331]
  exact BstLean.Part261.master12331

theorem compatible12331 : BstLean.Part259.agent12331.charge ≤ master12331.retainedCharge := by
  change BstLean.Part259.agent12331.charge ≤ BstLean.Part261.master12331.retainedCharge
  rw [show BstLean.Part261.master12331.retainedCharge =
    BstLean.Part259.scalar12331.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12331]
  norm_num [BstLean.Part259.agent12331, BstLean.Part259.scalar12331]

noncomputable def row12331 : BstLean.Part259.RowInputs 12331 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12331
    master12331 BstLean.Part262.actualCertificate12331
    BstLean.Part264b.N12331.covarianceEvent12331
    (BstLean.Part263.cell BstLean.Part263.scalarRow12331.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12331)
    BstLean.Part264b.N12331.covarianceEvent12331_measurable BstLean.Part264b.N12331.covarianceEvent12331_payment
    BstLean.Part264b.N12331.frame12331 (fun t c hw hc => ⟨root12331 t c hw hc⟩)
    BstLean.Part262.allocation12331 compatible12331

theorem energy12332 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12332.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12332, BstLean.Part263.cell12332]

noncomputable def root12332 (t : ℝ) (c : Ret 12332)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12332 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12332) :
    BstLean.Part243.RootInputs 12332 t c BstLean.Part259.agent12332.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12332
    BstLean.Part264b.N12332.sourceNumerics12332
    (by norm_num [BstLean.Part263.scalarRow12332])
    (by norm_num [BstLean.Part263.scalarRow12332])
    (by norm_num [BstLean.Part263.scalarRow12332])
    energy12332 BstLean.Part262.actualCertificate12332 t c hw hc

noncomputable def master12332 :
    MasterCertificate 12332 (BstLean.Part260.worldParameters 12332) BstLean.Part259.agent12332 := by
  rw [BstLean.Part260.parameters12332]
  exact BstLean.Part261.master12332

theorem compatible12332 : BstLean.Part259.agent12332.charge ≤ master12332.retainedCharge := by
  change BstLean.Part259.agent12332.charge ≤ BstLean.Part261.master12332.retainedCharge
  rw [show BstLean.Part261.master12332.retainedCharge =
    BstLean.Part259.scalar12332.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12332]
  norm_num [BstLean.Part259.agent12332, BstLean.Part259.scalar12332]

noncomputable def row12332 : BstLean.Part259.RowInputs 12332 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12332
    master12332 BstLean.Part262.actualCertificate12332
    BstLean.Part264b.N12332.covarianceEvent12332
    (BstLean.Part263.cell BstLean.Part263.scalarRow12332.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12332)
    BstLean.Part264b.N12332.covarianceEvent12332_measurable BstLean.Part264b.N12332.covarianceEvent12332_payment
    BstLean.Part264b.N12332.frame12332 (fun t c hw hc => ⟨root12332 t c hw hc⟩)
    BstLean.Part262.allocation12332 compatible12332

theorem energy12333 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12333.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12333, BstLean.Part263.cell12333]

noncomputable def root12333 (t : ℝ) (c : Ret 12333)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12333 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12333) :
    BstLean.Part243.RootInputs 12333 t c BstLean.Part259.agent12333.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12333
    BstLean.Part264b.N12333.sourceNumerics12333
    (by norm_num [BstLean.Part263.scalarRow12333])
    (by norm_num [BstLean.Part263.scalarRow12333])
    (by norm_num [BstLean.Part263.scalarRow12333])
    energy12333 BstLean.Part262.actualCertificate12333 t c hw hc

noncomputable def master12333 :
    MasterCertificate 12333 (BstLean.Part260.worldParameters 12333) BstLean.Part259.agent12333 := by
  rw [BstLean.Part260.parameters12333]
  exact BstLean.Part261.master12333

theorem compatible12333 : BstLean.Part259.agent12333.charge ≤ master12333.retainedCharge := by
  change BstLean.Part259.agent12333.charge ≤ BstLean.Part261.master12333.retainedCharge
  rw [show BstLean.Part261.master12333.retainedCharge =
    BstLean.Part259.scalar12333.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12333]
  norm_num [BstLean.Part259.agent12333, BstLean.Part259.scalar12333]

noncomputable def row12333 : BstLean.Part259.RowInputs 12333 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12333
    master12333 BstLean.Part262.actualCertificate12333
    BstLean.Part264b.N12333.covarianceEvent12333
    (BstLean.Part263.cell BstLean.Part263.scalarRow12333.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12333)
    BstLean.Part264b.N12333.covarianceEvent12333_measurable BstLean.Part264b.N12333.covarianceEvent12333_payment
    BstLean.Part264b.N12333.frame12333 (fun t c hw hc => ⟨root12333 t c hw hc⟩)
    BstLean.Part262.allocation12333 compatible12333

theorem energy12334 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12334.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12334, BstLean.Part263.cell12334]

noncomputable def root12334 (t : ℝ) (c : Ret 12334)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12334 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12334) :
    BstLean.Part243.RootInputs 12334 t c BstLean.Part259.agent12334.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12334
    BstLean.Part264b.N12334.sourceNumerics12334
    (by norm_num [BstLean.Part263.scalarRow12334])
    (by norm_num [BstLean.Part263.scalarRow12334])
    (by norm_num [BstLean.Part263.scalarRow12334])
    energy12334 BstLean.Part262.actualCertificate12334 t c hw hc

noncomputable def master12334 :
    MasterCertificate 12334 (BstLean.Part260.worldParameters 12334) BstLean.Part259.agent12334 := by
  rw [BstLean.Part260.parameters12334]
  exact BstLean.Part261.master12334

theorem compatible12334 : BstLean.Part259.agent12334.charge ≤ master12334.retainedCharge := by
  change BstLean.Part259.agent12334.charge ≤ BstLean.Part261.master12334.retainedCharge
  rw [show BstLean.Part261.master12334.retainedCharge =
    BstLean.Part259.scalar12334.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12334]
  norm_num [BstLean.Part259.agent12334, BstLean.Part259.scalar12334]

noncomputable def row12334 : BstLean.Part259.RowInputs 12334 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12334
    master12334 BstLean.Part262.actualCertificate12334
    BstLean.Part264b.N12334.covarianceEvent12334
    (BstLean.Part263.cell BstLean.Part263.scalarRow12334.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12334)
    BstLean.Part264b.N12334.covarianceEvent12334_measurable BstLean.Part264b.N12334.covarianceEvent12334_payment
    BstLean.Part264b.N12334.frame12334 (fun t c hw hc => ⟨root12334 t c hw hc⟩)
    BstLean.Part262.allocation12334 compatible12334

theorem energy12335 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12335.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12335, BstLean.Part263.cell12335]

noncomputable def root12335 (t : ℝ) (c : Ret 12335)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12335 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12335) :
    BstLean.Part243.RootInputs 12335 t c BstLean.Part259.agent12335.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12335
    BstLean.Part264b.N12335.sourceNumerics12335
    (by norm_num [BstLean.Part263.scalarRow12335])
    (by norm_num [BstLean.Part263.scalarRow12335])
    (by norm_num [BstLean.Part263.scalarRow12335])
    energy12335 BstLean.Part262.actualCertificate12335 t c hw hc

noncomputable def master12335 :
    MasterCertificate 12335 (BstLean.Part260.worldParameters 12335) BstLean.Part259.agent12335 := by
  rw [BstLean.Part260.parameters12335]
  exact BstLean.Part261.master12335

theorem compatible12335 : BstLean.Part259.agent12335.charge ≤ master12335.retainedCharge := by
  change BstLean.Part259.agent12335.charge ≤ BstLean.Part261.master12335.retainedCharge
  rw [show BstLean.Part261.master12335.retainedCharge =
    BstLean.Part259.scalar12335.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12335]
  norm_num [BstLean.Part259.agent12335, BstLean.Part259.scalar12335]

noncomputable def row12335 : BstLean.Part259.RowInputs 12335 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12335
    master12335 BstLean.Part262.actualCertificate12335
    BstLean.Part264b.N12335.covarianceEvent12335
    (BstLean.Part263.cell BstLean.Part263.scalarRow12335.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12335)
    BstLean.Part264b.N12335.covarianceEvent12335_measurable BstLean.Part264b.N12335.covarianceEvent12335_payment
    BstLean.Part264b.N12335.frame12335 (fun t c hw hc => ⟨root12335 t c hw hc⟩)
    BstLean.Part262.allocation12335 compatible12335

theorem energy12336 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12336.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12336, BstLean.Part263.cell12336]

noncomputable def root12336 (t : ℝ) (c : Ret 12336)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12336 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12336) :
    BstLean.Part243.RootInputs 12336 t c BstLean.Part259.agent12336.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12336
    BstLean.Part264b.N12336.sourceNumerics12336
    (by norm_num [BstLean.Part263.scalarRow12336])
    (by norm_num [BstLean.Part263.scalarRow12336])
    (by norm_num [BstLean.Part263.scalarRow12336])
    energy12336 BstLean.Part262.actualCertificate12336 t c hw hc

noncomputable def master12336 :
    MasterCertificate 12336 (BstLean.Part260.worldParameters 12336) BstLean.Part259.agent12336 := by
  rw [BstLean.Part260.parameters12336]
  exact BstLean.Part261.master12336

theorem compatible12336 : BstLean.Part259.agent12336.charge ≤ master12336.retainedCharge := by
  change BstLean.Part259.agent12336.charge ≤ BstLean.Part261.master12336.retainedCharge
  rw [show BstLean.Part261.master12336.retainedCharge =
    BstLean.Part259.scalar12336.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12336]
  norm_num [BstLean.Part259.agent12336, BstLean.Part259.scalar12336]

noncomputable def row12336 : BstLean.Part259.RowInputs 12336 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12336
    master12336 BstLean.Part262.actualCertificate12336
    BstLean.Part264b.N12336.covarianceEvent12336
    (BstLean.Part263.cell BstLean.Part263.scalarRow12336.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12336)
    BstLean.Part264b.N12336.covarianceEvent12336_measurable BstLean.Part264b.N12336.covarianceEvent12336_payment
    BstLean.Part264b.N12336.frame12336 (fun t c hw hc => ⟨root12336 t c hw hc⟩)
    BstLean.Part262.allocation12336 compatible12336

theorem energy12337 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12337.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12337, BstLean.Part263.cell12337]

noncomputable def root12337 (t : ℝ) (c : Ret 12337)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12337 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12337) :
    BstLean.Part243.RootInputs 12337 t c BstLean.Part259.agent12337.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12337
    BstLean.Part264b.N12337.sourceNumerics12337
    (by norm_num [BstLean.Part263.scalarRow12337])
    (by norm_num [BstLean.Part263.scalarRow12337])
    (by norm_num [BstLean.Part263.scalarRow12337])
    energy12337 BstLean.Part262.actualCertificate12337 t c hw hc

noncomputable def master12337 :
    MasterCertificate 12337 (BstLean.Part260.worldParameters 12337) BstLean.Part259.agent12337 := by
  rw [BstLean.Part260.parameters12337]
  exact BstLean.Part261.master12337

theorem compatible12337 : BstLean.Part259.agent12337.charge ≤ master12337.retainedCharge := by
  change BstLean.Part259.agent12337.charge ≤ BstLean.Part261.master12337.retainedCharge
  rw [show BstLean.Part261.master12337.retainedCharge =
    BstLean.Part259.scalar12337.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12337]
  norm_num [BstLean.Part259.agent12337, BstLean.Part259.scalar12337]

noncomputable def row12337 : BstLean.Part259.RowInputs 12337 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12337
    master12337 BstLean.Part262.actualCertificate12337
    BstLean.Part264b.N12337.covarianceEvent12337
    (BstLean.Part263.cell BstLean.Part263.scalarRow12337.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12337)
    BstLean.Part264b.N12337.covarianceEvent12337_measurable BstLean.Part264b.N12337.covarianceEvent12337_payment
    BstLean.Part264b.N12337.frame12337 (fun t c hw hc => ⟨root12337 t c hw hc⟩)
    BstLean.Part262.allocation12337 compatible12337

theorem energy12338 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12338.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12338, BstLean.Part263.cell12338]

noncomputable def root12338 (t : ℝ) (c : Ret 12338)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12338 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12338) :
    BstLean.Part243.RootInputs 12338 t c BstLean.Part259.agent12338.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12338
    BstLean.Part264b.N12338.sourceNumerics12338
    (by norm_num [BstLean.Part263.scalarRow12338])
    (by norm_num [BstLean.Part263.scalarRow12338])
    (by norm_num [BstLean.Part263.scalarRow12338])
    energy12338 BstLean.Part262.actualCertificate12338 t c hw hc

noncomputable def master12338 :
    MasterCertificate 12338 (BstLean.Part260.worldParameters 12338) BstLean.Part259.agent12338 := by
  rw [BstLean.Part260.parameters12338]
  exact BstLean.Part261.master12338

theorem compatible12338 : BstLean.Part259.agent12338.charge ≤ master12338.retainedCharge := by
  change BstLean.Part259.agent12338.charge ≤ BstLean.Part261.master12338.retainedCharge
  rw [show BstLean.Part261.master12338.retainedCharge =
    BstLean.Part259.scalar12338.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12338]
  norm_num [BstLean.Part259.agent12338, BstLean.Part259.scalar12338]

noncomputable def row12338 : BstLean.Part259.RowInputs 12338 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12338
    master12338 BstLean.Part262.actualCertificate12338
    BstLean.Part264b.N12338.covarianceEvent12338
    (BstLean.Part263.cell BstLean.Part263.scalarRow12338.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12338)
    BstLean.Part264b.N12338.covarianceEvent12338_measurable BstLean.Part264b.N12338.covarianceEvent12338_payment
    BstLean.Part264b.N12338.frame12338 (fun t c hw hc => ⟨root12338 t c hw hc⟩)
    BstLean.Part262.allocation12338 compatible12338

theorem energy12339 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12339.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12339, BstLean.Part263.cell12339]

noncomputable def root12339 (t : ℝ) (c : Ret 12339)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12339 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12339) :
    BstLean.Part243.RootInputs 12339 t c BstLean.Part259.agent12339.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12339
    BstLean.Part264b.N12339.sourceNumerics12339
    (by norm_num [BstLean.Part263.scalarRow12339])
    (by norm_num [BstLean.Part263.scalarRow12339])
    (by norm_num [BstLean.Part263.scalarRow12339])
    energy12339 BstLean.Part262.actualCertificate12339 t c hw hc

noncomputable def master12339 :
    MasterCertificate 12339 (BstLean.Part260.worldParameters 12339) BstLean.Part259.agent12339 := by
  rw [BstLean.Part260.parameters12339]
  exact BstLean.Part261.master12339

theorem compatible12339 : BstLean.Part259.agent12339.charge ≤ master12339.retainedCharge := by
  change BstLean.Part259.agent12339.charge ≤ BstLean.Part261.master12339.retainedCharge
  rw [show BstLean.Part261.master12339.retainedCharge =
    BstLean.Part259.scalar12339.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12339]
  norm_num [BstLean.Part259.agent12339, BstLean.Part259.scalar12339]

noncomputable def row12339 : BstLean.Part259.RowInputs 12339 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12339
    master12339 BstLean.Part262.actualCertificate12339
    BstLean.Part264b.N12339.covarianceEvent12339
    (BstLean.Part263.cell BstLean.Part263.scalarRow12339.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12339)
    BstLean.Part264b.N12339.covarianceEvent12339_measurable BstLean.Part264b.N12339.covarianceEvent12339_payment
    BstLean.Part264b.N12339.frame12339 (fun t c hw hc => ⟨root12339 t c hw hc⟩)
    BstLean.Part262.allocation12339 compatible12339

theorem energy12340 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12340.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12340, BstLean.Part263.cell12340]

noncomputable def root12340 (t : ℝ) (c : Ret 12340)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12340 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12340) :
    BstLean.Part243.RootInputs 12340 t c BstLean.Part259.agent12340.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12340
    BstLean.Part264b.N12340.sourceNumerics12340
    (by norm_num [BstLean.Part263.scalarRow12340])
    (by norm_num [BstLean.Part263.scalarRow12340])
    (by norm_num [BstLean.Part263.scalarRow12340])
    energy12340 BstLean.Part262.actualCertificate12340 t c hw hc

noncomputable def master12340 :
    MasterCertificate 12340 (BstLean.Part260.worldParameters 12340) BstLean.Part259.agent12340 := by
  rw [BstLean.Part260.parameters12340]
  exact BstLean.Part261.master12340

theorem compatible12340 : BstLean.Part259.agent12340.charge ≤ master12340.retainedCharge := by
  change BstLean.Part259.agent12340.charge ≤ BstLean.Part261.master12340.retainedCharge
  rw [show BstLean.Part261.master12340.retainedCharge =
    BstLean.Part259.scalar12340.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12340]
  norm_num [BstLean.Part259.agent12340, BstLean.Part259.scalar12340]

noncomputable def row12340 : BstLean.Part259.RowInputs 12340 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12340
    master12340 BstLean.Part262.actualCertificate12340
    BstLean.Part264b.N12340.covarianceEvent12340
    (BstLean.Part263.cell BstLean.Part263.scalarRow12340.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12340)
    BstLean.Part264b.N12340.covarianceEvent12340_measurable BstLean.Part264b.N12340.covarianceEvent12340_payment
    BstLean.Part264b.N12340.frame12340 (fun t c hw hc => ⟨root12340 t c hw hc⟩)
    BstLean.Part262.allocation12340 compatible12340

theorem energy12341 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12341.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12341, BstLean.Part263.cell12341]

noncomputable def root12341 (t : ℝ) (c : Ret 12341)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12341 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12341) :
    BstLean.Part243.RootInputs 12341 t c BstLean.Part259.agent12341.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12341
    BstLean.Part264b.N12341.sourceNumerics12341
    (by norm_num [BstLean.Part263.scalarRow12341])
    (by norm_num [BstLean.Part263.scalarRow12341])
    (by norm_num [BstLean.Part263.scalarRow12341])
    energy12341 BstLean.Part262.actualCertificate12341 t c hw hc

noncomputable def master12341 :
    MasterCertificate 12341 (BstLean.Part260.worldParameters 12341) BstLean.Part259.agent12341 := by
  rw [BstLean.Part260.parameters12341]
  exact BstLean.Part261.master12341

theorem compatible12341 : BstLean.Part259.agent12341.charge ≤ master12341.retainedCharge := by
  change BstLean.Part259.agent12341.charge ≤ BstLean.Part261.master12341.retainedCharge
  rw [show BstLean.Part261.master12341.retainedCharge =
    BstLean.Part259.scalar12341.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12341]
  norm_num [BstLean.Part259.agent12341, BstLean.Part259.scalar12341]

noncomputable def row12341 : BstLean.Part259.RowInputs 12341 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12341
    master12341 BstLean.Part262.actualCertificate12341
    BstLean.Part264b.N12341.covarianceEvent12341
    (BstLean.Part263.cell BstLean.Part263.scalarRow12341.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12341)
    BstLean.Part264b.N12341.covarianceEvent12341_measurable BstLean.Part264b.N12341.covarianceEvent12341_payment
    BstLean.Part264b.N12341.frame12341 (fun t c hw hc => ⟨root12341 t c hw hc⟩)
    BstLean.Part262.allocation12341 compatible12341

theorem energy12342 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12342.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12342, BstLean.Part263.cell12342]

noncomputable def root12342 (t : ℝ) (c : Ret 12342)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12342 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12342) :
    BstLean.Part243.RootInputs 12342 t c BstLean.Part259.agent12342.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12342
    BstLean.Part264b.N12342.sourceNumerics12342
    (by norm_num [BstLean.Part263.scalarRow12342])
    (by norm_num [BstLean.Part263.scalarRow12342])
    (by norm_num [BstLean.Part263.scalarRow12342])
    energy12342 BstLean.Part262.actualCertificate12342 t c hw hc

noncomputable def master12342 :
    MasterCertificate 12342 (BstLean.Part260.worldParameters 12342) BstLean.Part259.agent12342 := by
  rw [BstLean.Part260.parameters12342]
  exact BstLean.Part261.master12342

theorem compatible12342 : BstLean.Part259.agent12342.charge ≤ master12342.retainedCharge := by
  change BstLean.Part259.agent12342.charge ≤ BstLean.Part261.master12342.retainedCharge
  rw [show BstLean.Part261.master12342.retainedCharge =
    BstLean.Part259.scalar12342.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12342]
  norm_num [BstLean.Part259.agent12342, BstLean.Part259.scalar12342]

noncomputable def row12342 : BstLean.Part259.RowInputs 12342 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12342
    master12342 BstLean.Part262.actualCertificate12342
    BstLean.Part264b.N12342.covarianceEvent12342
    (BstLean.Part263.cell BstLean.Part263.scalarRow12342.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12342)
    BstLean.Part264b.N12342.covarianceEvent12342_measurable BstLean.Part264b.N12342.covarianceEvent12342_payment
    BstLean.Part264b.N12342.frame12342 (fun t c hw hc => ⟨root12342 t c hw hc⟩)
    BstLean.Part262.allocation12342 compatible12342

theorem energy12343 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12343.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12343, BstLean.Part263.cell12343]

noncomputable def root12343 (t : ℝ) (c : Ret 12343)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12343 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12343) :
    BstLean.Part243.RootInputs 12343 t c BstLean.Part259.agent12343.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12343
    BstLean.Part264b.N12343.sourceNumerics12343
    (by norm_num [BstLean.Part263.scalarRow12343])
    (by norm_num [BstLean.Part263.scalarRow12343])
    (by norm_num [BstLean.Part263.scalarRow12343])
    energy12343 BstLean.Part262.actualCertificate12343 t c hw hc

noncomputable def master12343 :
    MasterCertificate 12343 (BstLean.Part260.worldParameters 12343) BstLean.Part259.agent12343 := by
  rw [BstLean.Part260.parameters12343]
  exact BstLean.Part261.master12343

theorem compatible12343 : BstLean.Part259.agent12343.charge ≤ master12343.retainedCharge := by
  change BstLean.Part259.agent12343.charge ≤ BstLean.Part261.master12343.retainedCharge
  rw [show BstLean.Part261.master12343.retainedCharge =
    BstLean.Part259.scalar12343.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12343]
  norm_num [BstLean.Part259.agent12343, BstLean.Part259.scalar12343]

noncomputable def row12343 : BstLean.Part259.RowInputs 12343 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12343
    master12343 BstLean.Part262.actualCertificate12343
    BstLean.Part264b.N12343.covarianceEvent12343
    (BstLean.Part263.cell BstLean.Part263.scalarRow12343.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12343)
    BstLean.Part264b.N12343.covarianceEvent12343_measurable BstLean.Part264b.N12343.covarianceEvent12343_payment
    BstLean.Part264b.N12343.frame12343 (fun t c hw hc => ⟨root12343 t c hw hc⟩)
    BstLean.Part262.allocation12343 compatible12343

theorem energy12344 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12344.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12344, BstLean.Part263.cell12344]

noncomputable def root12344 (t : ℝ) (c : Ret 12344)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12344 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12344) :
    BstLean.Part243.RootInputs 12344 t c BstLean.Part259.agent12344.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12344
    BstLean.Part264b.N12344.sourceNumerics12344
    (by norm_num [BstLean.Part263.scalarRow12344])
    (by norm_num [BstLean.Part263.scalarRow12344])
    (by norm_num [BstLean.Part263.scalarRow12344])
    energy12344 BstLean.Part262.actualCertificate12344 t c hw hc

noncomputable def master12344 :
    MasterCertificate 12344 (BstLean.Part260.worldParameters 12344) BstLean.Part259.agent12344 := by
  rw [BstLean.Part260.parameters12344]
  exact BstLean.Part261.master12344

theorem compatible12344 : BstLean.Part259.agent12344.charge ≤ master12344.retainedCharge := by
  change BstLean.Part259.agent12344.charge ≤ BstLean.Part261.master12344.retainedCharge
  rw [show BstLean.Part261.master12344.retainedCharge =
    BstLean.Part259.scalar12344.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12344]
  norm_num [BstLean.Part259.agent12344, BstLean.Part259.scalar12344]

noncomputable def row12344 : BstLean.Part259.RowInputs 12344 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12344
    master12344 BstLean.Part262.actualCertificate12344
    BstLean.Part264b.N12344.covarianceEvent12344
    (BstLean.Part263.cell BstLean.Part263.scalarRow12344.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12344)
    BstLean.Part264b.N12344.covarianceEvent12344_measurable BstLean.Part264b.N12344.covarianceEvent12344_payment
    BstLean.Part264b.N12344.frame12344 (fun t c hw hc => ⟨root12344 t c hw hc⟩)
    BstLean.Part262.allocation12344 compatible12344

theorem energy12345 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12345.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12345, BstLean.Part263.cell12345]

noncomputable def root12345 (t : ℝ) (c : Ret 12345)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12345 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12345) :
    BstLean.Part243.RootInputs 12345 t c BstLean.Part259.agent12345.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12345
    BstLean.Part264b.N12345.sourceNumerics12345
    (by norm_num [BstLean.Part263.scalarRow12345])
    (by norm_num [BstLean.Part263.scalarRow12345])
    (by norm_num [BstLean.Part263.scalarRow12345])
    energy12345 BstLean.Part262.actualCertificate12345 t c hw hc

noncomputable def master12345 :
    MasterCertificate 12345 (BstLean.Part260.worldParameters 12345) BstLean.Part259.agent12345 := by
  rw [BstLean.Part260.parameters12345]
  exact BstLean.Part261.master12345

theorem compatible12345 : BstLean.Part259.agent12345.charge ≤ master12345.retainedCharge := by
  change BstLean.Part259.agent12345.charge ≤ BstLean.Part261.master12345.retainedCharge
  rw [show BstLean.Part261.master12345.retainedCharge =
    BstLean.Part259.scalar12345.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12345]
  norm_num [BstLean.Part259.agent12345, BstLean.Part259.scalar12345]

noncomputable def row12345 : BstLean.Part259.RowInputs 12345 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12345
    master12345 BstLean.Part262.actualCertificate12345
    BstLean.Part264b.N12345.covarianceEvent12345
    (BstLean.Part263.cell BstLean.Part263.scalarRow12345.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12345)
    BstLean.Part264b.N12345.covarianceEvent12345_measurable BstLean.Part264b.N12345.covarianceEvent12345_payment
    BstLean.Part264b.N12345.frame12345 (fun t c hw hc => ⟨root12345 t c hw hc⟩)
    BstLean.Part262.allocation12345 compatible12345

theorem energy12346 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12346.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12346, BstLean.Part263.cell12346]

noncomputable def root12346 (t : ℝ) (c : Ret 12346)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12346 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12346) :
    BstLean.Part243.RootInputs 12346 t c BstLean.Part259.agent12346.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12346
    BstLean.Part264b.N12346.sourceNumerics12346
    (by norm_num [BstLean.Part263.scalarRow12346])
    (by norm_num [BstLean.Part263.scalarRow12346])
    (by norm_num [BstLean.Part263.scalarRow12346])
    energy12346 BstLean.Part262.actualCertificate12346 t c hw hc

noncomputable def master12346 :
    MasterCertificate 12346 (BstLean.Part260.worldParameters 12346) BstLean.Part259.agent12346 := by
  rw [BstLean.Part260.parameters12346]
  exact BstLean.Part261.master12346

theorem compatible12346 : BstLean.Part259.agent12346.charge ≤ master12346.retainedCharge := by
  change BstLean.Part259.agent12346.charge ≤ BstLean.Part261.master12346.retainedCharge
  rw [show BstLean.Part261.master12346.retainedCharge =
    BstLean.Part259.scalar12346.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12346]
  norm_num [BstLean.Part259.agent12346, BstLean.Part259.scalar12346]

noncomputable def row12346 : BstLean.Part259.RowInputs 12346 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12346
    master12346 BstLean.Part262.actualCertificate12346
    BstLean.Part264b.N12346.covarianceEvent12346
    (BstLean.Part263.cell BstLean.Part263.scalarRow12346.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12346)
    BstLean.Part264b.N12346.covarianceEvent12346_measurable BstLean.Part264b.N12346.covarianceEvent12346_payment
    BstLean.Part264b.N12346.frame12346 (fun t c hw hc => ⟨root12346 t c hw hc⟩)
    BstLean.Part262.allocation12346 compatible12346

theorem energy12347 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12347.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12347, BstLean.Part263.cell12347]

noncomputable def root12347 (t : ℝ) (c : Ret 12347)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12347 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12347) :
    BstLean.Part243.RootInputs 12347 t c BstLean.Part259.agent12347.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12347
    BstLean.Part264b.N12347.sourceNumerics12347
    (by norm_num [BstLean.Part263.scalarRow12347])
    (by norm_num [BstLean.Part263.scalarRow12347])
    (by norm_num [BstLean.Part263.scalarRow12347])
    energy12347 BstLean.Part262.actualCertificate12347 t c hw hc

noncomputable def master12347 :
    MasterCertificate 12347 (BstLean.Part260.worldParameters 12347) BstLean.Part259.agent12347 := by
  rw [BstLean.Part260.parameters12347]
  exact BstLean.Part261.master12347

theorem compatible12347 : BstLean.Part259.agent12347.charge ≤ master12347.retainedCharge := by
  change BstLean.Part259.agent12347.charge ≤ BstLean.Part261.master12347.retainedCharge
  rw [show BstLean.Part261.master12347.retainedCharge =
    BstLean.Part259.scalar12347.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12347]
  norm_num [BstLean.Part259.agent12347, BstLean.Part259.scalar12347]

noncomputable def row12347 : BstLean.Part259.RowInputs 12347 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12347
    master12347 BstLean.Part262.actualCertificate12347
    BstLean.Part264b.N12347.covarianceEvent12347
    (BstLean.Part263.cell BstLean.Part263.scalarRow12347.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12347)
    BstLean.Part264b.N12347.covarianceEvent12347_measurable BstLean.Part264b.N12347.covarianceEvent12347_payment
    BstLean.Part264b.N12347.frame12347 (fun t c hw hc => ⟨root12347 t c hw hc⟩)
    BstLean.Part262.allocation12347 compatible12347

theorem energy12348 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12348.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12348, BstLean.Part263.cell12348]

noncomputable def root12348 (t : ℝ) (c : Ret 12348)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12348 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12348) :
    BstLean.Part243.RootInputs 12348 t c BstLean.Part259.agent12348.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12348
    BstLean.Part264b.N12348.sourceNumerics12348
    (by norm_num [BstLean.Part263.scalarRow12348])
    (by norm_num [BstLean.Part263.scalarRow12348])
    (by norm_num [BstLean.Part263.scalarRow12348])
    energy12348 BstLean.Part262.actualCertificate12348 t c hw hc

noncomputable def master12348 :
    MasterCertificate 12348 (BstLean.Part260.worldParameters 12348) BstLean.Part259.agent12348 := by
  rw [BstLean.Part260.parameters12348]
  exact BstLean.Part261.master12348

theorem compatible12348 : BstLean.Part259.agent12348.charge ≤ master12348.retainedCharge := by
  change BstLean.Part259.agent12348.charge ≤ BstLean.Part261.master12348.retainedCharge
  rw [show BstLean.Part261.master12348.retainedCharge =
    BstLean.Part259.scalar12348.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12348]
  norm_num [BstLean.Part259.agent12348, BstLean.Part259.scalar12348]

noncomputable def row12348 : BstLean.Part259.RowInputs 12348 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12348
    master12348 BstLean.Part262.actualCertificate12348
    BstLean.Part264b.N12348.covarianceEvent12348
    (BstLean.Part263.cell BstLean.Part263.scalarRow12348.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12348)
    BstLean.Part264b.N12348.covarianceEvent12348_measurable BstLean.Part264b.N12348.covarianceEvent12348_payment
    BstLean.Part264b.N12348.frame12348 (fun t c hw hc => ⟨root12348 t c hw hc⟩)
    BstLean.Part262.allocation12348 compatible12348

theorem energy12349 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12349.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12349, BstLean.Part263.cell12349]

noncomputable def root12349 (t : ℝ) (c : Ret 12349)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12349 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12349) :
    BstLean.Part243.RootInputs 12349 t c BstLean.Part259.agent12349.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12349
    BstLean.Part264b.N12349.sourceNumerics12349
    (by norm_num [BstLean.Part263.scalarRow12349])
    (by norm_num [BstLean.Part263.scalarRow12349])
    (by norm_num [BstLean.Part263.scalarRow12349])
    energy12349 BstLean.Part262.actualCertificate12349 t c hw hc

noncomputable def master12349 :
    MasterCertificate 12349 (BstLean.Part260.worldParameters 12349) BstLean.Part259.agent12349 := by
  rw [BstLean.Part260.parameters12349]
  exact BstLean.Part261.master12349

theorem compatible12349 : BstLean.Part259.agent12349.charge ≤ master12349.retainedCharge := by
  change BstLean.Part259.agent12349.charge ≤ BstLean.Part261.master12349.retainedCharge
  rw [show BstLean.Part261.master12349.retainedCharge =
    BstLean.Part259.scalar12349.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12349]
  norm_num [BstLean.Part259.agent12349, BstLean.Part259.scalar12349]

noncomputable def row12349 : BstLean.Part259.RowInputs 12349 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12349
    master12349 BstLean.Part262.actualCertificate12349
    BstLean.Part264b.N12349.covarianceEvent12349
    (BstLean.Part263.cell BstLean.Part263.scalarRow12349.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12349)
    BstLean.Part264b.N12349.covarianceEvent12349_measurable BstLean.Part264b.N12349.covarianceEvent12349_payment
    BstLean.Part264b.N12349.frame12349 (fun t c hw hc => ⟨root12349 t c hw hc⟩)
    BstLean.Part262.allocation12349 compatible12349

end BstLean.Part267
