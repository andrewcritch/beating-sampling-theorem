import BstLean.Part267Bridge
import BstLean.Part264bFamily
import BstLean.Part261Coverage
import BstLean.Part262ActualCoverage

namespace BstLean.Part267
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part192 BstLean.Part196

theorem energy12230 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12230.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12230, BstLean.Part263.cell12230]

noncomputable def root12230 (t : ℝ) (c : Ret 12230)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12230 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12230) :
    BstLean.Part243.RootInputs 12230 t c BstLean.Part259.agent12230.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12230
    BstLean.Part264b.N12230.sourceNumerics12230
    (by norm_num [BstLean.Part263.scalarRow12230])
    (by norm_num [BstLean.Part263.scalarRow12230])
    (by norm_num [BstLean.Part263.scalarRow12230])
    energy12230 BstLean.Part262.actualCertificate12230 t c hw hc

noncomputable def master12230 :
    MasterCertificate 12230 (BstLean.Part260.worldParameters 12230) BstLean.Part259.agent12230 := by
  rw [BstLean.Part260.parameters12230]
  exact BstLean.Part261.master12230

theorem compatible12230 : BstLean.Part259.agent12230.charge ≤ master12230.retainedCharge := by
  change BstLean.Part259.agent12230.charge ≤ BstLean.Part261.master12230.retainedCharge
  rw [show BstLean.Part261.master12230.retainedCharge =
    BstLean.Part259.scalar12230.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12230]
  norm_num [BstLean.Part259.agent12230, BstLean.Part259.scalar12230]

noncomputable def row12230 : BstLean.Part259.RowInputs 12230 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12230
    master12230 BstLean.Part262.actualCertificate12230
    BstLean.Part264b.N12230.covarianceEvent12230
    (BstLean.Part263.cell BstLean.Part263.scalarRow12230.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12230)
    BstLean.Part264b.N12230.covarianceEvent12230_measurable BstLean.Part264b.N12230.covarianceEvent12230_payment
    BstLean.Part264b.N12230.frame12230 (fun t c hw hc => ⟨root12230 t c hw hc⟩)
    BstLean.Part262.allocation12230 compatible12230

theorem energy12231 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12231.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12231, BstLean.Part263.cell12231]

noncomputable def root12231 (t : ℝ) (c : Ret 12231)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12231 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12231) :
    BstLean.Part243.RootInputs 12231 t c BstLean.Part259.agent12231.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12231
    BstLean.Part264b.N12231.sourceNumerics12231
    (by norm_num [BstLean.Part263.scalarRow12231])
    (by norm_num [BstLean.Part263.scalarRow12231])
    (by norm_num [BstLean.Part263.scalarRow12231])
    energy12231 BstLean.Part262.actualCertificate12231 t c hw hc

noncomputable def master12231 :
    MasterCertificate 12231 (BstLean.Part260.worldParameters 12231) BstLean.Part259.agent12231 := by
  rw [BstLean.Part260.parameters12231]
  exact BstLean.Part261.master12231

theorem compatible12231 : BstLean.Part259.agent12231.charge ≤ master12231.retainedCharge := by
  change BstLean.Part259.agent12231.charge ≤ BstLean.Part261.master12231.retainedCharge
  rw [show BstLean.Part261.master12231.retainedCharge =
    BstLean.Part259.scalar12231.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12231]
  norm_num [BstLean.Part259.agent12231, BstLean.Part259.scalar12231]

noncomputable def row12231 : BstLean.Part259.RowInputs 12231 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12231
    master12231 BstLean.Part262.actualCertificate12231
    BstLean.Part264b.N12231.covarianceEvent12231
    (BstLean.Part263.cell BstLean.Part263.scalarRow12231.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12231)
    BstLean.Part264b.N12231.covarianceEvent12231_measurable BstLean.Part264b.N12231.covarianceEvent12231_payment
    BstLean.Part264b.N12231.frame12231 (fun t c hw hc => ⟨root12231 t c hw hc⟩)
    BstLean.Part262.allocation12231 compatible12231

theorem energy12232 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12232.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12232, BstLean.Part263.cell12232]

noncomputable def root12232 (t : ℝ) (c : Ret 12232)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12232 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12232) :
    BstLean.Part243.RootInputs 12232 t c BstLean.Part259.agent12232.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12232
    BstLean.Part264b.N12232.sourceNumerics12232
    (by norm_num [BstLean.Part263.scalarRow12232])
    (by norm_num [BstLean.Part263.scalarRow12232])
    (by norm_num [BstLean.Part263.scalarRow12232])
    energy12232 BstLean.Part262.actualCertificate12232 t c hw hc

noncomputable def master12232 :
    MasterCertificate 12232 (BstLean.Part260.worldParameters 12232) BstLean.Part259.agent12232 := by
  rw [BstLean.Part260.parameters12232]
  exact BstLean.Part261.master12232

theorem compatible12232 : BstLean.Part259.agent12232.charge ≤ master12232.retainedCharge := by
  change BstLean.Part259.agent12232.charge ≤ BstLean.Part261.master12232.retainedCharge
  rw [show BstLean.Part261.master12232.retainedCharge =
    BstLean.Part259.scalar12232.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12232]
  norm_num [BstLean.Part259.agent12232, BstLean.Part259.scalar12232]

noncomputable def row12232 : BstLean.Part259.RowInputs 12232 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12232
    master12232 BstLean.Part262.actualCertificate12232
    BstLean.Part264b.N12232.covarianceEvent12232
    (BstLean.Part263.cell BstLean.Part263.scalarRow12232.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12232)
    BstLean.Part264b.N12232.covarianceEvent12232_measurable BstLean.Part264b.N12232.covarianceEvent12232_payment
    BstLean.Part264b.N12232.frame12232 (fun t c hw hc => ⟨root12232 t c hw hc⟩)
    BstLean.Part262.allocation12232 compatible12232

theorem energy12233 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12233.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12233, BstLean.Part263.cell12233]

noncomputable def root12233 (t : ℝ) (c : Ret 12233)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12233 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12233) :
    BstLean.Part243.RootInputs 12233 t c BstLean.Part259.agent12233.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12233
    BstLean.Part264b.N12233.sourceNumerics12233
    (by norm_num [BstLean.Part263.scalarRow12233])
    (by norm_num [BstLean.Part263.scalarRow12233])
    (by norm_num [BstLean.Part263.scalarRow12233])
    energy12233 BstLean.Part262.actualCertificate12233 t c hw hc

noncomputable def master12233 :
    MasterCertificate 12233 (BstLean.Part260.worldParameters 12233) BstLean.Part259.agent12233 := by
  rw [BstLean.Part260.parameters12233]
  exact BstLean.Part261.master12233

theorem compatible12233 : BstLean.Part259.agent12233.charge ≤ master12233.retainedCharge := by
  change BstLean.Part259.agent12233.charge ≤ BstLean.Part261.master12233.retainedCharge
  rw [show BstLean.Part261.master12233.retainedCharge =
    BstLean.Part259.scalar12233.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12233]
  norm_num [BstLean.Part259.agent12233, BstLean.Part259.scalar12233]

noncomputable def row12233 : BstLean.Part259.RowInputs 12233 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12233
    master12233 BstLean.Part262.actualCertificate12233
    BstLean.Part264b.N12233.covarianceEvent12233
    (BstLean.Part263.cell BstLean.Part263.scalarRow12233.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12233)
    BstLean.Part264b.N12233.covarianceEvent12233_measurable BstLean.Part264b.N12233.covarianceEvent12233_payment
    BstLean.Part264b.N12233.frame12233 (fun t c hw hc => ⟨root12233 t c hw hc⟩)
    BstLean.Part262.allocation12233 compatible12233

theorem energy12234 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12234.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12234, BstLean.Part263.cell12234]

noncomputable def root12234 (t : ℝ) (c : Ret 12234)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12234 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12234) :
    BstLean.Part243.RootInputs 12234 t c BstLean.Part259.agent12234.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12234
    BstLean.Part264b.N12234.sourceNumerics12234
    (by norm_num [BstLean.Part263.scalarRow12234])
    (by norm_num [BstLean.Part263.scalarRow12234])
    (by norm_num [BstLean.Part263.scalarRow12234])
    energy12234 BstLean.Part262.actualCertificate12234 t c hw hc

noncomputable def master12234 :
    MasterCertificate 12234 (BstLean.Part260.worldParameters 12234) BstLean.Part259.agent12234 := by
  rw [BstLean.Part260.parameters12234]
  exact BstLean.Part261.master12234

theorem compatible12234 : BstLean.Part259.agent12234.charge ≤ master12234.retainedCharge := by
  change BstLean.Part259.agent12234.charge ≤ BstLean.Part261.master12234.retainedCharge
  rw [show BstLean.Part261.master12234.retainedCharge =
    BstLean.Part259.scalar12234.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12234]
  norm_num [BstLean.Part259.agent12234, BstLean.Part259.scalar12234]

noncomputable def row12234 : BstLean.Part259.RowInputs 12234 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12234
    master12234 BstLean.Part262.actualCertificate12234
    BstLean.Part264b.N12234.covarianceEvent12234
    (BstLean.Part263.cell BstLean.Part263.scalarRow12234.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12234)
    BstLean.Part264b.N12234.covarianceEvent12234_measurable BstLean.Part264b.N12234.covarianceEvent12234_payment
    BstLean.Part264b.N12234.frame12234 (fun t c hw hc => ⟨root12234 t c hw hc⟩)
    BstLean.Part262.allocation12234 compatible12234

theorem energy12235 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12235.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12235, BstLean.Part263.cell12235]

noncomputable def root12235 (t : ℝ) (c : Ret 12235)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12235 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12235) :
    BstLean.Part243.RootInputs 12235 t c BstLean.Part259.agent12235.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12235
    BstLean.Part264b.N12235.sourceNumerics12235
    (by norm_num [BstLean.Part263.scalarRow12235])
    (by norm_num [BstLean.Part263.scalarRow12235])
    (by norm_num [BstLean.Part263.scalarRow12235])
    energy12235 BstLean.Part262.actualCertificate12235 t c hw hc

noncomputable def master12235 :
    MasterCertificate 12235 (BstLean.Part260.worldParameters 12235) BstLean.Part259.agent12235 := by
  rw [BstLean.Part260.parameters12235]
  exact BstLean.Part261.master12235

theorem compatible12235 : BstLean.Part259.agent12235.charge ≤ master12235.retainedCharge := by
  change BstLean.Part259.agent12235.charge ≤ BstLean.Part261.master12235.retainedCharge
  rw [show BstLean.Part261.master12235.retainedCharge =
    BstLean.Part259.scalar12235.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12235]
  norm_num [BstLean.Part259.agent12235, BstLean.Part259.scalar12235]

noncomputable def row12235 : BstLean.Part259.RowInputs 12235 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12235
    master12235 BstLean.Part262.actualCertificate12235
    BstLean.Part264b.N12235.covarianceEvent12235
    (BstLean.Part263.cell BstLean.Part263.scalarRow12235.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12235)
    BstLean.Part264b.N12235.covarianceEvent12235_measurable BstLean.Part264b.N12235.covarianceEvent12235_payment
    BstLean.Part264b.N12235.frame12235 (fun t c hw hc => ⟨root12235 t c hw hc⟩)
    BstLean.Part262.allocation12235 compatible12235

theorem energy12236 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12236.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12236, BstLean.Part263.cell12236]

noncomputable def root12236 (t : ℝ) (c : Ret 12236)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12236 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12236) :
    BstLean.Part243.RootInputs 12236 t c BstLean.Part259.agent12236.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12236
    BstLean.Part264b.N12236.sourceNumerics12236
    (by norm_num [BstLean.Part263.scalarRow12236])
    (by norm_num [BstLean.Part263.scalarRow12236])
    (by norm_num [BstLean.Part263.scalarRow12236])
    energy12236 BstLean.Part262.actualCertificate12236 t c hw hc

noncomputable def master12236 :
    MasterCertificate 12236 (BstLean.Part260.worldParameters 12236) BstLean.Part259.agent12236 := by
  rw [BstLean.Part260.parameters12236]
  exact BstLean.Part261.master12236

theorem compatible12236 : BstLean.Part259.agent12236.charge ≤ master12236.retainedCharge := by
  change BstLean.Part259.agent12236.charge ≤ BstLean.Part261.master12236.retainedCharge
  rw [show BstLean.Part261.master12236.retainedCharge =
    BstLean.Part259.scalar12236.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12236]
  norm_num [BstLean.Part259.agent12236, BstLean.Part259.scalar12236]

noncomputable def row12236 : BstLean.Part259.RowInputs 12236 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12236
    master12236 BstLean.Part262.actualCertificate12236
    BstLean.Part264b.N12236.covarianceEvent12236
    (BstLean.Part263.cell BstLean.Part263.scalarRow12236.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12236)
    BstLean.Part264b.N12236.covarianceEvent12236_measurable BstLean.Part264b.N12236.covarianceEvent12236_payment
    BstLean.Part264b.N12236.frame12236 (fun t c hw hc => ⟨root12236 t c hw hc⟩)
    BstLean.Part262.allocation12236 compatible12236

theorem energy12237 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12237.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12237, BstLean.Part263.cell12237]

noncomputable def root12237 (t : ℝ) (c : Ret 12237)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12237 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12237) :
    BstLean.Part243.RootInputs 12237 t c BstLean.Part259.agent12237.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12237
    BstLean.Part264b.N12237.sourceNumerics12237
    (by norm_num [BstLean.Part263.scalarRow12237])
    (by norm_num [BstLean.Part263.scalarRow12237])
    (by norm_num [BstLean.Part263.scalarRow12237])
    energy12237 BstLean.Part262.actualCertificate12237 t c hw hc

noncomputable def master12237 :
    MasterCertificate 12237 (BstLean.Part260.worldParameters 12237) BstLean.Part259.agent12237 := by
  rw [BstLean.Part260.parameters12237]
  exact BstLean.Part261.master12237

theorem compatible12237 : BstLean.Part259.agent12237.charge ≤ master12237.retainedCharge := by
  change BstLean.Part259.agent12237.charge ≤ BstLean.Part261.master12237.retainedCharge
  rw [show BstLean.Part261.master12237.retainedCharge =
    BstLean.Part259.scalar12237.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12237]
  norm_num [BstLean.Part259.agent12237, BstLean.Part259.scalar12237]

noncomputable def row12237 : BstLean.Part259.RowInputs 12237 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12237
    master12237 BstLean.Part262.actualCertificate12237
    BstLean.Part264b.N12237.covarianceEvent12237
    (BstLean.Part263.cell BstLean.Part263.scalarRow12237.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12237)
    BstLean.Part264b.N12237.covarianceEvent12237_measurable BstLean.Part264b.N12237.covarianceEvent12237_payment
    BstLean.Part264b.N12237.frame12237 (fun t c hw hc => ⟨root12237 t c hw hc⟩)
    BstLean.Part262.allocation12237 compatible12237

theorem energy12238 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12238.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12238, BstLean.Part263.cell12238]

noncomputable def root12238 (t : ℝ) (c : Ret 12238)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12238 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12238) :
    BstLean.Part243.RootInputs 12238 t c BstLean.Part259.agent12238.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12238
    BstLean.Part264b.N12238.sourceNumerics12238
    (by norm_num [BstLean.Part263.scalarRow12238])
    (by norm_num [BstLean.Part263.scalarRow12238])
    (by norm_num [BstLean.Part263.scalarRow12238])
    energy12238 BstLean.Part262.actualCertificate12238 t c hw hc

noncomputable def master12238 :
    MasterCertificate 12238 (BstLean.Part260.worldParameters 12238) BstLean.Part259.agent12238 := by
  rw [BstLean.Part260.parameters12238]
  exact BstLean.Part261.master12238

theorem compatible12238 : BstLean.Part259.agent12238.charge ≤ master12238.retainedCharge := by
  change BstLean.Part259.agent12238.charge ≤ BstLean.Part261.master12238.retainedCharge
  rw [show BstLean.Part261.master12238.retainedCharge =
    BstLean.Part259.scalar12238.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12238]
  norm_num [BstLean.Part259.agent12238, BstLean.Part259.scalar12238]

noncomputable def row12238 : BstLean.Part259.RowInputs 12238 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12238
    master12238 BstLean.Part262.actualCertificate12238
    BstLean.Part264b.N12238.covarianceEvent12238
    (BstLean.Part263.cell BstLean.Part263.scalarRow12238.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12238)
    BstLean.Part264b.N12238.covarianceEvent12238_measurable BstLean.Part264b.N12238.covarianceEvent12238_payment
    BstLean.Part264b.N12238.frame12238 (fun t c hw hc => ⟨root12238 t c hw hc⟩)
    BstLean.Part262.allocation12238 compatible12238

theorem energy12239 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12239.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12239, BstLean.Part263.cell12239]

noncomputable def root12239 (t : ℝ) (c : Ret 12239)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12239 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12239) :
    BstLean.Part243.RootInputs 12239 t c BstLean.Part259.agent12239.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12239
    BstLean.Part264b.N12239.sourceNumerics12239
    (by norm_num [BstLean.Part263.scalarRow12239])
    (by norm_num [BstLean.Part263.scalarRow12239])
    (by norm_num [BstLean.Part263.scalarRow12239])
    energy12239 BstLean.Part262.actualCertificate12239 t c hw hc

noncomputable def master12239 :
    MasterCertificate 12239 (BstLean.Part260.worldParameters 12239) BstLean.Part259.agent12239 := by
  rw [BstLean.Part260.parameters12239]
  exact BstLean.Part261.master12239

theorem compatible12239 : BstLean.Part259.agent12239.charge ≤ master12239.retainedCharge := by
  change BstLean.Part259.agent12239.charge ≤ BstLean.Part261.master12239.retainedCharge
  rw [show BstLean.Part261.master12239.retainedCharge =
    BstLean.Part259.scalar12239.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12239]
  norm_num [BstLean.Part259.agent12239, BstLean.Part259.scalar12239]

noncomputable def row12239 : BstLean.Part259.RowInputs 12239 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12239
    master12239 BstLean.Part262.actualCertificate12239
    BstLean.Part264b.N12239.covarianceEvent12239
    (BstLean.Part263.cell BstLean.Part263.scalarRow12239.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12239)
    BstLean.Part264b.N12239.covarianceEvent12239_measurable BstLean.Part264b.N12239.covarianceEvent12239_payment
    BstLean.Part264b.N12239.frame12239 (fun t c hw hc => ⟨root12239 t c hw hc⟩)
    BstLean.Part262.allocation12239 compatible12239

theorem energy12240 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12240.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12240, BstLean.Part263.cell12240]

noncomputable def root12240 (t : ℝ) (c : Ret 12240)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12240 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12240) :
    BstLean.Part243.RootInputs 12240 t c BstLean.Part259.agent12240.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12240
    BstLean.Part264b.N12240.sourceNumerics12240
    (by norm_num [BstLean.Part263.scalarRow12240])
    (by norm_num [BstLean.Part263.scalarRow12240])
    (by norm_num [BstLean.Part263.scalarRow12240])
    energy12240 BstLean.Part262.actualCertificate12240 t c hw hc

noncomputable def master12240 :
    MasterCertificate 12240 (BstLean.Part260.worldParameters 12240) BstLean.Part259.agent12240 := by
  rw [BstLean.Part260.parameters12240]
  exact BstLean.Part261.master12240

theorem compatible12240 : BstLean.Part259.agent12240.charge ≤ master12240.retainedCharge := by
  change BstLean.Part259.agent12240.charge ≤ BstLean.Part261.master12240.retainedCharge
  rw [show BstLean.Part261.master12240.retainedCharge =
    BstLean.Part259.scalar12240.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12240]
  norm_num [BstLean.Part259.agent12240, BstLean.Part259.scalar12240]

noncomputable def row12240 : BstLean.Part259.RowInputs 12240 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12240
    master12240 BstLean.Part262.actualCertificate12240
    BstLean.Part264b.N12240.covarianceEvent12240
    (BstLean.Part263.cell BstLean.Part263.scalarRow12240.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12240)
    BstLean.Part264b.N12240.covarianceEvent12240_measurable BstLean.Part264b.N12240.covarianceEvent12240_payment
    BstLean.Part264b.N12240.frame12240 (fun t c hw hc => ⟨root12240 t c hw hc⟩)
    BstLean.Part262.allocation12240 compatible12240

theorem energy12241 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12241.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12241, BstLean.Part263.cell12241]

noncomputable def root12241 (t : ℝ) (c : Ret 12241)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12241 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12241) :
    BstLean.Part243.RootInputs 12241 t c BstLean.Part259.agent12241.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12241
    BstLean.Part264b.N12241.sourceNumerics12241
    (by norm_num [BstLean.Part263.scalarRow12241])
    (by norm_num [BstLean.Part263.scalarRow12241])
    (by norm_num [BstLean.Part263.scalarRow12241])
    energy12241 BstLean.Part262.actualCertificate12241 t c hw hc

noncomputable def master12241 :
    MasterCertificate 12241 (BstLean.Part260.worldParameters 12241) BstLean.Part259.agent12241 := by
  rw [BstLean.Part260.parameters12241]
  exact BstLean.Part261.master12241

theorem compatible12241 : BstLean.Part259.agent12241.charge ≤ master12241.retainedCharge := by
  change BstLean.Part259.agent12241.charge ≤ BstLean.Part261.master12241.retainedCharge
  rw [show BstLean.Part261.master12241.retainedCharge =
    BstLean.Part259.scalar12241.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12241]
  norm_num [BstLean.Part259.agent12241, BstLean.Part259.scalar12241]

noncomputable def row12241 : BstLean.Part259.RowInputs 12241 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12241
    master12241 BstLean.Part262.actualCertificate12241
    BstLean.Part264b.N12241.covarianceEvent12241
    (BstLean.Part263.cell BstLean.Part263.scalarRow12241.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12241)
    BstLean.Part264b.N12241.covarianceEvent12241_measurable BstLean.Part264b.N12241.covarianceEvent12241_payment
    BstLean.Part264b.N12241.frame12241 (fun t c hw hc => ⟨root12241 t c hw hc⟩)
    BstLean.Part262.allocation12241 compatible12241

theorem energy12242 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12242.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12242, BstLean.Part263.cell12242]

noncomputable def root12242 (t : ℝ) (c : Ret 12242)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12242 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12242) :
    BstLean.Part243.RootInputs 12242 t c BstLean.Part259.agent12242.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12242
    BstLean.Part264b.N12242.sourceNumerics12242
    (by norm_num [BstLean.Part263.scalarRow12242])
    (by norm_num [BstLean.Part263.scalarRow12242])
    (by norm_num [BstLean.Part263.scalarRow12242])
    energy12242 BstLean.Part262.actualCertificate12242 t c hw hc

noncomputable def master12242 :
    MasterCertificate 12242 (BstLean.Part260.worldParameters 12242) BstLean.Part259.agent12242 := by
  rw [BstLean.Part260.parameters12242]
  exact BstLean.Part261.master12242

theorem compatible12242 : BstLean.Part259.agent12242.charge ≤ master12242.retainedCharge := by
  change BstLean.Part259.agent12242.charge ≤ BstLean.Part261.master12242.retainedCharge
  rw [show BstLean.Part261.master12242.retainedCharge =
    BstLean.Part259.scalar12242.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12242]
  norm_num [BstLean.Part259.agent12242, BstLean.Part259.scalar12242]

noncomputable def row12242 : BstLean.Part259.RowInputs 12242 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12242
    master12242 BstLean.Part262.actualCertificate12242
    BstLean.Part264b.N12242.covarianceEvent12242
    (BstLean.Part263.cell BstLean.Part263.scalarRow12242.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12242)
    BstLean.Part264b.N12242.covarianceEvent12242_measurable BstLean.Part264b.N12242.covarianceEvent12242_payment
    BstLean.Part264b.N12242.frame12242 (fun t c hw hc => ⟨root12242 t c hw hc⟩)
    BstLean.Part262.allocation12242 compatible12242

theorem energy12243 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12243.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12243, BstLean.Part263.cell12243]

noncomputable def root12243 (t : ℝ) (c : Ret 12243)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12243 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12243) :
    BstLean.Part243.RootInputs 12243 t c BstLean.Part259.agent12243.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12243
    BstLean.Part264b.N12243.sourceNumerics12243
    (by norm_num [BstLean.Part263.scalarRow12243])
    (by norm_num [BstLean.Part263.scalarRow12243])
    (by norm_num [BstLean.Part263.scalarRow12243])
    energy12243 BstLean.Part262.actualCertificate12243 t c hw hc

noncomputable def master12243 :
    MasterCertificate 12243 (BstLean.Part260.worldParameters 12243) BstLean.Part259.agent12243 := by
  rw [BstLean.Part260.parameters12243]
  exact BstLean.Part261.master12243

theorem compatible12243 : BstLean.Part259.agent12243.charge ≤ master12243.retainedCharge := by
  change BstLean.Part259.agent12243.charge ≤ BstLean.Part261.master12243.retainedCharge
  rw [show BstLean.Part261.master12243.retainedCharge =
    BstLean.Part259.scalar12243.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12243]
  norm_num [BstLean.Part259.agent12243, BstLean.Part259.scalar12243]

noncomputable def row12243 : BstLean.Part259.RowInputs 12243 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12243
    master12243 BstLean.Part262.actualCertificate12243
    BstLean.Part264b.N12243.covarianceEvent12243
    (BstLean.Part263.cell BstLean.Part263.scalarRow12243.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12243)
    BstLean.Part264b.N12243.covarianceEvent12243_measurable BstLean.Part264b.N12243.covarianceEvent12243_payment
    BstLean.Part264b.N12243.frame12243 (fun t c hw hc => ⟨root12243 t c hw hc⟩)
    BstLean.Part262.allocation12243 compatible12243

theorem energy12244 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12244.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12244, BstLean.Part263.cell12244]

noncomputable def root12244 (t : ℝ) (c : Ret 12244)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12244 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12244) :
    BstLean.Part243.RootInputs 12244 t c BstLean.Part259.agent12244.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12244
    BstLean.Part264b.N12244.sourceNumerics12244
    (by norm_num [BstLean.Part263.scalarRow12244])
    (by norm_num [BstLean.Part263.scalarRow12244])
    (by norm_num [BstLean.Part263.scalarRow12244])
    energy12244 BstLean.Part262.actualCertificate12244 t c hw hc

noncomputable def master12244 :
    MasterCertificate 12244 (BstLean.Part260.worldParameters 12244) BstLean.Part259.agent12244 := by
  rw [BstLean.Part260.parameters12244]
  exact BstLean.Part261.master12244

theorem compatible12244 : BstLean.Part259.agent12244.charge ≤ master12244.retainedCharge := by
  change BstLean.Part259.agent12244.charge ≤ BstLean.Part261.master12244.retainedCharge
  rw [show BstLean.Part261.master12244.retainedCharge =
    BstLean.Part259.scalar12244.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12244]
  norm_num [BstLean.Part259.agent12244, BstLean.Part259.scalar12244]

noncomputable def row12244 : BstLean.Part259.RowInputs 12244 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12244
    master12244 BstLean.Part262.actualCertificate12244
    BstLean.Part264b.N12244.covarianceEvent12244
    (BstLean.Part263.cell BstLean.Part263.scalarRow12244.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12244)
    BstLean.Part264b.N12244.covarianceEvent12244_measurable BstLean.Part264b.N12244.covarianceEvent12244_payment
    BstLean.Part264b.N12244.frame12244 (fun t c hw hc => ⟨root12244 t c hw hc⟩)
    BstLean.Part262.allocation12244 compatible12244

theorem energy12245 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12245.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12245, BstLean.Part263.cell12245]

noncomputable def root12245 (t : ℝ) (c : Ret 12245)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12245 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12245) :
    BstLean.Part243.RootInputs 12245 t c BstLean.Part259.agent12245.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12245
    BstLean.Part264b.N12245.sourceNumerics12245
    (by norm_num [BstLean.Part263.scalarRow12245])
    (by norm_num [BstLean.Part263.scalarRow12245])
    (by norm_num [BstLean.Part263.scalarRow12245])
    energy12245 BstLean.Part262.actualCertificate12245 t c hw hc

noncomputable def master12245 :
    MasterCertificate 12245 (BstLean.Part260.worldParameters 12245) BstLean.Part259.agent12245 := by
  rw [BstLean.Part260.parameters12245]
  exact BstLean.Part261.master12245

theorem compatible12245 : BstLean.Part259.agent12245.charge ≤ master12245.retainedCharge := by
  change BstLean.Part259.agent12245.charge ≤ BstLean.Part261.master12245.retainedCharge
  rw [show BstLean.Part261.master12245.retainedCharge =
    BstLean.Part259.scalar12245.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12245]
  norm_num [BstLean.Part259.agent12245, BstLean.Part259.scalar12245]

noncomputable def row12245 : BstLean.Part259.RowInputs 12245 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12245
    master12245 BstLean.Part262.actualCertificate12245
    BstLean.Part264b.N12245.covarianceEvent12245
    (BstLean.Part263.cell BstLean.Part263.scalarRow12245.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12245)
    BstLean.Part264b.N12245.covarianceEvent12245_measurable BstLean.Part264b.N12245.covarianceEvent12245_payment
    BstLean.Part264b.N12245.frame12245 (fun t c hw hc => ⟨root12245 t c hw hc⟩)
    BstLean.Part262.allocation12245 compatible12245

theorem energy12246 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12246.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12246, BstLean.Part263.cell12246]

noncomputable def root12246 (t : ℝ) (c : Ret 12246)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12246 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12246) :
    BstLean.Part243.RootInputs 12246 t c BstLean.Part259.agent12246.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12246
    BstLean.Part264b.N12246.sourceNumerics12246
    (by norm_num [BstLean.Part263.scalarRow12246])
    (by norm_num [BstLean.Part263.scalarRow12246])
    (by norm_num [BstLean.Part263.scalarRow12246])
    energy12246 BstLean.Part262.actualCertificate12246 t c hw hc

noncomputable def master12246 :
    MasterCertificate 12246 (BstLean.Part260.worldParameters 12246) BstLean.Part259.agent12246 := by
  rw [BstLean.Part260.parameters12246]
  exact BstLean.Part261.master12246

theorem compatible12246 : BstLean.Part259.agent12246.charge ≤ master12246.retainedCharge := by
  change BstLean.Part259.agent12246.charge ≤ BstLean.Part261.master12246.retainedCharge
  rw [show BstLean.Part261.master12246.retainedCharge =
    BstLean.Part259.scalar12246.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12246]
  norm_num [BstLean.Part259.agent12246, BstLean.Part259.scalar12246]

noncomputable def row12246 : BstLean.Part259.RowInputs 12246 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12246
    master12246 BstLean.Part262.actualCertificate12246
    BstLean.Part264b.N12246.covarianceEvent12246
    (BstLean.Part263.cell BstLean.Part263.scalarRow12246.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12246)
    BstLean.Part264b.N12246.covarianceEvent12246_measurable BstLean.Part264b.N12246.covarianceEvent12246_payment
    BstLean.Part264b.N12246.frame12246 (fun t c hw hc => ⟨root12246 t c hw hc⟩)
    BstLean.Part262.allocation12246 compatible12246

theorem energy12247 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12247.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12247, BstLean.Part263.cell12247]

noncomputable def root12247 (t : ℝ) (c : Ret 12247)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12247 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12247) :
    BstLean.Part243.RootInputs 12247 t c BstLean.Part259.agent12247.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12247
    BstLean.Part264b.N12247.sourceNumerics12247
    (by norm_num [BstLean.Part263.scalarRow12247])
    (by norm_num [BstLean.Part263.scalarRow12247])
    (by norm_num [BstLean.Part263.scalarRow12247])
    energy12247 BstLean.Part262.actualCertificate12247 t c hw hc

noncomputable def master12247 :
    MasterCertificate 12247 (BstLean.Part260.worldParameters 12247) BstLean.Part259.agent12247 := by
  rw [BstLean.Part260.parameters12247]
  exact BstLean.Part261.master12247

theorem compatible12247 : BstLean.Part259.agent12247.charge ≤ master12247.retainedCharge := by
  change BstLean.Part259.agent12247.charge ≤ BstLean.Part261.master12247.retainedCharge
  rw [show BstLean.Part261.master12247.retainedCharge =
    BstLean.Part259.scalar12247.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12247]
  norm_num [BstLean.Part259.agent12247, BstLean.Part259.scalar12247]

noncomputable def row12247 : BstLean.Part259.RowInputs 12247 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12247
    master12247 BstLean.Part262.actualCertificate12247
    BstLean.Part264b.N12247.covarianceEvent12247
    (BstLean.Part263.cell BstLean.Part263.scalarRow12247.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12247)
    BstLean.Part264b.N12247.covarianceEvent12247_measurable BstLean.Part264b.N12247.covarianceEvent12247_payment
    BstLean.Part264b.N12247.frame12247 (fun t c hw hc => ⟨root12247 t c hw hc⟩)
    BstLean.Part262.allocation12247 compatible12247

theorem energy12248 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12248.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12248, BstLean.Part263.cell12248]

noncomputable def root12248 (t : ℝ) (c : Ret 12248)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12248 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12248) :
    BstLean.Part243.RootInputs 12248 t c BstLean.Part259.agent12248.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12248
    BstLean.Part264b.N12248.sourceNumerics12248
    (by norm_num [BstLean.Part263.scalarRow12248])
    (by norm_num [BstLean.Part263.scalarRow12248])
    (by norm_num [BstLean.Part263.scalarRow12248])
    energy12248 BstLean.Part262.actualCertificate12248 t c hw hc

noncomputable def master12248 :
    MasterCertificate 12248 (BstLean.Part260.worldParameters 12248) BstLean.Part259.agent12248 := by
  rw [BstLean.Part260.parameters12248]
  exact BstLean.Part261.master12248

theorem compatible12248 : BstLean.Part259.agent12248.charge ≤ master12248.retainedCharge := by
  change BstLean.Part259.agent12248.charge ≤ BstLean.Part261.master12248.retainedCharge
  rw [show BstLean.Part261.master12248.retainedCharge =
    BstLean.Part259.scalar12248.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12248]
  norm_num [BstLean.Part259.agent12248, BstLean.Part259.scalar12248]

noncomputable def row12248 : BstLean.Part259.RowInputs 12248 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12248
    master12248 BstLean.Part262.actualCertificate12248
    BstLean.Part264b.N12248.covarianceEvent12248
    (BstLean.Part263.cell BstLean.Part263.scalarRow12248.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12248)
    BstLean.Part264b.N12248.covarianceEvent12248_measurable BstLean.Part264b.N12248.covarianceEvent12248_payment
    BstLean.Part264b.N12248.frame12248 (fun t c hw hc => ⟨root12248 t c hw hc⟩)
    BstLean.Part262.allocation12248 compatible12248

theorem energy12249 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12249.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12249, BstLean.Part263.cell12249]

noncomputable def root12249 (t : ℝ) (c : Ret 12249)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12249 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12249) :
    BstLean.Part243.RootInputs 12249 t c BstLean.Part259.agent12249.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12249
    BstLean.Part264b.N12249.sourceNumerics12249
    (by norm_num [BstLean.Part263.scalarRow12249])
    (by norm_num [BstLean.Part263.scalarRow12249])
    (by norm_num [BstLean.Part263.scalarRow12249])
    energy12249 BstLean.Part262.actualCertificate12249 t c hw hc

noncomputable def master12249 :
    MasterCertificate 12249 (BstLean.Part260.worldParameters 12249) BstLean.Part259.agent12249 := by
  rw [BstLean.Part260.parameters12249]
  exact BstLean.Part261.master12249

theorem compatible12249 : BstLean.Part259.agent12249.charge ≤ master12249.retainedCharge := by
  change BstLean.Part259.agent12249.charge ≤ BstLean.Part261.master12249.retainedCharge
  rw [show BstLean.Part261.master12249.retainedCharge =
    BstLean.Part259.scalar12249.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12249]
  norm_num [BstLean.Part259.agent12249, BstLean.Part259.scalar12249]

noncomputable def row12249 : BstLean.Part259.RowInputs 12249 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12249
    master12249 BstLean.Part262.actualCertificate12249
    BstLean.Part264b.N12249.covarianceEvent12249
    (BstLean.Part263.cell BstLean.Part263.scalarRow12249.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12249)
    BstLean.Part264b.N12249.covarianceEvent12249_measurable BstLean.Part264b.N12249.covarianceEvent12249_payment
    BstLean.Part264b.N12249.frame12249 (fun t c hw hc => ⟨root12249 t c hw hc⟩)
    BstLean.Part262.allocation12249 compatible12249

theorem energy12250 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12250.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12250, BstLean.Part263.cell12250]

noncomputable def root12250 (t : ℝ) (c : Ret 12250)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12250 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12250) :
    BstLean.Part243.RootInputs 12250 t c BstLean.Part259.agent12250.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12250
    BstLean.Part264b.N12250.sourceNumerics12250
    (by norm_num [BstLean.Part263.scalarRow12250])
    (by norm_num [BstLean.Part263.scalarRow12250])
    (by norm_num [BstLean.Part263.scalarRow12250])
    energy12250 BstLean.Part262.actualCertificate12250 t c hw hc

noncomputable def master12250 :
    MasterCertificate 12250 (BstLean.Part260.worldParameters 12250) BstLean.Part259.agent12250 := by
  rw [BstLean.Part260.parameters12250]
  exact BstLean.Part261.master12250

theorem compatible12250 : BstLean.Part259.agent12250.charge ≤ master12250.retainedCharge := by
  change BstLean.Part259.agent12250.charge ≤ BstLean.Part261.master12250.retainedCharge
  rw [show BstLean.Part261.master12250.retainedCharge =
    BstLean.Part259.scalar12250.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12250]
  norm_num [BstLean.Part259.agent12250, BstLean.Part259.scalar12250]

noncomputable def row12250 : BstLean.Part259.RowInputs 12250 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12250
    master12250 BstLean.Part262.actualCertificate12250
    BstLean.Part264b.N12250.covarianceEvent12250
    (BstLean.Part263.cell BstLean.Part263.scalarRow12250.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12250)
    BstLean.Part264b.N12250.covarianceEvent12250_measurable BstLean.Part264b.N12250.covarianceEvent12250_payment
    BstLean.Part264b.N12250.frame12250 (fun t c hw hc => ⟨root12250 t c hw hc⟩)
    BstLean.Part262.allocation12250 compatible12250

theorem energy12251 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12251.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12251, BstLean.Part263.cell12251]

noncomputable def root12251 (t : ℝ) (c : Ret 12251)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12251 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12251) :
    BstLean.Part243.RootInputs 12251 t c BstLean.Part259.agent12251.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12251
    BstLean.Part264b.N12251.sourceNumerics12251
    (by norm_num [BstLean.Part263.scalarRow12251])
    (by norm_num [BstLean.Part263.scalarRow12251])
    (by norm_num [BstLean.Part263.scalarRow12251])
    energy12251 BstLean.Part262.actualCertificate12251 t c hw hc

noncomputable def master12251 :
    MasterCertificate 12251 (BstLean.Part260.worldParameters 12251) BstLean.Part259.agent12251 := by
  rw [BstLean.Part260.parameters12251]
  exact BstLean.Part261.master12251

theorem compatible12251 : BstLean.Part259.agent12251.charge ≤ master12251.retainedCharge := by
  change BstLean.Part259.agent12251.charge ≤ BstLean.Part261.master12251.retainedCharge
  rw [show BstLean.Part261.master12251.retainedCharge =
    BstLean.Part259.scalar12251.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12251]
  norm_num [BstLean.Part259.agent12251, BstLean.Part259.scalar12251]

noncomputable def row12251 : BstLean.Part259.RowInputs 12251 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12251
    master12251 BstLean.Part262.actualCertificate12251
    BstLean.Part264b.N12251.covarianceEvent12251
    (BstLean.Part263.cell BstLean.Part263.scalarRow12251.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12251)
    BstLean.Part264b.N12251.covarianceEvent12251_measurable BstLean.Part264b.N12251.covarianceEvent12251_payment
    BstLean.Part264b.N12251.frame12251 (fun t c hw hc => ⟨root12251 t c hw hc⟩)
    BstLean.Part262.allocation12251 compatible12251

theorem energy12252 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12252.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12252, BstLean.Part263.cell12252]

noncomputable def root12252 (t : ℝ) (c : Ret 12252)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12252 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12252) :
    BstLean.Part243.RootInputs 12252 t c BstLean.Part259.agent12252.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12252
    BstLean.Part264b.N12252.sourceNumerics12252
    (by norm_num [BstLean.Part263.scalarRow12252])
    (by norm_num [BstLean.Part263.scalarRow12252])
    (by norm_num [BstLean.Part263.scalarRow12252])
    energy12252 BstLean.Part262.actualCertificate12252 t c hw hc

noncomputable def master12252 :
    MasterCertificate 12252 (BstLean.Part260.worldParameters 12252) BstLean.Part259.agent12252 := by
  rw [BstLean.Part260.parameters12252]
  exact BstLean.Part261.master12252

theorem compatible12252 : BstLean.Part259.agent12252.charge ≤ master12252.retainedCharge := by
  change BstLean.Part259.agent12252.charge ≤ BstLean.Part261.master12252.retainedCharge
  rw [show BstLean.Part261.master12252.retainedCharge =
    BstLean.Part259.scalar12252.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12252]
  norm_num [BstLean.Part259.agent12252, BstLean.Part259.scalar12252]

noncomputable def row12252 : BstLean.Part259.RowInputs 12252 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12252
    master12252 BstLean.Part262.actualCertificate12252
    BstLean.Part264b.N12252.covarianceEvent12252
    (BstLean.Part263.cell BstLean.Part263.scalarRow12252.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12252)
    BstLean.Part264b.N12252.covarianceEvent12252_measurable BstLean.Part264b.N12252.covarianceEvent12252_payment
    BstLean.Part264b.N12252.frame12252 (fun t c hw hc => ⟨root12252 t c hw hc⟩)
    BstLean.Part262.allocation12252 compatible12252

theorem energy12253 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12253.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12253, BstLean.Part263.cell12253]

noncomputable def root12253 (t : ℝ) (c : Ret 12253)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12253 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12253) :
    BstLean.Part243.RootInputs 12253 t c BstLean.Part259.agent12253.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12253
    BstLean.Part264b.N12253.sourceNumerics12253
    (by norm_num [BstLean.Part263.scalarRow12253])
    (by norm_num [BstLean.Part263.scalarRow12253])
    (by norm_num [BstLean.Part263.scalarRow12253])
    energy12253 BstLean.Part262.actualCertificate12253 t c hw hc

noncomputable def master12253 :
    MasterCertificate 12253 (BstLean.Part260.worldParameters 12253) BstLean.Part259.agent12253 := by
  rw [BstLean.Part260.parameters12253]
  exact BstLean.Part261.master12253

theorem compatible12253 : BstLean.Part259.agent12253.charge ≤ master12253.retainedCharge := by
  change BstLean.Part259.agent12253.charge ≤ BstLean.Part261.master12253.retainedCharge
  rw [show BstLean.Part261.master12253.retainedCharge =
    BstLean.Part259.scalar12253.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12253]
  norm_num [BstLean.Part259.agent12253, BstLean.Part259.scalar12253]

noncomputable def row12253 : BstLean.Part259.RowInputs 12253 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12253
    master12253 BstLean.Part262.actualCertificate12253
    BstLean.Part264b.N12253.covarianceEvent12253
    (BstLean.Part263.cell BstLean.Part263.scalarRow12253.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12253)
    BstLean.Part264b.N12253.covarianceEvent12253_measurable BstLean.Part264b.N12253.covarianceEvent12253_payment
    BstLean.Part264b.N12253.frame12253 (fun t c hw hc => ⟨root12253 t c hw hc⟩)
    BstLean.Part262.allocation12253 compatible12253

end BstLean.Part267
