import BstLean.Part267Bridge
import BstLean.Part264bFamily
import BstLean.Part261Coverage
import BstLean.Part262ActualCoverage

namespace BstLean.Part267
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part192 BstLean.Part196

theorem energy12278 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12278.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12278, BstLean.Part263.cell12278]

noncomputable def root12278 (t : ℝ) (c : Ret 12278)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12278 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12278) :
    BstLean.Part243.RootInputs 12278 t c BstLean.Part259.agent12278.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12278
    BstLean.Part264b.N12278.sourceNumerics12278
    (by norm_num [BstLean.Part263.scalarRow12278])
    (by norm_num [BstLean.Part263.scalarRow12278])
    (by norm_num [BstLean.Part263.scalarRow12278])
    energy12278 BstLean.Part262.actualCertificate12278 t c hw hc

noncomputable def master12278 :
    MasterCertificate 12278 (BstLean.Part260.worldParameters 12278) BstLean.Part259.agent12278 := by
  rw [BstLean.Part260.parameters12278]
  exact BstLean.Part261.master12278

theorem compatible12278 : BstLean.Part259.agent12278.charge ≤ master12278.retainedCharge := by
  change BstLean.Part259.agent12278.charge ≤ BstLean.Part261.master12278.retainedCharge
  rw [show BstLean.Part261.master12278.retainedCharge =
    BstLean.Part259.scalar12278.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12278]
  norm_num [BstLean.Part259.agent12278, BstLean.Part259.scalar12278]

noncomputable def row12278 : BstLean.Part259.RowInputs 12278 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12278
    master12278 BstLean.Part262.actualCertificate12278
    BstLean.Part264b.N12278.covarianceEvent12278
    (BstLean.Part263.cell BstLean.Part263.scalarRow12278.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12278)
    BstLean.Part264b.N12278.covarianceEvent12278_measurable BstLean.Part264b.N12278.covarianceEvent12278_payment
    BstLean.Part264b.N12278.frame12278 (fun t c hw hc => ⟨root12278 t c hw hc⟩)
    BstLean.Part262.allocation12278 compatible12278

theorem energy12279 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12279.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12279, BstLean.Part263.cell12279]

noncomputable def root12279 (t : ℝ) (c : Ret 12279)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12279 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12279) :
    BstLean.Part243.RootInputs 12279 t c BstLean.Part259.agent12279.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12279
    BstLean.Part264b.N12279.sourceNumerics12279
    (by norm_num [BstLean.Part263.scalarRow12279])
    (by norm_num [BstLean.Part263.scalarRow12279])
    (by norm_num [BstLean.Part263.scalarRow12279])
    energy12279 BstLean.Part262.actualCertificate12279 t c hw hc

noncomputable def master12279 :
    MasterCertificate 12279 (BstLean.Part260.worldParameters 12279) BstLean.Part259.agent12279 := by
  rw [BstLean.Part260.parameters12279]
  exact BstLean.Part261.master12279

theorem compatible12279 : BstLean.Part259.agent12279.charge ≤ master12279.retainedCharge := by
  change BstLean.Part259.agent12279.charge ≤ BstLean.Part261.master12279.retainedCharge
  rw [show BstLean.Part261.master12279.retainedCharge =
    BstLean.Part259.scalar12279.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12279]
  norm_num [BstLean.Part259.agent12279, BstLean.Part259.scalar12279]

noncomputable def row12279 : BstLean.Part259.RowInputs 12279 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12279
    master12279 BstLean.Part262.actualCertificate12279
    BstLean.Part264b.N12279.covarianceEvent12279
    (BstLean.Part263.cell BstLean.Part263.scalarRow12279.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12279)
    BstLean.Part264b.N12279.covarianceEvent12279_measurable BstLean.Part264b.N12279.covarianceEvent12279_payment
    BstLean.Part264b.N12279.frame12279 (fun t c hw hc => ⟨root12279 t c hw hc⟩)
    BstLean.Part262.allocation12279 compatible12279

theorem energy12280 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12280.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12280, BstLean.Part263.cell12280]

noncomputable def root12280 (t : ℝ) (c : Ret 12280)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12280 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12280) :
    BstLean.Part243.RootInputs 12280 t c BstLean.Part259.agent12280.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12280
    BstLean.Part264b.N12280.sourceNumerics12280
    (by norm_num [BstLean.Part263.scalarRow12280])
    (by norm_num [BstLean.Part263.scalarRow12280])
    (by norm_num [BstLean.Part263.scalarRow12280])
    energy12280 BstLean.Part262.actualCertificate12280 t c hw hc

noncomputable def master12280 :
    MasterCertificate 12280 (BstLean.Part260.worldParameters 12280) BstLean.Part259.agent12280 := by
  rw [BstLean.Part260.parameters12280]
  exact BstLean.Part261.master12280

theorem compatible12280 : BstLean.Part259.agent12280.charge ≤ master12280.retainedCharge := by
  change BstLean.Part259.agent12280.charge ≤ BstLean.Part261.master12280.retainedCharge
  rw [show BstLean.Part261.master12280.retainedCharge =
    BstLean.Part259.scalar12280.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12280]
  norm_num [BstLean.Part259.agent12280, BstLean.Part259.scalar12280]

noncomputable def row12280 : BstLean.Part259.RowInputs 12280 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12280
    master12280 BstLean.Part262.actualCertificate12280
    BstLean.Part264b.N12280.covarianceEvent12280
    (BstLean.Part263.cell BstLean.Part263.scalarRow12280.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12280)
    BstLean.Part264b.N12280.covarianceEvent12280_measurable BstLean.Part264b.N12280.covarianceEvent12280_payment
    BstLean.Part264b.N12280.frame12280 (fun t c hw hc => ⟨root12280 t c hw hc⟩)
    BstLean.Part262.allocation12280 compatible12280

theorem energy12281 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12281.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12281, BstLean.Part263.cell12281]

noncomputable def root12281 (t : ℝ) (c : Ret 12281)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12281 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12281) :
    BstLean.Part243.RootInputs 12281 t c BstLean.Part259.agent12281.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12281
    BstLean.Part264b.N12281.sourceNumerics12281
    (by norm_num [BstLean.Part263.scalarRow12281])
    (by norm_num [BstLean.Part263.scalarRow12281])
    (by norm_num [BstLean.Part263.scalarRow12281])
    energy12281 BstLean.Part262.actualCertificate12281 t c hw hc

noncomputable def master12281 :
    MasterCertificate 12281 (BstLean.Part260.worldParameters 12281) BstLean.Part259.agent12281 := by
  rw [BstLean.Part260.parameters12281]
  exact BstLean.Part261.master12281

theorem compatible12281 : BstLean.Part259.agent12281.charge ≤ master12281.retainedCharge := by
  change BstLean.Part259.agent12281.charge ≤ BstLean.Part261.master12281.retainedCharge
  rw [show BstLean.Part261.master12281.retainedCharge =
    BstLean.Part259.scalar12281.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12281]
  norm_num [BstLean.Part259.agent12281, BstLean.Part259.scalar12281]

noncomputable def row12281 : BstLean.Part259.RowInputs 12281 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12281
    master12281 BstLean.Part262.actualCertificate12281
    BstLean.Part264b.N12281.covarianceEvent12281
    (BstLean.Part263.cell BstLean.Part263.scalarRow12281.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12281)
    BstLean.Part264b.N12281.covarianceEvent12281_measurable BstLean.Part264b.N12281.covarianceEvent12281_payment
    BstLean.Part264b.N12281.frame12281 (fun t c hw hc => ⟨root12281 t c hw hc⟩)
    BstLean.Part262.allocation12281 compatible12281

theorem energy12282 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12282.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12282, BstLean.Part263.cell12282]

noncomputable def root12282 (t : ℝ) (c : Ret 12282)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12282 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12282) :
    BstLean.Part243.RootInputs 12282 t c BstLean.Part259.agent12282.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12282
    BstLean.Part264b.N12282.sourceNumerics12282
    (by norm_num [BstLean.Part263.scalarRow12282])
    (by norm_num [BstLean.Part263.scalarRow12282])
    (by norm_num [BstLean.Part263.scalarRow12282])
    energy12282 BstLean.Part262.actualCertificate12282 t c hw hc

noncomputable def master12282 :
    MasterCertificate 12282 (BstLean.Part260.worldParameters 12282) BstLean.Part259.agent12282 := by
  rw [BstLean.Part260.parameters12282]
  exact BstLean.Part261.master12282

theorem compatible12282 : BstLean.Part259.agent12282.charge ≤ master12282.retainedCharge := by
  change BstLean.Part259.agent12282.charge ≤ BstLean.Part261.master12282.retainedCharge
  rw [show BstLean.Part261.master12282.retainedCharge =
    BstLean.Part259.scalar12282.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12282]
  norm_num [BstLean.Part259.agent12282, BstLean.Part259.scalar12282]

noncomputable def row12282 : BstLean.Part259.RowInputs 12282 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12282
    master12282 BstLean.Part262.actualCertificate12282
    BstLean.Part264b.N12282.covarianceEvent12282
    (BstLean.Part263.cell BstLean.Part263.scalarRow12282.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12282)
    BstLean.Part264b.N12282.covarianceEvent12282_measurable BstLean.Part264b.N12282.covarianceEvent12282_payment
    BstLean.Part264b.N12282.frame12282 (fun t c hw hc => ⟨root12282 t c hw hc⟩)
    BstLean.Part262.allocation12282 compatible12282

theorem energy12283 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12283.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12283, BstLean.Part263.cell12283]

noncomputable def root12283 (t : ℝ) (c : Ret 12283)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12283 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12283) :
    BstLean.Part243.RootInputs 12283 t c BstLean.Part259.agent12283.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12283
    BstLean.Part264b.N12283.sourceNumerics12283
    (by norm_num [BstLean.Part263.scalarRow12283])
    (by norm_num [BstLean.Part263.scalarRow12283])
    (by norm_num [BstLean.Part263.scalarRow12283])
    energy12283 BstLean.Part262.actualCertificate12283 t c hw hc

noncomputable def master12283 :
    MasterCertificate 12283 (BstLean.Part260.worldParameters 12283) BstLean.Part259.agent12283 := by
  rw [BstLean.Part260.parameters12283]
  exact BstLean.Part261.master12283

theorem compatible12283 : BstLean.Part259.agent12283.charge ≤ master12283.retainedCharge := by
  change BstLean.Part259.agent12283.charge ≤ BstLean.Part261.master12283.retainedCharge
  rw [show BstLean.Part261.master12283.retainedCharge =
    BstLean.Part259.scalar12283.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12283]
  norm_num [BstLean.Part259.agent12283, BstLean.Part259.scalar12283]

noncomputable def row12283 : BstLean.Part259.RowInputs 12283 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12283
    master12283 BstLean.Part262.actualCertificate12283
    BstLean.Part264b.N12283.covarianceEvent12283
    (BstLean.Part263.cell BstLean.Part263.scalarRow12283.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12283)
    BstLean.Part264b.N12283.covarianceEvent12283_measurable BstLean.Part264b.N12283.covarianceEvent12283_payment
    BstLean.Part264b.N12283.frame12283 (fun t c hw hc => ⟨root12283 t c hw hc⟩)
    BstLean.Part262.allocation12283 compatible12283

theorem energy12284 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12284.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12284, BstLean.Part263.cell12284]

noncomputable def root12284 (t : ℝ) (c : Ret 12284)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12284 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12284) :
    BstLean.Part243.RootInputs 12284 t c BstLean.Part259.agent12284.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12284
    BstLean.Part264b.N12284.sourceNumerics12284
    (by norm_num [BstLean.Part263.scalarRow12284])
    (by norm_num [BstLean.Part263.scalarRow12284])
    (by norm_num [BstLean.Part263.scalarRow12284])
    energy12284 BstLean.Part262.actualCertificate12284 t c hw hc

noncomputable def master12284 :
    MasterCertificate 12284 (BstLean.Part260.worldParameters 12284) BstLean.Part259.agent12284 := by
  rw [BstLean.Part260.parameters12284]
  exact BstLean.Part261.master12284

theorem compatible12284 : BstLean.Part259.agent12284.charge ≤ master12284.retainedCharge := by
  change BstLean.Part259.agent12284.charge ≤ BstLean.Part261.master12284.retainedCharge
  rw [show BstLean.Part261.master12284.retainedCharge =
    BstLean.Part259.scalar12284.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12284]
  norm_num [BstLean.Part259.agent12284, BstLean.Part259.scalar12284]

noncomputable def row12284 : BstLean.Part259.RowInputs 12284 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12284
    master12284 BstLean.Part262.actualCertificate12284
    BstLean.Part264b.N12284.covarianceEvent12284
    (BstLean.Part263.cell BstLean.Part263.scalarRow12284.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12284)
    BstLean.Part264b.N12284.covarianceEvent12284_measurable BstLean.Part264b.N12284.covarianceEvent12284_payment
    BstLean.Part264b.N12284.frame12284 (fun t c hw hc => ⟨root12284 t c hw hc⟩)
    BstLean.Part262.allocation12284 compatible12284

theorem energy12285 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12285.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12285, BstLean.Part263.cell12285]

noncomputable def root12285 (t : ℝ) (c : Ret 12285)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12285 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12285) :
    BstLean.Part243.RootInputs 12285 t c BstLean.Part259.agent12285.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12285
    BstLean.Part264b.N12285.sourceNumerics12285
    (by norm_num [BstLean.Part263.scalarRow12285])
    (by norm_num [BstLean.Part263.scalarRow12285])
    (by norm_num [BstLean.Part263.scalarRow12285])
    energy12285 BstLean.Part262.actualCertificate12285 t c hw hc

noncomputable def master12285 :
    MasterCertificate 12285 (BstLean.Part260.worldParameters 12285) BstLean.Part259.agent12285 := by
  rw [BstLean.Part260.parameters12285]
  exact BstLean.Part261.master12285

theorem compatible12285 : BstLean.Part259.agent12285.charge ≤ master12285.retainedCharge := by
  change BstLean.Part259.agent12285.charge ≤ BstLean.Part261.master12285.retainedCharge
  rw [show BstLean.Part261.master12285.retainedCharge =
    BstLean.Part259.scalar12285.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12285]
  norm_num [BstLean.Part259.agent12285, BstLean.Part259.scalar12285]

noncomputable def row12285 : BstLean.Part259.RowInputs 12285 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12285
    master12285 BstLean.Part262.actualCertificate12285
    BstLean.Part264b.N12285.covarianceEvent12285
    (BstLean.Part263.cell BstLean.Part263.scalarRow12285.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12285)
    BstLean.Part264b.N12285.covarianceEvent12285_measurable BstLean.Part264b.N12285.covarianceEvent12285_payment
    BstLean.Part264b.N12285.frame12285 (fun t c hw hc => ⟨root12285 t c hw hc⟩)
    BstLean.Part262.allocation12285 compatible12285

theorem energy12286 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12286.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12286, BstLean.Part263.cell12286]

noncomputable def root12286 (t : ℝ) (c : Ret 12286)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12286 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12286) :
    BstLean.Part243.RootInputs 12286 t c BstLean.Part259.agent12286.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12286
    BstLean.Part264b.N12286.sourceNumerics12286
    (by norm_num [BstLean.Part263.scalarRow12286])
    (by norm_num [BstLean.Part263.scalarRow12286])
    (by norm_num [BstLean.Part263.scalarRow12286])
    energy12286 BstLean.Part262.actualCertificate12286 t c hw hc

noncomputable def master12286 :
    MasterCertificate 12286 (BstLean.Part260.worldParameters 12286) BstLean.Part259.agent12286 := by
  rw [BstLean.Part260.parameters12286]
  exact BstLean.Part261.master12286

theorem compatible12286 : BstLean.Part259.agent12286.charge ≤ master12286.retainedCharge := by
  change BstLean.Part259.agent12286.charge ≤ BstLean.Part261.master12286.retainedCharge
  rw [show BstLean.Part261.master12286.retainedCharge =
    BstLean.Part259.scalar12286.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12286]
  norm_num [BstLean.Part259.agent12286, BstLean.Part259.scalar12286]

noncomputable def row12286 : BstLean.Part259.RowInputs 12286 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12286
    master12286 BstLean.Part262.actualCertificate12286
    BstLean.Part264b.N12286.covarianceEvent12286
    (BstLean.Part263.cell BstLean.Part263.scalarRow12286.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12286)
    BstLean.Part264b.N12286.covarianceEvent12286_measurable BstLean.Part264b.N12286.covarianceEvent12286_payment
    BstLean.Part264b.N12286.frame12286 (fun t c hw hc => ⟨root12286 t c hw hc⟩)
    BstLean.Part262.allocation12286 compatible12286

theorem energy12287 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12287.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12287, BstLean.Part263.cell12287]

noncomputable def root12287 (t : ℝ) (c : Ret 12287)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12287 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12287) :
    BstLean.Part243.RootInputs 12287 t c BstLean.Part259.agent12287.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12287
    BstLean.Part264b.N12287.sourceNumerics12287
    (by norm_num [BstLean.Part263.scalarRow12287])
    (by norm_num [BstLean.Part263.scalarRow12287])
    (by norm_num [BstLean.Part263.scalarRow12287])
    energy12287 BstLean.Part262.actualCertificate12287 t c hw hc

noncomputable def master12287 :
    MasterCertificate 12287 (BstLean.Part260.worldParameters 12287) BstLean.Part259.agent12287 := by
  rw [BstLean.Part260.parameters12287]
  exact BstLean.Part261.master12287

theorem compatible12287 : BstLean.Part259.agent12287.charge ≤ master12287.retainedCharge := by
  change BstLean.Part259.agent12287.charge ≤ BstLean.Part261.master12287.retainedCharge
  rw [show BstLean.Part261.master12287.retainedCharge =
    BstLean.Part259.scalar12287.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12287]
  norm_num [BstLean.Part259.agent12287, BstLean.Part259.scalar12287]

noncomputable def row12287 : BstLean.Part259.RowInputs 12287 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12287
    master12287 BstLean.Part262.actualCertificate12287
    BstLean.Part264b.N12287.covarianceEvent12287
    (BstLean.Part263.cell BstLean.Part263.scalarRow12287.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12287)
    BstLean.Part264b.N12287.covarianceEvent12287_measurable BstLean.Part264b.N12287.covarianceEvent12287_payment
    BstLean.Part264b.N12287.frame12287 (fun t c hw hc => ⟨root12287 t c hw hc⟩)
    BstLean.Part262.allocation12287 compatible12287

theorem energy12288 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12288.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12288, BstLean.Part263.cell12288]

noncomputable def root12288 (t : ℝ) (c : Ret 12288)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12288 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12288) :
    BstLean.Part243.RootInputs 12288 t c BstLean.Part259.agent12288.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12288
    BstLean.Part264b.N12288.sourceNumerics12288
    (by norm_num [BstLean.Part263.scalarRow12288])
    (by norm_num [BstLean.Part263.scalarRow12288])
    (by norm_num [BstLean.Part263.scalarRow12288])
    energy12288 BstLean.Part262.actualCertificate12288 t c hw hc

noncomputable def master12288 :
    MasterCertificate 12288 (BstLean.Part260.worldParameters 12288) BstLean.Part259.agent12288 := by
  rw [BstLean.Part260.parameters12288]
  exact BstLean.Part261.master12288

theorem compatible12288 : BstLean.Part259.agent12288.charge ≤ master12288.retainedCharge := by
  change BstLean.Part259.agent12288.charge ≤ BstLean.Part261.master12288.retainedCharge
  rw [show BstLean.Part261.master12288.retainedCharge =
    BstLean.Part259.scalar12288.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12288]
  norm_num [BstLean.Part259.agent12288, BstLean.Part259.scalar12288]

noncomputable def row12288 : BstLean.Part259.RowInputs 12288 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12288
    master12288 BstLean.Part262.actualCertificate12288
    BstLean.Part264b.N12288.covarianceEvent12288
    (BstLean.Part263.cell BstLean.Part263.scalarRow12288.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12288)
    BstLean.Part264b.N12288.covarianceEvent12288_measurable BstLean.Part264b.N12288.covarianceEvent12288_payment
    BstLean.Part264b.N12288.frame12288 (fun t c hw hc => ⟨root12288 t c hw hc⟩)
    BstLean.Part262.allocation12288 compatible12288

theorem energy12289 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12289.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12289, BstLean.Part263.cell12289]

noncomputable def root12289 (t : ℝ) (c : Ret 12289)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12289 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12289) :
    BstLean.Part243.RootInputs 12289 t c BstLean.Part259.agent12289.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12289
    BstLean.Part264b.N12289.sourceNumerics12289
    (by norm_num [BstLean.Part263.scalarRow12289])
    (by norm_num [BstLean.Part263.scalarRow12289])
    (by norm_num [BstLean.Part263.scalarRow12289])
    energy12289 BstLean.Part262.actualCertificate12289 t c hw hc

noncomputable def master12289 :
    MasterCertificate 12289 (BstLean.Part260.worldParameters 12289) BstLean.Part259.agent12289 := by
  rw [BstLean.Part260.parameters12289]
  exact BstLean.Part261.master12289

theorem compatible12289 : BstLean.Part259.agent12289.charge ≤ master12289.retainedCharge := by
  change BstLean.Part259.agent12289.charge ≤ BstLean.Part261.master12289.retainedCharge
  rw [show BstLean.Part261.master12289.retainedCharge =
    BstLean.Part259.scalar12289.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12289]
  norm_num [BstLean.Part259.agent12289, BstLean.Part259.scalar12289]

noncomputable def row12289 : BstLean.Part259.RowInputs 12289 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12289
    master12289 BstLean.Part262.actualCertificate12289
    BstLean.Part264b.N12289.covarianceEvent12289
    (BstLean.Part263.cell BstLean.Part263.scalarRow12289.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12289)
    BstLean.Part264b.N12289.covarianceEvent12289_measurable BstLean.Part264b.N12289.covarianceEvent12289_payment
    BstLean.Part264b.N12289.frame12289 (fun t c hw hc => ⟨root12289 t c hw hc⟩)
    BstLean.Part262.allocation12289 compatible12289

theorem energy12290 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12290.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12290, BstLean.Part263.cell12290]

noncomputable def root12290 (t : ℝ) (c : Ret 12290)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12290 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12290) :
    BstLean.Part243.RootInputs 12290 t c BstLean.Part259.agent12290.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12290
    BstLean.Part264b.N12290.sourceNumerics12290
    (by norm_num [BstLean.Part263.scalarRow12290])
    (by norm_num [BstLean.Part263.scalarRow12290])
    (by norm_num [BstLean.Part263.scalarRow12290])
    energy12290 BstLean.Part262.actualCertificate12290 t c hw hc

noncomputable def master12290 :
    MasterCertificate 12290 (BstLean.Part260.worldParameters 12290) BstLean.Part259.agent12290 := by
  rw [BstLean.Part260.parameters12290]
  exact BstLean.Part261.master12290

theorem compatible12290 : BstLean.Part259.agent12290.charge ≤ master12290.retainedCharge := by
  change BstLean.Part259.agent12290.charge ≤ BstLean.Part261.master12290.retainedCharge
  rw [show BstLean.Part261.master12290.retainedCharge =
    BstLean.Part259.scalar12290.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12290]
  norm_num [BstLean.Part259.agent12290, BstLean.Part259.scalar12290]

noncomputable def row12290 : BstLean.Part259.RowInputs 12290 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12290
    master12290 BstLean.Part262.actualCertificate12290
    BstLean.Part264b.N12290.covarianceEvent12290
    (BstLean.Part263.cell BstLean.Part263.scalarRow12290.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12290)
    BstLean.Part264b.N12290.covarianceEvent12290_measurable BstLean.Part264b.N12290.covarianceEvent12290_payment
    BstLean.Part264b.N12290.frame12290 (fun t c hw hc => ⟨root12290 t c hw hc⟩)
    BstLean.Part262.allocation12290 compatible12290

theorem energy12291 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12291.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12291, BstLean.Part263.cell12291]

noncomputable def root12291 (t : ℝ) (c : Ret 12291)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12291 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12291) :
    BstLean.Part243.RootInputs 12291 t c BstLean.Part259.agent12291.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12291
    BstLean.Part264b.N12291.sourceNumerics12291
    (by norm_num [BstLean.Part263.scalarRow12291])
    (by norm_num [BstLean.Part263.scalarRow12291])
    (by norm_num [BstLean.Part263.scalarRow12291])
    energy12291 BstLean.Part262.actualCertificate12291 t c hw hc

noncomputable def master12291 :
    MasterCertificate 12291 (BstLean.Part260.worldParameters 12291) BstLean.Part259.agent12291 := by
  rw [BstLean.Part260.parameters12291]
  exact BstLean.Part261.master12291

theorem compatible12291 : BstLean.Part259.agent12291.charge ≤ master12291.retainedCharge := by
  change BstLean.Part259.agent12291.charge ≤ BstLean.Part261.master12291.retainedCharge
  rw [show BstLean.Part261.master12291.retainedCharge =
    BstLean.Part259.scalar12291.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12291]
  norm_num [BstLean.Part259.agent12291, BstLean.Part259.scalar12291]

noncomputable def row12291 : BstLean.Part259.RowInputs 12291 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12291
    master12291 BstLean.Part262.actualCertificate12291
    BstLean.Part264b.N12291.covarianceEvent12291
    (BstLean.Part263.cell BstLean.Part263.scalarRow12291.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12291)
    BstLean.Part264b.N12291.covarianceEvent12291_measurable BstLean.Part264b.N12291.covarianceEvent12291_payment
    BstLean.Part264b.N12291.frame12291 (fun t c hw hc => ⟨root12291 t c hw hc⟩)
    BstLean.Part262.allocation12291 compatible12291

theorem energy12292 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12292.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12292, BstLean.Part263.cell12292]

noncomputable def root12292 (t : ℝ) (c : Ret 12292)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12292 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12292) :
    BstLean.Part243.RootInputs 12292 t c BstLean.Part259.agent12292.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12292
    BstLean.Part264b.N12292.sourceNumerics12292
    (by norm_num [BstLean.Part263.scalarRow12292])
    (by norm_num [BstLean.Part263.scalarRow12292])
    (by norm_num [BstLean.Part263.scalarRow12292])
    energy12292 BstLean.Part262.actualCertificate12292 t c hw hc

noncomputable def master12292 :
    MasterCertificate 12292 (BstLean.Part260.worldParameters 12292) BstLean.Part259.agent12292 := by
  rw [BstLean.Part260.parameters12292]
  exact BstLean.Part261.master12292

theorem compatible12292 : BstLean.Part259.agent12292.charge ≤ master12292.retainedCharge := by
  change BstLean.Part259.agent12292.charge ≤ BstLean.Part261.master12292.retainedCharge
  rw [show BstLean.Part261.master12292.retainedCharge =
    BstLean.Part259.scalar12292.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12292]
  norm_num [BstLean.Part259.agent12292, BstLean.Part259.scalar12292]

noncomputable def row12292 : BstLean.Part259.RowInputs 12292 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12292
    master12292 BstLean.Part262.actualCertificate12292
    BstLean.Part264b.N12292.covarianceEvent12292
    (BstLean.Part263.cell BstLean.Part263.scalarRow12292.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12292)
    BstLean.Part264b.N12292.covarianceEvent12292_measurable BstLean.Part264b.N12292.covarianceEvent12292_payment
    BstLean.Part264b.N12292.frame12292 (fun t c hw hc => ⟨root12292 t c hw hc⟩)
    BstLean.Part262.allocation12292 compatible12292

theorem energy12293 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12293.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12293, BstLean.Part263.cell12293]

noncomputable def root12293 (t : ℝ) (c : Ret 12293)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12293 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12293) :
    BstLean.Part243.RootInputs 12293 t c BstLean.Part259.agent12293.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12293
    BstLean.Part264b.N12293.sourceNumerics12293
    (by norm_num [BstLean.Part263.scalarRow12293])
    (by norm_num [BstLean.Part263.scalarRow12293])
    (by norm_num [BstLean.Part263.scalarRow12293])
    energy12293 BstLean.Part262.actualCertificate12293 t c hw hc

noncomputable def master12293 :
    MasterCertificate 12293 (BstLean.Part260.worldParameters 12293) BstLean.Part259.agent12293 := by
  rw [BstLean.Part260.parameters12293]
  exact BstLean.Part261.master12293

theorem compatible12293 : BstLean.Part259.agent12293.charge ≤ master12293.retainedCharge := by
  change BstLean.Part259.agent12293.charge ≤ BstLean.Part261.master12293.retainedCharge
  rw [show BstLean.Part261.master12293.retainedCharge =
    BstLean.Part259.scalar12293.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12293]
  norm_num [BstLean.Part259.agent12293, BstLean.Part259.scalar12293]

noncomputable def row12293 : BstLean.Part259.RowInputs 12293 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12293
    master12293 BstLean.Part262.actualCertificate12293
    BstLean.Part264b.N12293.covarianceEvent12293
    (BstLean.Part263.cell BstLean.Part263.scalarRow12293.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12293)
    BstLean.Part264b.N12293.covarianceEvent12293_measurable BstLean.Part264b.N12293.covarianceEvent12293_payment
    BstLean.Part264b.N12293.frame12293 (fun t c hw hc => ⟨root12293 t c hw hc⟩)
    BstLean.Part262.allocation12293 compatible12293

theorem energy12294 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12294.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12294, BstLean.Part263.cell12294]

noncomputable def root12294 (t : ℝ) (c : Ret 12294)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12294 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12294) :
    BstLean.Part243.RootInputs 12294 t c BstLean.Part259.agent12294.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12294
    BstLean.Part264b.N12294.sourceNumerics12294
    (by norm_num [BstLean.Part263.scalarRow12294])
    (by norm_num [BstLean.Part263.scalarRow12294])
    (by norm_num [BstLean.Part263.scalarRow12294])
    energy12294 BstLean.Part262.actualCertificate12294 t c hw hc

noncomputable def master12294 :
    MasterCertificate 12294 (BstLean.Part260.worldParameters 12294) BstLean.Part259.agent12294 := by
  rw [BstLean.Part260.parameters12294]
  exact BstLean.Part261.master12294

theorem compatible12294 : BstLean.Part259.agent12294.charge ≤ master12294.retainedCharge := by
  change BstLean.Part259.agent12294.charge ≤ BstLean.Part261.master12294.retainedCharge
  rw [show BstLean.Part261.master12294.retainedCharge =
    BstLean.Part259.scalar12294.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12294]
  norm_num [BstLean.Part259.agent12294, BstLean.Part259.scalar12294]

noncomputable def row12294 : BstLean.Part259.RowInputs 12294 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12294
    master12294 BstLean.Part262.actualCertificate12294
    BstLean.Part264b.N12294.covarianceEvent12294
    (BstLean.Part263.cell BstLean.Part263.scalarRow12294.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12294)
    BstLean.Part264b.N12294.covarianceEvent12294_measurable BstLean.Part264b.N12294.covarianceEvent12294_payment
    BstLean.Part264b.N12294.frame12294 (fun t c hw hc => ⟨root12294 t c hw hc⟩)
    BstLean.Part262.allocation12294 compatible12294

theorem energy12295 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12295.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12295, BstLean.Part263.cell12295]

noncomputable def root12295 (t : ℝ) (c : Ret 12295)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12295 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12295) :
    BstLean.Part243.RootInputs 12295 t c BstLean.Part259.agent12295.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12295
    BstLean.Part264b.N12295.sourceNumerics12295
    (by norm_num [BstLean.Part263.scalarRow12295])
    (by norm_num [BstLean.Part263.scalarRow12295])
    (by norm_num [BstLean.Part263.scalarRow12295])
    energy12295 BstLean.Part262.actualCertificate12295 t c hw hc

noncomputable def master12295 :
    MasterCertificate 12295 (BstLean.Part260.worldParameters 12295) BstLean.Part259.agent12295 := by
  rw [BstLean.Part260.parameters12295]
  exact BstLean.Part261.master12295

theorem compatible12295 : BstLean.Part259.agent12295.charge ≤ master12295.retainedCharge := by
  change BstLean.Part259.agent12295.charge ≤ BstLean.Part261.master12295.retainedCharge
  rw [show BstLean.Part261.master12295.retainedCharge =
    BstLean.Part259.scalar12295.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12295]
  norm_num [BstLean.Part259.agent12295, BstLean.Part259.scalar12295]

noncomputable def row12295 : BstLean.Part259.RowInputs 12295 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12295
    master12295 BstLean.Part262.actualCertificate12295
    BstLean.Part264b.N12295.covarianceEvent12295
    (BstLean.Part263.cell BstLean.Part263.scalarRow12295.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12295)
    BstLean.Part264b.N12295.covarianceEvent12295_measurable BstLean.Part264b.N12295.covarianceEvent12295_payment
    BstLean.Part264b.N12295.frame12295 (fun t c hw hc => ⟨root12295 t c hw hc⟩)
    BstLean.Part262.allocation12295 compatible12295

theorem energy12296 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12296.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12296, BstLean.Part263.cell12296]

noncomputable def root12296 (t : ℝ) (c : Ret 12296)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12296 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12296) :
    BstLean.Part243.RootInputs 12296 t c BstLean.Part259.agent12296.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12296
    BstLean.Part264b.N12296.sourceNumerics12296
    (by norm_num [BstLean.Part263.scalarRow12296])
    (by norm_num [BstLean.Part263.scalarRow12296])
    (by norm_num [BstLean.Part263.scalarRow12296])
    energy12296 BstLean.Part262.actualCertificate12296 t c hw hc

noncomputable def master12296 :
    MasterCertificate 12296 (BstLean.Part260.worldParameters 12296) BstLean.Part259.agent12296 := by
  rw [BstLean.Part260.parameters12296]
  exact BstLean.Part261.master12296

theorem compatible12296 : BstLean.Part259.agent12296.charge ≤ master12296.retainedCharge := by
  change BstLean.Part259.agent12296.charge ≤ BstLean.Part261.master12296.retainedCharge
  rw [show BstLean.Part261.master12296.retainedCharge =
    BstLean.Part259.scalar12296.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12296]
  norm_num [BstLean.Part259.agent12296, BstLean.Part259.scalar12296]

noncomputable def row12296 : BstLean.Part259.RowInputs 12296 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12296
    master12296 BstLean.Part262.actualCertificate12296
    BstLean.Part264b.N12296.covarianceEvent12296
    (BstLean.Part263.cell BstLean.Part263.scalarRow12296.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12296)
    BstLean.Part264b.N12296.covarianceEvent12296_measurable BstLean.Part264b.N12296.covarianceEvent12296_payment
    BstLean.Part264b.N12296.frame12296 (fun t c hw hc => ⟨root12296 t c hw hc⟩)
    BstLean.Part262.allocation12296 compatible12296

theorem energy12297 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12297.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12297, BstLean.Part263.cell12297]

noncomputable def root12297 (t : ℝ) (c : Ret 12297)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12297 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12297) :
    BstLean.Part243.RootInputs 12297 t c BstLean.Part259.agent12297.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12297
    BstLean.Part264b.N12297.sourceNumerics12297
    (by norm_num [BstLean.Part263.scalarRow12297])
    (by norm_num [BstLean.Part263.scalarRow12297])
    (by norm_num [BstLean.Part263.scalarRow12297])
    energy12297 BstLean.Part262.actualCertificate12297 t c hw hc

noncomputable def master12297 :
    MasterCertificate 12297 (BstLean.Part260.worldParameters 12297) BstLean.Part259.agent12297 := by
  rw [BstLean.Part260.parameters12297]
  exact BstLean.Part261.master12297

theorem compatible12297 : BstLean.Part259.agent12297.charge ≤ master12297.retainedCharge := by
  change BstLean.Part259.agent12297.charge ≤ BstLean.Part261.master12297.retainedCharge
  rw [show BstLean.Part261.master12297.retainedCharge =
    BstLean.Part259.scalar12297.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12297]
  norm_num [BstLean.Part259.agent12297, BstLean.Part259.scalar12297]

noncomputable def row12297 : BstLean.Part259.RowInputs 12297 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12297
    master12297 BstLean.Part262.actualCertificate12297
    BstLean.Part264b.N12297.covarianceEvent12297
    (BstLean.Part263.cell BstLean.Part263.scalarRow12297.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12297)
    BstLean.Part264b.N12297.covarianceEvent12297_measurable BstLean.Part264b.N12297.covarianceEvent12297_payment
    BstLean.Part264b.N12297.frame12297 (fun t c hw hc => ⟨root12297 t c hw hc⟩)
    BstLean.Part262.allocation12297 compatible12297

theorem energy12298 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12298.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12298, BstLean.Part263.cell12298]

noncomputable def root12298 (t : ℝ) (c : Ret 12298)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12298 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12298) :
    BstLean.Part243.RootInputs 12298 t c BstLean.Part259.agent12298.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12298
    BstLean.Part264b.N12298.sourceNumerics12298
    (by norm_num [BstLean.Part263.scalarRow12298])
    (by norm_num [BstLean.Part263.scalarRow12298])
    (by norm_num [BstLean.Part263.scalarRow12298])
    energy12298 BstLean.Part262.actualCertificate12298 t c hw hc

noncomputable def master12298 :
    MasterCertificate 12298 (BstLean.Part260.worldParameters 12298) BstLean.Part259.agent12298 := by
  rw [BstLean.Part260.parameters12298]
  exact BstLean.Part261.master12298

theorem compatible12298 : BstLean.Part259.agent12298.charge ≤ master12298.retainedCharge := by
  change BstLean.Part259.agent12298.charge ≤ BstLean.Part261.master12298.retainedCharge
  rw [show BstLean.Part261.master12298.retainedCharge =
    BstLean.Part259.scalar12298.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12298]
  norm_num [BstLean.Part259.agent12298, BstLean.Part259.scalar12298]

noncomputable def row12298 : BstLean.Part259.RowInputs 12298 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12298
    master12298 BstLean.Part262.actualCertificate12298
    BstLean.Part264b.N12298.covarianceEvent12298
    (BstLean.Part263.cell BstLean.Part263.scalarRow12298.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12298)
    BstLean.Part264b.N12298.covarianceEvent12298_measurable BstLean.Part264b.N12298.covarianceEvent12298_payment
    BstLean.Part264b.N12298.frame12298 (fun t c hw hc => ⟨root12298 t c hw hc⟩)
    BstLean.Part262.allocation12298 compatible12298

theorem energy12299 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12299.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12299, BstLean.Part263.cell12299]

noncomputable def root12299 (t : ℝ) (c : Ret 12299)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12299 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12299) :
    BstLean.Part243.RootInputs 12299 t c BstLean.Part259.agent12299.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12299
    BstLean.Part264b.N12299.sourceNumerics12299
    (by norm_num [BstLean.Part263.scalarRow12299])
    (by norm_num [BstLean.Part263.scalarRow12299])
    (by norm_num [BstLean.Part263.scalarRow12299])
    energy12299 BstLean.Part262.actualCertificate12299 t c hw hc

noncomputable def master12299 :
    MasterCertificate 12299 (BstLean.Part260.worldParameters 12299) BstLean.Part259.agent12299 := by
  rw [BstLean.Part260.parameters12299]
  exact BstLean.Part261.master12299

theorem compatible12299 : BstLean.Part259.agent12299.charge ≤ master12299.retainedCharge := by
  change BstLean.Part259.agent12299.charge ≤ BstLean.Part261.master12299.retainedCharge
  rw [show BstLean.Part261.master12299.retainedCharge =
    BstLean.Part259.scalar12299.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12299]
  norm_num [BstLean.Part259.agent12299, BstLean.Part259.scalar12299]

noncomputable def row12299 : BstLean.Part259.RowInputs 12299 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12299
    master12299 BstLean.Part262.actualCertificate12299
    BstLean.Part264b.N12299.covarianceEvent12299
    (BstLean.Part263.cell BstLean.Part263.scalarRow12299.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12299)
    BstLean.Part264b.N12299.covarianceEvent12299_measurable BstLean.Part264b.N12299.covarianceEvent12299_payment
    BstLean.Part264b.N12299.frame12299 (fun t c hw hc => ⟨root12299 t c hw hc⟩)
    BstLean.Part262.allocation12299 compatible12299

theorem energy12300 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12300.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12300, BstLean.Part263.cell12300]

noncomputable def root12300 (t : ℝ) (c : Ret 12300)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12300 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12300) :
    BstLean.Part243.RootInputs 12300 t c BstLean.Part259.agent12300.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12300
    BstLean.Part264b.N12300.sourceNumerics12300
    (by norm_num [BstLean.Part263.scalarRow12300])
    (by norm_num [BstLean.Part263.scalarRow12300])
    (by norm_num [BstLean.Part263.scalarRow12300])
    energy12300 BstLean.Part262.actualCertificate12300 t c hw hc

noncomputable def master12300 :
    MasterCertificate 12300 (BstLean.Part260.worldParameters 12300) BstLean.Part259.agent12300 := by
  rw [BstLean.Part260.parameters12300]
  exact BstLean.Part261.master12300

theorem compatible12300 : BstLean.Part259.agent12300.charge ≤ master12300.retainedCharge := by
  change BstLean.Part259.agent12300.charge ≤ BstLean.Part261.master12300.retainedCharge
  rw [show BstLean.Part261.master12300.retainedCharge =
    BstLean.Part259.scalar12300.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12300]
  norm_num [BstLean.Part259.agent12300, BstLean.Part259.scalar12300]

noncomputable def row12300 : BstLean.Part259.RowInputs 12300 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12300
    master12300 BstLean.Part262.actualCertificate12300
    BstLean.Part264b.N12300.covarianceEvent12300
    (BstLean.Part263.cell BstLean.Part263.scalarRow12300.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12300)
    BstLean.Part264b.N12300.covarianceEvent12300_measurable BstLean.Part264b.N12300.covarianceEvent12300_payment
    BstLean.Part264b.N12300.frame12300 (fun t c hw hc => ⟨root12300 t c hw hc⟩)
    BstLean.Part262.allocation12300 compatible12300

theorem energy12301 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12301.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12301, BstLean.Part263.cell12301]

noncomputable def root12301 (t : ℝ) (c : Ret 12301)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12301 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12301) :
    BstLean.Part243.RootInputs 12301 t c BstLean.Part259.agent12301.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12301
    BstLean.Part264b.N12301.sourceNumerics12301
    (by norm_num [BstLean.Part263.scalarRow12301])
    (by norm_num [BstLean.Part263.scalarRow12301])
    (by norm_num [BstLean.Part263.scalarRow12301])
    energy12301 BstLean.Part262.actualCertificate12301 t c hw hc

noncomputable def master12301 :
    MasterCertificate 12301 (BstLean.Part260.worldParameters 12301) BstLean.Part259.agent12301 := by
  rw [BstLean.Part260.parameters12301]
  exact BstLean.Part261.master12301

theorem compatible12301 : BstLean.Part259.agent12301.charge ≤ master12301.retainedCharge := by
  change BstLean.Part259.agent12301.charge ≤ BstLean.Part261.master12301.retainedCharge
  rw [show BstLean.Part261.master12301.retainedCharge =
    BstLean.Part259.scalar12301.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12301]
  norm_num [BstLean.Part259.agent12301, BstLean.Part259.scalar12301]

noncomputable def row12301 : BstLean.Part259.RowInputs 12301 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12301
    master12301 BstLean.Part262.actualCertificate12301
    BstLean.Part264b.N12301.covarianceEvent12301
    (BstLean.Part263.cell BstLean.Part263.scalarRow12301.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12301)
    BstLean.Part264b.N12301.covarianceEvent12301_measurable BstLean.Part264b.N12301.covarianceEvent12301_payment
    BstLean.Part264b.N12301.frame12301 (fun t c hw hc => ⟨root12301 t c hw hc⟩)
    BstLean.Part262.allocation12301 compatible12301

end BstLean.Part267
