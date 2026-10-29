import BstLean.Part267Bridge
import BstLean.Part264bFamily
import BstLean.Part261Coverage
import BstLean.Part262ActualCoverage

namespace BstLean.Part267
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part192 BstLean.Part196

theorem energy12254 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12254.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12254, BstLean.Part263.cell12254]

noncomputable def root12254 (t : ℝ) (c : Ret 12254)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12254 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12254) :
    BstLean.Part243.RootInputs 12254 t c BstLean.Part259.agent12254.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12254
    BstLean.Part264b.N12254.sourceNumerics12254
    (by norm_num [BstLean.Part263.scalarRow12254])
    (by norm_num [BstLean.Part263.scalarRow12254])
    (by norm_num [BstLean.Part263.scalarRow12254])
    energy12254 BstLean.Part262.actualCertificate12254 t c hw hc

noncomputable def master12254 :
    MasterCertificate 12254 (BstLean.Part260.worldParameters 12254) BstLean.Part259.agent12254 := by
  rw [BstLean.Part260.parameters12254]
  exact BstLean.Part261.master12254

theorem compatible12254 : BstLean.Part259.agent12254.charge ≤ master12254.retainedCharge := by
  change BstLean.Part259.agent12254.charge ≤ BstLean.Part261.master12254.retainedCharge
  rw [show BstLean.Part261.master12254.retainedCharge =
    BstLean.Part259.scalar12254.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12254]
  norm_num [BstLean.Part259.agent12254, BstLean.Part259.scalar12254]

noncomputable def row12254 : BstLean.Part259.RowInputs 12254 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12254
    master12254 BstLean.Part262.actualCertificate12254
    BstLean.Part264b.N12254.covarianceEvent12254
    (BstLean.Part263.cell BstLean.Part263.scalarRow12254.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12254)
    BstLean.Part264b.N12254.covarianceEvent12254_measurable BstLean.Part264b.N12254.covarianceEvent12254_payment
    BstLean.Part264b.N12254.frame12254 (fun t c hw hc => ⟨root12254 t c hw hc⟩)
    BstLean.Part262.allocation12254 compatible12254

theorem energy12255 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12255.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12255, BstLean.Part263.cell12255]

noncomputable def root12255 (t : ℝ) (c : Ret 12255)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12255 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12255) :
    BstLean.Part243.RootInputs 12255 t c BstLean.Part259.agent12255.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12255
    BstLean.Part264b.N12255.sourceNumerics12255
    (by norm_num [BstLean.Part263.scalarRow12255])
    (by norm_num [BstLean.Part263.scalarRow12255])
    (by norm_num [BstLean.Part263.scalarRow12255])
    energy12255 BstLean.Part262.actualCertificate12255 t c hw hc

noncomputable def master12255 :
    MasterCertificate 12255 (BstLean.Part260.worldParameters 12255) BstLean.Part259.agent12255 := by
  rw [BstLean.Part260.parameters12255]
  exact BstLean.Part261.master12255

theorem compatible12255 : BstLean.Part259.agent12255.charge ≤ master12255.retainedCharge := by
  change BstLean.Part259.agent12255.charge ≤ BstLean.Part261.master12255.retainedCharge
  rw [show BstLean.Part261.master12255.retainedCharge =
    BstLean.Part259.scalar12255.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12255]
  norm_num [BstLean.Part259.agent12255, BstLean.Part259.scalar12255]

noncomputable def row12255 : BstLean.Part259.RowInputs 12255 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12255
    master12255 BstLean.Part262.actualCertificate12255
    BstLean.Part264b.N12255.covarianceEvent12255
    (BstLean.Part263.cell BstLean.Part263.scalarRow12255.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12255)
    BstLean.Part264b.N12255.covarianceEvent12255_measurable BstLean.Part264b.N12255.covarianceEvent12255_payment
    BstLean.Part264b.N12255.frame12255 (fun t c hw hc => ⟨root12255 t c hw hc⟩)
    BstLean.Part262.allocation12255 compatible12255

theorem energy12256 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12256.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12256, BstLean.Part263.cell12256]

noncomputable def root12256 (t : ℝ) (c : Ret 12256)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12256 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12256) :
    BstLean.Part243.RootInputs 12256 t c BstLean.Part259.agent12256.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12256
    BstLean.Part264b.N12256.sourceNumerics12256
    (by norm_num [BstLean.Part263.scalarRow12256])
    (by norm_num [BstLean.Part263.scalarRow12256])
    (by norm_num [BstLean.Part263.scalarRow12256])
    energy12256 BstLean.Part262.actualCertificate12256 t c hw hc

noncomputable def master12256 :
    MasterCertificate 12256 (BstLean.Part260.worldParameters 12256) BstLean.Part259.agent12256 := by
  rw [BstLean.Part260.parameters12256]
  exact BstLean.Part261.master12256

theorem compatible12256 : BstLean.Part259.agent12256.charge ≤ master12256.retainedCharge := by
  change BstLean.Part259.agent12256.charge ≤ BstLean.Part261.master12256.retainedCharge
  rw [show BstLean.Part261.master12256.retainedCharge =
    BstLean.Part259.scalar12256.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12256]
  norm_num [BstLean.Part259.agent12256, BstLean.Part259.scalar12256]

noncomputable def row12256 : BstLean.Part259.RowInputs 12256 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12256
    master12256 BstLean.Part262.actualCertificate12256
    BstLean.Part264b.N12256.covarianceEvent12256
    (BstLean.Part263.cell BstLean.Part263.scalarRow12256.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12256)
    BstLean.Part264b.N12256.covarianceEvent12256_measurable BstLean.Part264b.N12256.covarianceEvent12256_payment
    BstLean.Part264b.N12256.frame12256 (fun t c hw hc => ⟨root12256 t c hw hc⟩)
    BstLean.Part262.allocation12256 compatible12256

theorem energy12257 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12257.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12257, BstLean.Part263.cell12257]

noncomputable def root12257 (t : ℝ) (c : Ret 12257)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12257 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12257) :
    BstLean.Part243.RootInputs 12257 t c BstLean.Part259.agent12257.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12257
    BstLean.Part264b.N12257.sourceNumerics12257
    (by norm_num [BstLean.Part263.scalarRow12257])
    (by norm_num [BstLean.Part263.scalarRow12257])
    (by norm_num [BstLean.Part263.scalarRow12257])
    energy12257 BstLean.Part262.actualCertificate12257 t c hw hc

noncomputable def master12257 :
    MasterCertificate 12257 (BstLean.Part260.worldParameters 12257) BstLean.Part259.agent12257 := by
  rw [BstLean.Part260.parameters12257]
  exact BstLean.Part261.master12257

theorem compatible12257 : BstLean.Part259.agent12257.charge ≤ master12257.retainedCharge := by
  change BstLean.Part259.agent12257.charge ≤ BstLean.Part261.master12257.retainedCharge
  rw [show BstLean.Part261.master12257.retainedCharge =
    BstLean.Part259.scalar12257.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12257]
  norm_num [BstLean.Part259.agent12257, BstLean.Part259.scalar12257]

noncomputable def row12257 : BstLean.Part259.RowInputs 12257 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12257
    master12257 BstLean.Part262.actualCertificate12257
    BstLean.Part264b.N12257.covarianceEvent12257
    (BstLean.Part263.cell BstLean.Part263.scalarRow12257.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12257)
    BstLean.Part264b.N12257.covarianceEvent12257_measurable BstLean.Part264b.N12257.covarianceEvent12257_payment
    BstLean.Part264b.N12257.frame12257 (fun t c hw hc => ⟨root12257 t c hw hc⟩)
    BstLean.Part262.allocation12257 compatible12257

theorem energy12258 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12258.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12258, BstLean.Part263.cell12258]

noncomputable def root12258 (t : ℝ) (c : Ret 12258)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12258 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12258) :
    BstLean.Part243.RootInputs 12258 t c BstLean.Part259.agent12258.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12258
    BstLean.Part264b.N12258.sourceNumerics12258
    (by norm_num [BstLean.Part263.scalarRow12258])
    (by norm_num [BstLean.Part263.scalarRow12258])
    (by norm_num [BstLean.Part263.scalarRow12258])
    energy12258 BstLean.Part262.actualCertificate12258 t c hw hc

noncomputable def master12258 :
    MasterCertificate 12258 (BstLean.Part260.worldParameters 12258) BstLean.Part259.agent12258 := by
  rw [BstLean.Part260.parameters12258]
  exact BstLean.Part261.master12258

theorem compatible12258 : BstLean.Part259.agent12258.charge ≤ master12258.retainedCharge := by
  change BstLean.Part259.agent12258.charge ≤ BstLean.Part261.master12258.retainedCharge
  rw [show BstLean.Part261.master12258.retainedCharge =
    BstLean.Part259.scalar12258.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12258]
  norm_num [BstLean.Part259.agent12258, BstLean.Part259.scalar12258]

noncomputable def row12258 : BstLean.Part259.RowInputs 12258 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12258
    master12258 BstLean.Part262.actualCertificate12258
    BstLean.Part264b.N12258.covarianceEvent12258
    (BstLean.Part263.cell BstLean.Part263.scalarRow12258.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12258)
    BstLean.Part264b.N12258.covarianceEvent12258_measurable BstLean.Part264b.N12258.covarianceEvent12258_payment
    BstLean.Part264b.N12258.frame12258 (fun t c hw hc => ⟨root12258 t c hw hc⟩)
    BstLean.Part262.allocation12258 compatible12258

theorem energy12259 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12259.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12259, BstLean.Part263.cell12259]

noncomputable def root12259 (t : ℝ) (c : Ret 12259)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12259 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12259) :
    BstLean.Part243.RootInputs 12259 t c BstLean.Part259.agent12259.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12259
    BstLean.Part264b.N12259.sourceNumerics12259
    (by norm_num [BstLean.Part263.scalarRow12259])
    (by norm_num [BstLean.Part263.scalarRow12259])
    (by norm_num [BstLean.Part263.scalarRow12259])
    energy12259 BstLean.Part262.actualCertificate12259 t c hw hc

noncomputable def master12259 :
    MasterCertificate 12259 (BstLean.Part260.worldParameters 12259) BstLean.Part259.agent12259 := by
  rw [BstLean.Part260.parameters12259]
  exact BstLean.Part261.master12259

theorem compatible12259 : BstLean.Part259.agent12259.charge ≤ master12259.retainedCharge := by
  change BstLean.Part259.agent12259.charge ≤ BstLean.Part261.master12259.retainedCharge
  rw [show BstLean.Part261.master12259.retainedCharge =
    BstLean.Part259.scalar12259.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12259]
  norm_num [BstLean.Part259.agent12259, BstLean.Part259.scalar12259]

noncomputable def row12259 : BstLean.Part259.RowInputs 12259 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12259
    master12259 BstLean.Part262.actualCertificate12259
    BstLean.Part264b.N12259.covarianceEvent12259
    (BstLean.Part263.cell BstLean.Part263.scalarRow12259.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12259)
    BstLean.Part264b.N12259.covarianceEvent12259_measurable BstLean.Part264b.N12259.covarianceEvent12259_payment
    BstLean.Part264b.N12259.frame12259 (fun t c hw hc => ⟨root12259 t c hw hc⟩)
    BstLean.Part262.allocation12259 compatible12259

theorem energy12260 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12260.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12260, BstLean.Part263.cell12260]

noncomputable def root12260 (t : ℝ) (c : Ret 12260)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12260 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12260) :
    BstLean.Part243.RootInputs 12260 t c BstLean.Part259.agent12260.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12260
    BstLean.Part264b.N12260.sourceNumerics12260
    (by norm_num [BstLean.Part263.scalarRow12260])
    (by norm_num [BstLean.Part263.scalarRow12260])
    (by norm_num [BstLean.Part263.scalarRow12260])
    energy12260 BstLean.Part262.actualCertificate12260 t c hw hc

noncomputable def master12260 :
    MasterCertificate 12260 (BstLean.Part260.worldParameters 12260) BstLean.Part259.agent12260 := by
  rw [BstLean.Part260.parameters12260]
  exact BstLean.Part261.master12260

theorem compatible12260 : BstLean.Part259.agent12260.charge ≤ master12260.retainedCharge := by
  change BstLean.Part259.agent12260.charge ≤ BstLean.Part261.master12260.retainedCharge
  rw [show BstLean.Part261.master12260.retainedCharge =
    BstLean.Part259.scalar12260.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12260]
  norm_num [BstLean.Part259.agent12260, BstLean.Part259.scalar12260]

noncomputable def row12260 : BstLean.Part259.RowInputs 12260 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12260
    master12260 BstLean.Part262.actualCertificate12260
    BstLean.Part264b.N12260.covarianceEvent12260
    (BstLean.Part263.cell BstLean.Part263.scalarRow12260.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12260)
    BstLean.Part264b.N12260.covarianceEvent12260_measurable BstLean.Part264b.N12260.covarianceEvent12260_payment
    BstLean.Part264b.N12260.frame12260 (fun t c hw hc => ⟨root12260 t c hw hc⟩)
    BstLean.Part262.allocation12260 compatible12260

theorem energy12261 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12261.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12261, BstLean.Part263.cell12261]

noncomputable def root12261 (t : ℝ) (c : Ret 12261)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12261 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12261) :
    BstLean.Part243.RootInputs 12261 t c BstLean.Part259.agent12261.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12261
    BstLean.Part264b.N12261.sourceNumerics12261
    (by norm_num [BstLean.Part263.scalarRow12261])
    (by norm_num [BstLean.Part263.scalarRow12261])
    (by norm_num [BstLean.Part263.scalarRow12261])
    energy12261 BstLean.Part262.actualCertificate12261 t c hw hc

noncomputable def master12261 :
    MasterCertificate 12261 (BstLean.Part260.worldParameters 12261) BstLean.Part259.agent12261 := by
  rw [BstLean.Part260.parameters12261]
  exact BstLean.Part261.master12261

theorem compatible12261 : BstLean.Part259.agent12261.charge ≤ master12261.retainedCharge := by
  change BstLean.Part259.agent12261.charge ≤ BstLean.Part261.master12261.retainedCharge
  rw [show BstLean.Part261.master12261.retainedCharge =
    BstLean.Part259.scalar12261.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12261]
  norm_num [BstLean.Part259.agent12261, BstLean.Part259.scalar12261]

noncomputable def row12261 : BstLean.Part259.RowInputs 12261 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12261
    master12261 BstLean.Part262.actualCertificate12261
    BstLean.Part264b.N12261.covarianceEvent12261
    (BstLean.Part263.cell BstLean.Part263.scalarRow12261.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12261)
    BstLean.Part264b.N12261.covarianceEvent12261_measurable BstLean.Part264b.N12261.covarianceEvent12261_payment
    BstLean.Part264b.N12261.frame12261 (fun t c hw hc => ⟨root12261 t c hw hc⟩)
    BstLean.Part262.allocation12261 compatible12261

theorem energy12262 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12262.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12262, BstLean.Part263.cell12262]

noncomputable def root12262 (t : ℝ) (c : Ret 12262)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12262 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12262) :
    BstLean.Part243.RootInputs 12262 t c BstLean.Part259.agent12262.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12262
    BstLean.Part264b.N12262.sourceNumerics12262
    (by norm_num [BstLean.Part263.scalarRow12262])
    (by norm_num [BstLean.Part263.scalarRow12262])
    (by norm_num [BstLean.Part263.scalarRow12262])
    energy12262 BstLean.Part262.actualCertificate12262 t c hw hc

noncomputable def master12262 :
    MasterCertificate 12262 (BstLean.Part260.worldParameters 12262) BstLean.Part259.agent12262 := by
  rw [BstLean.Part260.parameters12262]
  exact BstLean.Part261.master12262

theorem compatible12262 : BstLean.Part259.agent12262.charge ≤ master12262.retainedCharge := by
  change BstLean.Part259.agent12262.charge ≤ BstLean.Part261.master12262.retainedCharge
  rw [show BstLean.Part261.master12262.retainedCharge =
    BstLean.Part259.scalar12262.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12262]
  norm_num [BstLean.Part259.agent12262, BstLean.Part259.scalar12262]

noncomputable def row12262 : BstLean.Part259.RowInputs 12262 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12262
    master12262 BstLean.Part262.actualCertificate12262
    BstLean.Part264b.N12262.covarianceEvent12262
    (BstLean.Part263.cell BstLean.Part263.scalarRow12262.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12262)
    BstLean.Part264b.N12262.covarianceEvent12262_measurable BstLean.Part264b.N12262.covarianceEvent12262_payment
    BstLean.Part264b.N12262.frame12262 (fun t c hw hc => ⟨root12262 t c hw hc⟩)
    BstLean.Part262.allocation12262 compatible12262

theorem energy12263 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12263.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12263, BstLean.Part263.cell12263]

noncomputable def root12263 (t : ℝ) (c : Ret 12263)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12263 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12263) :
    BstLean.Part243.RootInputs 12263 t c BstLean.Part259.agent12263.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12263
    BstLean.Part264b.N12263.sourceNumerics12263
    (by norm_num [BstLean.Part263.scalarRow12263])
    (by norm_num [BstLean.Part263.scalarRow12263])
    (by norm_num [BstLean.Part263.scalarRow12263])
    energy12263 BstLean.Part262.actualCertificate12263 t c hw hc

noncomputable def master12263 :
    MasterCertificate 12263 (BstLean.Part260.worldParameters 12263) BstLean.Part259.agent12263 := by
  rw [BstLean.Part260.parameters12263]
  exact BstLean.Part261.master12263

theorem compatible12263 : BstLean.Part259.agent12263.charge ≤ master12263.retainedCharge := by
  change BstLean.Part259.agent12263.charge ≤ BstLean.Part261.master12263.retainedCharge
  rw [show BstLean.Part261.master12263.retainedCharge =
    BstLean.Part259.scalar12263.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12263]
  norm_num [BstLean.Part259.agent12263, BstLean.Part259.scalar12263]

noncomputable def row12263 : BstLean.Part259.RowInputs 12263 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12263
    master12263 BstLean.Part262.actualCertificate12263
    BstLean.Part264b.N12263.covarianceEvent12263
    (BstLean.Part263.cell BstLean.Part263.scalarRow12263.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12263)
    BstLean.Part264b.N12263.covarianceEvent12263_measurable BstLean.Part264b.N12263.covarianceEvent12263_payment
    BstLean.Part264b.N12263.frame12263 (fun t c hw hc => ⟨root12263 t c hw hc⟩)
    BstLean.Part262.allocation12263 compatible12263

theorem energy12264 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12264.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12264, BstLean.Part263.cell12264]

noncomputable def root12264 (t : ℝ) (c : Ret 12264)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12264 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12264) :
    BstLean.Part243.RootInputs 12264 t c BstLean.Part259.agent12264.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12264
    BstLean.Part264b.N12264.sourceNumerics12264
    (by norm_num [BstLean.Part263.scalarRow12264])
    (by norm_num [BstLean.Part263.scalarRow12264])
    (by norm_num [BstLean.Part263.scalarRow12264])
    energy12264 BstLean.Part262.actualCertificate12264 t c hw hc

noncomputable def master12264 :
    MasterCertificate 12264 (BstLean.Part260.worldParameters 12264) BstLean.Part259.agent12264 := by
  rw [BstLean.Part260.parameters12264]
  exact BstLean.Part261.master12264

theorem compatible12264 : BstLean.Part259.agent12264.charge ≤ master12264.retainedCharge := by
  change BstLean.Part259.agent12264.charge ≤ BstLean.Part261.master12264.retainedCharge
  rw [show BstLean.Part261.master12264.retainedCharge =
    BstLean.Part259.scalar12264.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12264]
  norm_num [BstLean.Part259.agent12264, BstLean.Part259.scalar12264]

noncomputable def row12264 : BstLean.Part259.RowInputs 12264 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12264
    master12264 BstLean.Part262.actualCertificate12264
    BstLean.Part264b.N12264.covarianceEvent12264
    (BstLean.Part263.cell BstLean.Part263.scalarRow12264.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12264)
    BstLean.Part264b.N12264.covarianceEvent12264_measurable BstLean.Part264b.N12264.covarianceEvent12264_payment
    BstLean.Part264b.N12264.frame12264 (fun t c hw hc => ⟨root12264 t c hw hc⟩)
    BstLean.Part262.allocation12264 compatible12264

theorem energy12265 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12265.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12265, BstLean.Part263.cell12265]

noncomputable def root12265 (t : ℝ) (c : Ret 12265)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12265 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12265) :
    BstLean.Part243.RootInputs 12265 t c BstLean.Part259.agent12265.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12265
    BstLean.Part264b.N12265.sourceNumerics12265
    (by norm_num [BstLean.Part263.scalarRow12265])
    (by norm_num [BstLean.Part263.scalarRow12265])
    (by norm_num [BstLean.Part263.scalarRow12265])
    energy12265 BstLean.Part262.actualCertificate12265 t c hw hc

noncomputable def master12265 :
    MasterCertificate 12265 (BstLean.Part260.worldParameters 12265) BstLean.Part259.agent12265 := by
  rw [BstLean.Part260.parameters12265]
  exact BstLean.Part261.master12265

theorem compatible12265 : BstLean.Part259.agent12265.charge ≤ master12265.retainedCharge := by
  change BstLean.Part259.agent12265.charge ≤ BstLean.Part261.master12265.retainedCharge
  rw [show BstLean.Part261.master12265.retainedCharge =
    BstLean.Part259.scalar12265.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12265]
  norm_num [BstLean.Part259.agent12265, BstLean.Part259.scalar12265]

noncomputable def row12265 : BstLean.Part259.RowInputs 12265 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12265
    master12265 BstLean.Part262.actualCertificate12265
    BstLean.Part264b.N12265.covarianceEvent12265
    (BstLean.Part263.cell BstLean.Part263.scalarRow12265.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12265)
    BstLean.Part264b.N12265.covarianceEvent12265_measurable BstLean.Part264b.N12265.covarianceEvent12265_payment
    BstLean.Part264b.N12265.frame12265 (fun t c hw hc => ⟨root12265 t c hw hc⟩)
    BstLean.Part262.allocation12265 compatible12265

theorem energy12266 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12266.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12266, BstLean.Part263.cell12266]

noncomputable def root12266 (t : ℝ) (c : Ret 12266)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12266 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12266) :
    BstLean.Part243.RootInputs 12266 t c BstLean.Part259.agent12266.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12266
    BstLean.Part264b.N12266.sourceNumerics12266
    (by norm_num [BstLean.Part263.scalarRow12266])
    (by norm_num [BstLean.Part263.scalarRow12266])
    (by norm_num [BstLean.Part263.scalarRow12266])
    energy12266 BstLean.Part262.actualCertificate12266 t c hw hc

noncomputable def master12266 :
    MasterCertificate 12266 (BstLean.Part260.worldParameters 12266) BstLean.Part259.agent12266 := by
  rw [BstLean.Part260.parameters12266]
  exact BstLean.Part261.master12266

theorem compatible12266 : BstLean.Part259.agent12266.charge ≤ master12266.retainedCharge := by
  change BstLean.Part259.agent12266.charge ≤ BstLean.Part261.master12266.retainedCharge
  rw [show BstLean.Part261.master12266.retainedCharge =
    BstLean.Part259.scalar12266.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12266]
  norm_num [BstLean.Part259.agent12266, BstLean.Part259.scalar12266]

noncomputable def row12266 : BstLean.Part259.RowInputs 12266 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12266
    master12266 BstLean.Part262.actualCertificate12266
    BstLean.Part264b.N12266.covarianceEvent12266
    (BstLean.Part263.cell BstLean.Part263.scalarRow12266.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12266)
    BstLean.Part264b.N12266.covarianceEvent12266_measurable BstLean.Part264b.N12266.covarianceEvent12266_payment
    BstLean.Part264b.N12266.frame12266 (fun t c hw hc => ⟨root12266 t c hw hc⟩)
    BstLean.Part262.allocation12266 compatible12266

theorem energy12267 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12267.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12267, BstLean.Part263.cell12267]

noncomputable def root12267 (t : ℝ) (c : Ret 12267)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12267 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12267) :
    BstLean.Part243.RootInputs 12267 t c BstLean.Part259.agent12267.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12267
    BstLean.Part264b.N12267.sourceNumerics12267
    (by norm_num [BstLean.Part263.scalarRow12267])
    (by norm_num [BstLean.Part263.scalarRow12267])
    (by norm_num [BstLean.Part263.scalarRow12267])
    energy12267 BstLean.Part262.actualCertificate12267 t c hw hc

noncomputable def master12267 :
    MasterCertificate 12267 (BstLean.Part260.worldParameters 12267) BstLean.Part259.agent12267 := by
  rw [BstLean.Part260.parameters12267]
  exact BstLean.Part261.master12267

theorem compatible12267 : BstLean.Part259.agent12267.charge ≤ master12267.retainedCharge := by
  change BstLean.Part259.agent12267.charge ≤ BstLean.Part261.master12267.retainedCharge
  rw [show BstLean.Part261.master12267.retainedCharge =
    BstLean.Part259.scalar12267.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12267]
  norm_num [BstLean.Part259.agent12267, BstLean.Part259.scalar12267]

noncomputable def row12267 : BstLean.Part259.RowInputs 12267 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12267
    master12267 BstLean.Part262.actualCertificate12267
    BstLean.Part264b.N12267.covarianceEvent12267
    (BstLean.Part263.cell BstLean.Part263.scalarRow12267.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12267)
    BstLean.Part264b.N12267.covarianceEvent12267_measurable BstLean.Part264b.N12267.covarianceEvent12267_payment
    BstLean.Part264b.N12267.frame12267 (fun t c hw hc => ⟨root12267 t c hw hc⟩)
    BstLean.Part262.allocation12267 compatible12267

theorem energy12268 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12268.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12268, BstLean.Part263.cell12268]

noncomputable def root12268 (t : ℝ) (c : Ret 12268)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12268 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12268) :
    BstLean.Part243.RootInputs 12268 t c BstLean.Part259.agent12268.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12268
    BstLean.Part264b.N12268.sourceNumerics12268
    (by norm_num [BstLean.Part263.scalarRow12268])
    (by norm_num [BstLean.Part263.scalarRow12268])
    (by norm_num [BstLean.Part263.scalarRow12268])
    energy12268 BstLean.Part262.actualCertificate12268 t c hw hc

noncomputable def master12268 :
    MasterCertificate 12268 (BstLean.Part260.worldParameters 12268) BstLean.Part259.agent12268 := by
  rw [BstLean.Part260.parameters12268]
  exact BstLean.Part261.master12268

theorem compatible12268 : BstLean.Part259.agent12268.charge ≤ master12268.retainedCharge := by
  change BstLean.Part259.agent12268.charge ≤ BstLean.Part261.master12268.retainedCharge
  rw [show BstLean.Part261.master12268.retainedCharge =
    BstLean.Part259.scalar12268.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12268]
  norm_num [BstLean.Part259.agent12268, BstLean.Part259.scalar12268]

noncomputable def row12268 : BstLean.Part259.RowInputs 12268 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12268
    master12268 BstLean.Part262.actualCertificate12268
    BstLean.Part264b.N12268.covarianceEvent12268
    (BstLean.Part263.cell BstLean.Part263.scalarRow12268.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12268)
    BstLean.Part264b.N12268.covarianceEvent12268_measurable BstLean.Part264b.N12268.covarianceEvent12268_payment
    BstLean.Part264b.N12268.frame12268 (fun t c hw hc => ⟨root12268 t c hw hc⟩)
    BstLean.Part262.allocation12268 compatible12268

theorem energy12269 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12269.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12269, BstLean.Part263.cell12269]

noncomputable def root12269 (t : ℝ) (c : Ret 12269)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12269 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12269) :
    BstLean.Part243.RootInputs 12269 t c BstLean.Part259.agent12269.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12269
    BstLean.Part264b.N12269.sourceNumerics12269
    (by norm_num [BstLean.Part263.scalarRow12269])
    (by norm_num [BstLean.Part263.scalarRow12269])
    (by norm_num [BstLean.Part263.scalarRow12269])
    energy12269 BstLean.Part262.actualCertificate12269 t c hw hc

noncomputable def master12269 :
    MasterCertificate 12269 (BstLean.Part260.worldParameters 12269) BstLean.Part259.agent12269 := by
  rw [BstLean.Part260.parameters12269]
  exact BstLean.Part261.master12269

theorem compatible12269 : BstLean.Part259.agent12269.charge ≤ master12269.retainedCharge := by
  change BstLean.Part259.agent12269.charge ≤ BstLean.Part261.master12269.retainedCharge
  rw [show BstLean.Part261.master12269.retainedCharge =
    BstLean.Part259.scalar12269.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12269]
  norm_num [BstLean.Part259.agent12269, BstLean.Part259.scalar12269]

noncomputable def row12269 : BstLean.Part259.RowInputs 12269 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12269
    master12269 BstLean.Part262.actualCertificate12269
    BstLean.Part264b.N12269.covarianceEvent12269
    (BstLean.Part263.cell BstLean.Part263.scalarRow12269.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12269)
    BstLean.Part264b.N12269.covarianceEvent12269_measurable BstLean.Part264b.N12269.covarianceEvent12269_payment
    BstLean.Part264b.N12269.frame12269 (fun t c hw hc => ⟨root12269 t c hw hc⟩)
    BstLean.Part262.allocation12269 compatible12269

theorem energy12270 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12270.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12270, BstLean.Part263.cell12270]

noncomputable def root12270 (t : ℝ) (c : Ret 12270)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12270 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12270) :
    BstLean.Part243.RootInputs 12270 t c BstLean.Part259.agent12270.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12270
    BstLean.Part264b.N12270.sourceNumerics12270
    (by norm_num [BstLean.Part263.scalarRow12270])
    (by norm_num [BstLean.Part263.scalarRow12270])
    (by norm_num [BstLean.Part263.scalarRow12270])
    energy12270 BstLean.Part262.actualCertificate12270 t c hw hc

noncomputable def master12270 :
    MasterCertificate 12270 (BstLean.Part260.worldParameters 12270) BstLean.Part259.agent12270 := by
  rw [BstLean.Part260.parameters12270]
  exact BstLean.Part261.master12270

theorem compatible12270 : BstLean.Part259.agent12270.charge ≤ master12270.retainedCharge := by
  change BstLean.Part259.agent12270.charge ≤ BstLean.Part261.master12270.retainedCharge
  rw [show BstLean.Part261.master12270.retainedCharge =
    BstLean.Part259.scalar12270.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12270]
  norm_num [BstLean.Part259.agent12270, BstLean.Part259.scalar12270]

noncomputable def row12270 : BstLean.Part259.RowInputs 12270 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12270
    master12270 BstLean.Part262.actualCertificate12270
    BstLean.Part264b.N12270.covarianceEvent12270
    (BstLean.Part263.cell BstLean.Part263.scalarRow12270.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12270)
    BstLean.Part264b.N12270.covarianceEvent12270_measurable BstLean.Part264b.N12270.covarianceEvent12270_payment
    BstLean.Part264b.N12270.frame12270 (fun t c hw hc => ⟨root12270 t c hw hc⟩)
    BstLean.Part262.allocation12270 compatible12270

theorem energy12271 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12271.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12271, BstLean.Part263.cell12271]

noncomputable def root12271 (t : ℝ) (c : Ret 12271)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12271 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12271) :
    BstLean.Part243.RootInputs 12271 t c BstLean.Part259.agent12271.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12271
    BstLean.Part264b.N12271.sourceNumerics12271
    (by norm_num [BstLean.Part263.scalarRow12271])
    (by norm_num [BstLean.Part263.scalarRow12271])
    (by norm_num [BstLean.Part263.scalarRow12271])
    energy12271 BstLean.Part262.actualCertificate12271 t c hw hc

noncomputable def master12271 :
    MasterCertificate 12271 (BstLean.Part260.worldParameters 12271) BstLean.Part259.agent12271 := by
  rw [BstLean.Part260.parameters12271]
  exact BstLean.Part261.master12271

theorem compatible12271 : BstLean.Part259.agent12271.charge ≤ master12271.retainedCharge := by
  change BstLean.Part259.agent12271.charge ≤ BstLean.Part261.master12271.retainedCharge
  rw [show BstLean.Part261.master12271.retainedCharge =
    BstLean.Part259.scalar12271.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12271]
  norm_num [BstLean.Part259.agent12271, BstLean.Part259.scalar12271]

noncomputable def row12271 : BstLean.Part259.RowInputs 12271 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12271
    master12271 BstLean.Part262.actualCertificate12271
    BstLean.Part264b.N12271.covarianceEvent12271
    (BstLean.Part263.cell BstLean.Part263.scalarRow12271.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12271)
    BstLean.Part264b.N12271.covarianceEvent12271_measurable BstLean.Part264b.N12271.covarianceEvent12271_payment
    BstLean.Part264b.N12271.frame12271 (fun t c hw hc => ⟨root12271 t c hw hc⟩)
    BstLean.Part262.allocation12271 compatible12271

theorem energy12272 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12272.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12272, BstLean.Part263.cell12272]

noncomputable def root12272 (t : ℝ) (c : Ret 12272)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12272 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12272) :
    BstLean.Part243.RootInputs 12272 t c BstLean.Part259.agent12272.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12272
    BstLean.Part264b.N12272.sourceNumerics12272
    (by norm_num [BstLean.Part263.scalarRow12272])
    (by norm_num [BstLean.Part263.scalarRow12272])
    (by norm_num [BstLean.Part263.scalarRow12272])
    energy12272 BstLean.Part262.actualCertificate12272 t c hw hc

noncomputable def master12272 :
    MasterCertificate 12272 (BstLean.Part260.worldParameters 12272) BstLean.Part259.agent12272 := by
  rw [BstLean.Part260.parameters12272]
  exact BstLean.Part261.master12272

theorem compatible12272 : BstLean.Part259.agent12272.charge ≤ master12272.retainedCharge := by
  change BstLean.Part259.agent12272.charge ≤ BstLean.Part261.master12272.retainedCharge
  rw [show BstLean.Part261.master12272.retainedCharge =
    BstLean.Part259.scalar12272.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12272]
  norm_num [BstLean.Part259.agent12272, BstLean.Part259.scalar12272]

noncomputable def row12272 : BstLean.Part259.RowInputs 12272 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12272
    master12272 BstLean.Part262.actualCertificate12272
    BstLean.Part264b.N12272.covarianceEvent12272
    (BstLean.Part263.cell BstLean.Part263.scalarRow12272.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12272)
    BstLean.Part264b.N12272.covarianceEvent12272_measurable BstLean.Part264b.N12272.covarianceEvent12272_payment
    BstLean.Part264b.N12272.frame12272 (fun t c hw hc => ⟨root12272 t c hw hc⟩)
    BstLean.Part262.allocation12272 compatible12272

theorem energy12273 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12273.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12273, BstLean.Part263.cell12273]

noncomputable def root12273 (t : ℝ) (c : Ret 12273)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12273 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12273) :
    BstLean.Part243.RootInputs 12273 t c BstLean.Part259.agent12273.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12273
    BstLean.Part264b.N12273.sourceNumerics12273
    (by norm_num [BstLean.Part263.scalarRow12273])
    (by norm_num [BstLean.Part263.scalarRow12273])
    (by norm_num [BstLean.Part263.scalarRow12273])
    energy12273 BstLean.Part262.actualCertificate12273 t c hw hc

noncomputable def master12273 :
    MasterCertificate 12273 (BstLean.Part260.worldParameters 12273) BstLean.Part259.agent12273 := by
  rw [BstLean.Part260.parameters12273]
  exact BstLean.Part261.master12273

theorem compatible12273 : BstLean.Part259.agent12273.charge ≤ master12273.retainedCharge := by
  change BstLean.Part259.agent12273.charge ≤ BstLean.Part261.master12273.retainedCharge
  rw [show BstLean.Part261.master12273.retainedCharge =
    BstLean.Part259.scalar12273.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12273]
  norm_num [BstLean.Part259.agent12273, BstLean.Part259.scalar12273]

noncomputable def row12273 : BstLean.Part259.RowInputs 12273 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12273
    master12273 BstLean.Part262.actualCertificate12273
    BstLean.Part264b.N12273.covarianceEvent12273
    (BstLean.Part263.cell BstLean.Part263.scalarRow12273.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12273)
    BstLean.Part264b.N12273.covarianceEvent12273_measurable BstLean.Part264b.N12273.covarianceEvent12273_payment
    BstLean.Part264b.N12273.frame12273 (fun t c hw hc => ⟨root12273 t c hw hc⟩)
    BstLean.Part262.allocation12273 compatible12273

theorem energy12274 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12274.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12274, BstLean.Part263.cell12274]

noncomputable def root12274 (t : ℝ) (c : Ret 12274)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12274 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12274) :
    BstLean.Part243.RootInputs 12274 t c BstLean.Part259.agent12274.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12274
    BstLean.Part264b.N12274.sourceNumerics12274
    (by norm_num [BstLean.Part263.scalarRow12274])
    (by norm_num [BstLean.Part263.scalarRow12274])
    (by norm_num [BstLean.Part263.scalarRow12274])
    energy12274 BstLean.Part262.actualCertificate12274 t c hw hc

noncomputable def master12274 :
    MasterCertificate 12274 (BstLean.Part260.worldParameters 12274) BstLean.Part259.agent12274 := by
  rw [BstLean.Part260.parameters12274]
  exact BstLean.Part261.master12274

theorem compatible12274 : BstLean.Part259.agent12274.charge ≤ master12274.retainedCharge := by
  change BstLean.Part259.agent12274.charge ≤ BstLean.Part261.master12274.retainedCharge
  rw [show BstLean.Part261.master12274.retainedCharge =
    BstLean.Part259.scalar12274.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12274]
  norm_num [BstLean.Part259.agent12274, BstLean.Part259.scalar12274]

noncomputable def row12274 : BstLean.Part259.RowInputs 12274 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12274
    master12274 BstLean.Part262.actualCertificate12274
    BstLean.Part264b.N12274.covarianceEvent12274
    (BstLean.Part263.cell BstLean.Part263.scalarRow12274.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12274)
    BstLean.Part264b.N12274.covarianceEvent12274_measurable BstLean.Part264b.N12274.covarianceEvent12274_payment
    BstLean.Part264b.N12274.frame12274 (fun t c hw hc => ⟨root12274 t c hw hc⟩)
    BstLean.Part262.allocation12274 compatible12274

theorem energy12275 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12275.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12275, BstLean.Part263.cell12275]

noncomputable def root12275 (t : ℝ) (c : Ret 12275)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12275 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12275) :
    BstLean.Part243.RootInputs 12275 t c BstLean.Part259.agent12275.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12275
    BstLean.Part264b.N12275.sourceNumerics12275
    (by norm_num [BstLean.Part263.scalarRow12275])
    (by norm_num [BstLean.Part263.scalarRow12275])
    (by norm_num [BstLean.Part263.scalarRow12275])
    energy12275 BstLean.Part262.actualCertificate12275 t c hw hc

noncomputable def master12275 :
    MasterCertificate 12275 (BstLean.Part260.worldParameters 12275) BstLean.Part259.agent12275 := by
  rw [BstLean.Part260.parameters12275]
  exact BstLean.Part261.master12275

theorem compatible12275 : BstLean.Part259.agent12275.charge ≤ master12275.retainedCharge := by
  change BstLean.Part259.agent12275.charge ≤ BstLean.Part261.master12275.retainedCharge
  rw [show BstLean.Part261.master12275.retainedCharge =
    BstLean.Part259.scalar12275.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12275]
  norm_num [BstLean.Part259.agent12275, BstLean.Part259.scalar12275]

noncomputable def row12275 : BstLean.Part259.RowInputs 12275 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12275
    master12275 BstLean.Part262.actualCertificate12275
    BstLean.Part264b.N12275.covarianceEvent12275
    (BstLean.Part263.cell BstLean.Part263.scalarRow12275.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12275)
    BstLean.Part264b.N12275.covarianceEvent12275_measurable BstLean.Part264b.N12275.covarianceEvent12275_payment
    BstLean.Part264b.N12275.frame12275 (fun t c hw hc => ⟨root12275 t c hw hc⟩)
    BstLean.Part262.allocation12275 compatible12275

theorem energy12276 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12276.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12276, BstLean.Part263.cell12276]

noncomputable def root12276 (t : ℝ) (c : Ret 12276)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12276 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12276) :
    BstLean.Part243.RootInputs 12276 t c BstLean.Part259.agent12276.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12276
    BstLean.Part264b.N12276.sourceNumerics12276
    (by norm_num [BstLean.Part263.scalarRow12276])
    (by norm_num [BstLean.Part263.scalarRow12276])
    (by norm_num [BstLean.Part263.scalarRow12276])
    energy12276 BstLean.Part262.actualCertificate12276 t c hw hc

noncomputable def master12276 :
    MasterCertificate 12276 (BstLean.Part260.worldParameters 12276) BstLean.Part259.agent12276 := by
  rw [BstLean.Part260.parameters12276]
  exact BstLean.Part261.master12276

theorem compatible12276 : BstLean.Part259.agent12276.charge ≤ master12276.retainedCharge := by
  change BstLean.Part259.agent12276.charge ≤ BstLean.Part261.master12276.retainedCharge
  rw [show BstLean.Part261.master12276.retainedCharge =
    BstLean.Part259.scalar12276.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12276]
  norm_num [BstLean.Part259.agent12276, BstLean.Part259.scalar12276]

noncomputable def row12276 : BstLean.Part259.RowInputs 12276 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12276
    master12276 BstLean.Part262.actualCertificate12276
    BstLean.Part264b.N12276.covarianceEvent12276
    (BstLean.Part263.cell BstLean.Part263.scalarRow12276.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12276)
    BstLean.Part264b.N12276.covarianceEvent12276_measurable BstLean.Part264b.N12276.covarianceEvent12276_payment
    BstLean.Part264b.N12276.frame12276 (fun t c hw hc => ⟨root12276 t c hw hc⟩)
    BstLean.Part262.allocation12276 compatible12276

theorem energy12277 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12277.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12277, BstLean.Part263.cell12277]

noncomputable def root12277 (t : ℝ) (c : Ret 12277)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12277 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12277) :
    BstLean.Part243.RootInputs 12277 t c BstLean.Part259.agent12277.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12277
    BstLean.Part264b.N12277.sourceNumerics12277
    (by norm_num [BstLean.Part263.scalarRow12277])
    (by norm_num [BstLean.Part263.scalarRow12277])
    (by norm_num [BstLean.Part263.scalarRow12277])
    energy12277 BstLean.Part262.actualCertificate12277 t c hw hc

noncomputable def master12277 :
    MasterCertificate 12277 (BstLean.Part260.worldParameters 12277) BstLean.Part259.agent12277 := by
  rw [BstLean.Part260.parameters12277]
  exact BstLean.Part261.master12277

theorem compatible12277 : BstLean.Part259.agent12277.charge ≤ master12277.retainedCharge := by
  change BstLean.Part259.agent12277.charge ≤ BstLean.Part261.master12277.retainedCharge
  rw [show BstLean.Part261.master12277.retainedCharge =
    BstLean.Part259.scalar12277.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12277]
  norm_num [BstLean.Part259.agent12277, BstLean.Part259.scalar12277]

noncomputable def row12277 : BstLean.Part259.RowInputs 12277 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12277
    master12277 BstLean.Part262.actualCertificate12277
    BstLean.Part264b.N12277.covarianceEvent12277
    (BstLean.Part263.cell BstLean.Part263.scalarRow12277.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12277)
    BstLean.Part264b.N12277.covarianceEvent12277_measurable BstLean.Part264b.N12277.covarianceEvent12277_payment
    BstLean.Part264b.N12277.frame12277 (fun t c hw hc => ⟨root12277 t c hw hc⟩)
    BstLean.Part262.allocation12277 compatible12277

end BstLean.Part267
