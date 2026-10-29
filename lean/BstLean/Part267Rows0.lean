import BstLean.Part267Bridge
import BstLean.Part264bFamily
import BstLean.Part261Coverage
import BstLean.Part262ActualCoverage

namespace BstLean.Part267
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part192 BstLean.Part196

noncomputable def row12225 : BstLean.Part259.RowInputs 12225 :=
  BstLean.Part259.row12225

theorem energy12226 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12226.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12226, BstLean.Part263.cell12226]

noncomputable def root12226 (t : ℝ) (c : Ret 12226)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12226 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12226) :
    BstLean.Part243.RootInputs 12226 t c BstLean.Part259.agent12226.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12226
    BstLean.Part264.sourceNumerics12226
    (by norm_num [BstLean.Part263.scalarRow12226])
    (by norm_num [BstLean.Part263.scalarRow12226])
    (by norm_num [BstLean.Part263.scalarRow12226])
    energy12226 BstLean.Part262.actualCertificate12226 t c hw hc

noncomputable def master12226 :
    MasterCertificate 12226 (BstLean.Part260.worldParameters 12226) BstLean.Part259.agent12226 := by
  rw [BstLean.Part260.parameters12226]
  exact BstLean.Part261.master12226

theorem compatible12226 : BstLean.Part259.agent12226.charge ≤ master12226.retainedCharge := by
  change BstLean.Part259.agent12226.charge ≤ BstLean.Part261.master12226.retainedCharge
  rw [show BstLean.Part261.master12226.retainedCharge =
    BstLean.Part259.scalar12226.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12226]
  norm_num [BstLean.Part259.agent12226, BstLean.Part259.scalar12226]

noncomputable def row12226 : BstLean.Part259.RowInputs 12226 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12226
    master12226 BstLean.Part262.actualCertificate12226
    BstLean.Part264.covarianceEvent12226
    (BstLean.Part263.cell BstLean.Part263.scalarRow12226.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12226)
    BstLean.Part264.covarianceEvent12226_measurable BstLean.Part264.covarianceEvent12226_payment
    BstLean.Part264.frame12226 (fun t c hw hc => ⟨root12226 t c hw hc⟩)
    BstLean.Part262.allocation12226 compatible12226

theorem energy12227 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12227.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12227, BstLean.Part263.cell12227]

noncomputable def root12227 (t : ℝ) (c : Ret 12227)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12227 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12227) :
    BstLean.Part243.RootInputs 12227 t c BstLean.Part259.agent12227.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12227
    BstLean.Part264b.N12227.sourceNumerics12227
    (by norm_num [BstLean.Part263.scalarRow12227])
    (by norm_num [BstLean.Part263.scalarRow12227])
    (by norm_num [BstLean.Part263.scalarRow12227])
    energy12227 BstLean.Part262.actualCertificate12227 t c hw hc

noncomputable def master12227 :
    MasterCertificate 12227 (BstLean.Part260.worldParameters 12227) BstLean.Part259.agent12227 := by
  rw [BstLean.Part260.parameters12227]
  exact BstLean.Part261.master12227

theorem compatible12227 : BstLean.Part259.agent12227.charge ≤ master12227.retainedCharge := by
  change BstLean.Part259.agent12227.charge ≤ BstLean.Part261.master12227.retainedCharge
  rw [show BstLean.Part261.master12227.retainedCharge =
    BstLean.Part259.scalar12227.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12227]
  norm_num [BstLean.Part259.agent12227, BstLean.Part259.scalar12227]

noncomputable def row12227 : BstLean.Part259.RowInputs 12227 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12227
    master12227 BstLean.Part262.actualCertificate12227
    BstLean.Part264b.N12227.covarianceEvent12227
    (BstLean.Part263.cell BstLean.Part263.scalarRow12227.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12227)
    BstLean.Part264b.N12227.covarianceEvent12227_measurable BstLean.Part264b.N12227.covarianceEvent12227_payment
    BstLean.Part264b.N12227.frame12227 (fun t c hw hc => ⟨root12227 t c hw hc⟩)
    BstLean.Part262.allocation12227 compatible12227

theorem energy12228 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12228.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12228, BstLean.Part263.cell12228]

noncomputable def root12228 (t : ℝ) (c : Ret 12228)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12228 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12228) :
    BstLean.Part243.RootInputs 12228 t c BstLean.Part259.agent12228.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12228
    BstLean.Part264b.N12228.sourceNumerics12228
    (by norm_num [BstLean.Part263.scalarRow12228])
    (by norm_num [BstLean.Part263.scalarRow12228])
    (by norm_num [BstLean.Part263.scalarRow12228])
    energy12228 BstLean.Part262.actualCertificate12228 t c hw hc

noncomputable def master12228 :
    MasterCertificate 12228 (BstLean.Part260.worldParameters 12228) BstLean.Part259.agent12228 := by
  rw [BstLean.Part260.parameters12228]
  exact BstLean.Part261.master12228

theorem compatible12228 : BstLean.Part259.agent12228.charge ≤ master12228.retainedCharge := by
  change BstLean.Part259.agent12228.charge ≤ BstLean.Part261.master12228.retainedCharge
  rw [show BstLean.Part261.master12228.retainedCharge =
    BstLean.Part259.scalar12228.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12228]
  norm_num [BstLean.Part259.agent12228, BstLean.Part259.scalar12228]

noncomputable def row12228 : BstLean.Part259.RowInputs 12228 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12228
    master12228 BstLean.Part262.actualCertificate12228
    BstLean.Part264b.N12228.covarianceEvent12228
    (BstLean.Part263.cell BstLean.Part263.scalarRow12228.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12228)
    BstLean.Part264b.N12228.covarianceEvent12228_measurable BstLean.Part264b.N12228.covarianceEvent12228_payment
    BstLean.Part264b.N12228.frame12228 (fun t c hw hc => ⟨root12228 t c hw hc⟩)
    BstLean.Part262.allocation12228 compatible12228

theorem energy12229 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12229.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12229, BstLean.Part263.cell12229]

noncomputable def root12229 (t : ℝ) (c : Ret 12229)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12229 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12229) :
    BstLean.Part243.RootInputs 12229 t c BstLean.Part259.agent12229.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12229
    BstLean.Part264b.N12229.sourceNumerics12229
    (by norm_num [BstLean.Part263.scalarRow12229])
    (by norm_num [BstLean.Part263.scalarRow12229])
    (by norm_num [BstLean.Part263.scalarRow12229])
    energy12229 BstLean.Part262.actualCertificate12229 t c hw hc

noncomputable def master12229 :
    MasterCertificate 12229 (BstLean.Part260.worldParameters 12229) BstLean.Part259.agent12229 := by
  rw [BstLean.Part260.parameters12229]
  exact BstLean.Part261.master12229

theorem compatible12229 : BstLean.Part259.agent12229.charge ≤ master12229.retainedCharge := by
  change BstLean.Part259.agent12229.charge ≤ BstLean.Part261.master12229.retainedCharge
  rw [show BstLean.Part261.master12229.retainedCharge =
    BstLean.Part259.scalar12229.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12229]
  norm_num [BstLean.Part259.agent12229, BstLean.Part259.scalar12229]

noncomputable def row12229 : BstLean.Part259.RowInputs 12229 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12229
    master12229 BstLean.Part262.actualCertificate12229
    BstLean.Part264b.N12229.covarianceEvent12229
    (BstLean.Part263.cell BstLean.Part263.scalarRow12229.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12229)
    BstLean.Part264b.N12229.covarianceEvent12229_measurable BstLean.Part264b.N12229.covarianceEvent12229_payment
    BstLean.Part264b.N12229.frame12229 (fun t c hw hc => ⟨root12229 t c hw hc⟩)
    BstLean.Part262.allocation12229 compatible12229

end BstLean.Part267
