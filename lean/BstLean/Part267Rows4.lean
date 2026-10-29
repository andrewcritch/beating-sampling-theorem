import BstLean.Part267Bridge
import BstLean.Part264bFamily
import BstLean.Part261Coverage
import BstLean.Part262ActualCoverage

namespace BstLean.Part267
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part192 BstLean.Part196

theorem energy12302 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12302.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12302, BstLean.Part263.cell12302]

noncomputable def root12302 (t : ℝ) (c : Ret 12302)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12302 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12302) :
    BstLean.Part243.RootInputs 12302 t c BstLean.Part259.agent12302.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12302
    BstLean.Part264b.N12302.sourceNumerics12302
    (by norm_num [BstLean.Part263.scalarRow12302])
    (by norm_num [BstLean.Part263.scalarRow12302])
    (by norm_num [BstLean.Part263.scalarRow12302])
    energy12302 BstLean.Part262.actualCertificate12302 t c hw hc

noncomputable def master12302 :
    MasterCertificate 12302 (BstLean.Part260.worldParameters 12302) BstLean.Part259.agent12302 := by
  rw [BstLean.Part260.parameters12302]
  exact BstLean.Part261.master12302

theorem compatible12302 : BstLean.Part259.agent12302.charge ≤ master12302.retainedCharge := by
  change BstLean.Part259.agent12302.charge ≤ BstLean.Part261.master12302.retainedCharge
  rw [show BstLean.Part261.master12302.retainedCharge =
    BstLean.Part259.scalar12302.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12302]
  norm_num [BstLean.Part259.agent12302, BstLean.Part259.scalar12302]

noncomputable def row12302 : BstLean.Part259.RowInputs 12302 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12302
    master12302 BstLean.Part262.actualCertificate12302
    BstLean.Part264b.N12302.covarianceEvent12302
    (BstLean.Part263.cell BstLean.Part263.scalarRow12302.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12302)
    BstLean.Part264b.N12302.covarianceEvent12302_measurable BstLean.Part264b.N12302.covarianceEvent12302_payment
    BstLean.Part264b.N12302.frame12302 (fun t c hw hc => ⟨root12302 t c hw hc⟩)
    BstLean.Part262.allocation12302 compatible12302

theorem energy12303 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12303.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12303, BstLean.Part263.cell12303]

noncomputable def root12303 (t : ℝ) (c : Ret 12303)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12303 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12303) :
    BstLean.Part243.RootInputs 12303 t c BstLean.Part259.agent12303.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12303
    BstLean.Part264b.N12303.sourceNumerics12303
    (by norm_num [BstLean.Part263.scalarRow12303])
    (by norm_num [BstLean.Part263.scalarRow12303])
    (by norm_num [BstLean.Part263.scalarRow12303])
    energy12303 BstLean.Part262.actualCertificate12303 t c hw hc

noncomputable def master12303 :
    MasterCertificate 12303 (BstLean.Part260.worldParameters 12303) BstLean.Part259.agent12303 := by
  rw [BstLean.Part260.parameters12303]
  exact BstLean.Part261.master12303

theorem compatible12303 : BstLean.Part259.agent12303.charge ≤ master12303.retainedCharge := by
  change BstLean.Part259.agent12303.charge ≤ BstLean.Part261.master12303.retainedCharge
  rw [show BstLean.Part261.master12303.retainedCharge =
    BstLean.Part259.scalar12303.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12303]
  norm_num [BstLean.Part259.agent12303, BstLean.Part259.scalar12303]

noncomputable def row12303 : BstLean.Part259.RowInputs 12303 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12303
    master12303 BstLean.Part262.actualCertificate12303
    BstLean.Part264b.N12303.covarianceEvent12303
    (BstLean.Part263.cell BstLean.Part263.scalarRow12303.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12303)
    BstLean.Part264b.N12303.covarianceEvent12303_measurable BstLean.Part264b.N12303.covarianceEvent12303_payment
    BstLean.Part264b.N12303.frame12303 (fun t c hw hc => ⟨root12303 t c hw hc⟩)
    BstLean.Part262.allocation12303 compatible12303

theorem energy12304 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12304.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12304, BstLean.Part263.cell12304]

noncomputable def root12304 (t : ℝ) (c : Ret 12304)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12304 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12304) :
    BstLean.Part243.RootInputs 12304 t c BstLean.Part259.agent12304.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12304
    BstLean.Part264b.N12304.sourceNumerics12304
    (by norm_num [BstLean.Part263.scalarRow12304])
    (by norm_num [BstLean.Part263.scalarRow12304])
    (by norm_num [BstLean.Part263.scalarRow12304])
    energy12304 BstLean.Part262.actualCertificate12304 t c hw hc

noncomputable def master12304 :
    MasterCertificate 12304 (BstLean.Part260.worldParameters 12304) BstLean.Part259.agent12304 := by
  rw [BstLean.Part260.parameters12304]
  exact BstLean.Part261.master12304

theorem compatible12304 : BstLean.Part259.agent12304.charge ≤ master12304.retainedCharge := by
  change BstLean.Part259.agent12304.charge ≤ BstLean.Part261.master12304.retainedCharge
  rw [show BstLean.Part261.master12304.retainedCharge =
    BstLean.Part259.scalar12304.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12304]
  norm_num [BstLean.Part259.agent12304, BstLean.Part259.scalar12304]

noncomputable def row12304 : BstLean.Part259.RowInputs 12304 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12304
    master12304 BstLean.Part262.actualCertificate12304
    BstLean.Part264b.N12304.covarianceEvent12304
    (BstLean.Part263.cell BstLean.Part263.scalarRow12304.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12304)
    BstLean.Part264b.N12304.covarianceEvent12304_measurable BstLean.Part264b.N12304.covarianceEvent12304_payment
    BstLean.Part264b.N12304.frame12304 (fun t c hw hc => ⟨root12304 t c hw hc⟩)
    BstLean.Part262.allocation12304 compatible12304

theorem energy12305 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12305.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12305, BstLean.Part263.cell12305]

noncomputable def root12305 (t : ℝ) (c : Ret 12305)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12305 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12305) :
    BstLean.Part243.RootInputs 12305 t c BstLean.Part259.agent12305.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12305
    BstLean.Part264b.N12305.sourceNumerics12305
    (by norm_num [BstLean.Part263.scalarRow12305])
    (by norm_num [BstLean.Part263.scalarRow12305])
    (by norm_num [BstLean.Part263.scalarRow12305])
    energy12305 BstLean.Part262.actualCertificate12305 t c hw hc

noncomputable def master12305 :
    MasterCertificate 12305 (BstLean.Part260.worldParameters 12305) BstLean.Part259.agent12305 := by
  rw [BstLean.Part260.parameters12305]
  exact BstLean.Part261.master12305

theorem compatible12305 : BstLean.Part259.agent12305.charge ≤ master12305.retainedCharge := by
  change BstLean.Part259.agent12305.charge ≤ BstLean.Part261.master12305.retainedCharge
  rw [show BstLean.Part261.master12305.retainedCharge =
    BstLean.Part259.scalar12305.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12305]
  norm_num [BstLean.Part259.agent12305, BstLean.Part259.scalar12305]

noncomputable def row12305 : BstLean.Part259.RowInputs 12305 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12305
    master12305 BstLean.Part262.actualCertificate12305
    BstLean.Part264b.N12305.covarianceEvent12305
    (BstLean.Part263.cell BstLean.Part263.scalarRow12305.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12305)
    BstLean.Part264b.N12305.covarianceEvent12305_measurable BstLean.Part264b.N12305.covarianceEvent12305_payment
    BstLean.Part264b.N12305.frame12305 (fun t c hw hc => ⟨root12305 t c hw hc⟩)
    BstLean.Part262.allocation12305 compatible12305

theorem energy12306 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12306.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12306, BstLean.Part263.cell12306]

noncomputable def root12306 (t : ℝ) (c : Ret 12306)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12306 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12306) :
    BstLean.Part243.RootInputs 12306 t c BstLean.Part259.agent12306.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12306
    BstLean.Part264b.N12306.sourceNumerics12306
    (by norm_num [BstLean.Part263.scalarRow12306])
    (by norm_num [BstLean.Part263.scalarRow12306])
    (by norm_num [BstLean.Part263.scalarRow12306])
    energy12306 BstLean.Part262.actualCertificate12306 t c hw hc

noncomputable def master12306 :
    MasterCertificate 12306 (BstLean.Part260.worldParameters 12306) BstLean.Part259.agent12306 := by
  rw [BstLean.Part260.parameters12306]
  exact BstLean.Part261.master12306

theorem compatible12306 : BstLean.Part259.agent12306.charge ≤ master12306.retainedCharge := by
  change BstLean.Part259.agent12306.charge ≤ BstLean.Part261.master12306.retainedCharge
  rw [show BstLean.Part261.master12306.retainedCharge =
    BstLean.Part259.scalar12306.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12306]
  norm_num [BstLean.Part259.agent12306, BstLean.Part259.scalar12306]

noncomputable def row12306 : BstLean.Part259.RowInputs 12306 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12306
    master12306 BstLean.Part262.actualCertificate12306
    BstLean.Part264b.N12306.covarianceEvent12306
    (BstLean.Part263.cell BstLean.Part263.scalarRow12306.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12306)
    BstLean.Part264b.N12306.covarianceEvent12306_measurable BstLean.Part264b.N12306.covarianceEvent12306_payment
    BstLean.Part264b.N12306.frame12306 (fun t c hw hc => ⟨root12306 t c hw hc⟩)
    BstLean.Part262.allocation12306 compatible12306

theorem energy12307 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12307.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12307, BstLean.Part263.cell12307]

noncomputable def root12307 (t : ℝ) (c : Ret 12307)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12307 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12307) :
    BstLean.Part243.RootInputs 12307 t c BstLean.Part259.agent12307.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12307
    BstLean.Part264b.N12307.sourceNumerics12307
    (by norm_num [BstLean.Part263.scalarRow12307])
    (by norm_num [BstLean.Part263.scalarRow12307])
    (by norm_num [BstLean.Part263.scalarRow12307])
    energy12307 BstLean.Part262.actualCertificate12307 t c hw hc

noncomputable def master12307 :
    MasterCertificate 12307 (BstLean.Part260.worldParameters 12307) BstLean.Part259.agent12307 := by
  rw [BstLean.Part260.parameters12307]
  exact BstLean.Part261.master12307

theorem compatible12307 : BstLean.Part259.agent12307.charge ≤ master12307.retainedCharge := by
  change BstLean.Part259.agent12307.charge ≤ BstLean.Part261.master12307.retainedCharge
  rw [show BstLean.Part261.master12307.retainedCharge =
    BstLean.Part259.scalar12307.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12307]
  norm_num [BstLean.Part259.agent12307, BstLean.Part259.scalar12307]

noncomputable def row12307 : BstLean.Part259.RowInputs 12307 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12307
    master12307 BstLean.Part262.actualCertificate12307
    BstLean.Part264b.N12307.covarianceEvent12307
    (BstLean.Part263.cell BstLean.Part263.scalarRow12307.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12307)
    BstLean.Part264b.N12307.covarianceEvent12307_measurable BstLean.Part264b.N12307.covarianceEvent12307_payment
    BstLean.Part264b.N12307.frame12307 (fun t c hw hc => ⟨root12307 t c hw hc⟩)
    BstLean.Part262.allocation12307 compatible12307

theorem energy12308 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12308.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12308, BstLean.Part263.cell12308]

noncomputable def root12308 (t : ℝ) (c : Ret 12308)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12308 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12308) :
    BstLean.Part243.RootInputs 12308 t c BstLean.Part259.agent12308.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12308
    BstLean.Part264b.N12308.sourceNumerics12308
    (by norm_num [BstLean.Part263.scalarRow12308])
    (by norm_num [BstLean.Part263.scalarRow12308])
    (by norm_num [BstLean.Part263.scalarRow12308])
    energy12308 BstLean.Part262.actualCertificate12308 t c hw hc

noncomputable def master12308 :
    MasterCertificate 12308 (BstLean.Part260.worldParameters 12308) BstLean.Part259.agent12308 := by
  rw [BstLean.Part260.parameters12308]
  exact BstLean.Part261.master12308

theorem compatible12308 : BstLean.Part259.agent12308.charge ≤ master12308.retainedCharge := by
  change BstLean.Part259.agent12308.charge ≤ BstLean.Part261.master12308.retainedCharge
  rw [show BstLean.Part261.master12308.retainedCharge =
    BstLean.Part259.scalar12308.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12308]
  norm_num [BstLean.Part259.agent12308, BstLean.Part259.scalar12308]

noncomputable def row12308 : BstLean.Part259.RowInputs 12308 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12308
    master12308 BstLean.Part262.actualCertificate12308
    BstLean.Part264b.N12308.covarianceEvent12308
    (BstLean.Part263.cell BstLean.Part263.scalarRow12308.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12308)
    BstLean.Part264b.N12308.covarianceEvent12308_measurable BstLean.Part264b.N12308.covarianceEvent12308_payment
    BstLean.Part264b.N12308.frame12308 (fun t c hw hc => ⟨root12308 t c hw hc⟩)
    BstLean.Part262.allocation12308 compatible12308

theorem energy12309 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12309.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12309, BstLean.Part263.cell12309]

noncomputable def root12309 (t : ℝ) (c : Ret 12309)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12309 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12309) :
    BstLean.Part243.RootInputs 12309 t c BstLean.Part259.agent12309.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12309
    BstLean.Part264b.N12309.sourceNumerics12309
    (by norm_num [BstLean.Part263.scalarRow12309])
    (by norm_num [BstLean.Part263.scalarRow12309])
    (by norm_num [BstLean.Part263.scalarRow12309])
    energy12309 BstLean.Part262.actualCertificate12309 t c hw hc

noncomputable def master12309 :
    MasterCertificate 12309 (BstLean.Part260.worldParameters 12309) BstLean.Part259.agent12309 := by
  rw [BstLean.Part260.parameters12309]
  exact BstLean.Part261.master12309

theorem compatible12309 : BstLean.Part259.agent12309.charge ≤ master12309.retainedCharge := by
  change BstLean.Part259.agent12309.charge ≤ BstLean.Part261.master12309.retainedCharge
  rw [show BstLean.Part261.master12309.retainedCharge =
    BstLean.Part259.scalar12309.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12309]
  norm_num [BstLean.Part259.agent12309, BstLean.Part259.scalar12309]

noncomputable def row12309 : BstLean.Part259.RowInputs 12309 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12309
    master12309 BstLean.Part262.actualCertificate12309
    BstLean.Part264b.N12309.covarianceEvent12309
    (BstLean.Part263.cell BstLean.Part263.scalarRow12309.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12309)
    BstLean.Part264b.N12309.covarianceEvent12309_measurable BstLean.Part264b.N12309.covarianceEvent12309_payment
    BstLean.Part264b.N12309.frame12309 (fun t c hw hc => ⟨root12309 t c hw hc⟩)
    BstLean.Part262.allocation12309 compatible12309

theorem energy12310 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12310.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12310, BstLean.Part263.cell12310]

noncomputable def root12310 (t : ℝ) (c : Ret 12310)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12310 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12310) :
    BstLean.Part243.RootInputs 12310 t c BstLean.Part259.agent12310.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12310
    BstLean.Part264b.N12310.sourceNumerics12310
    (by norm_num [BstLean.Part263.scalarRow12310])
    (by norm_num [BstLean.Part263.scalarRow12310])
    (by norm_num [BstLean.Part263.scalarRow12310])
    energy12310 BstLean.Part262.actualCertificate12310 t c hw hc

noncomputable def master12310 :
    MasterCertificate 12310 (BstLean.Part260.worldParameters 12310) BstLean.Part259.agent12310 := by
  rw [BstLean.Part260.parameters12310]
  exact BstLean.Part261.master12310

theorem compatible12310 : BstLean.Part259.agent12310.charge ≤ master12310.retainedCharge := by
  change BstLean.Part259.agent12310.charge ≤ BstLean.Part261.master12310.retainedCharge
  rw [show BstLean.Part261.master12310.retainedCharge =
    BstLean.Part259.scalar12310.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12310]
  norm_num [BstLean.Part259.agent12310, BstLean.Part259.scalar12310]

noncomputable def row12310 : BstLean.Part259.RowInputs 12310 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12310
    master12310 BstLean.Part262.actualCertificate12310
    BstLean.Part264b.N12310.covarianceEvent12310
    (BstLean.Part263.cell BstLean.Part263.scalarRow12310.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12310)
    BstLean.Part264b.N12310.covarianceEvent12310_measurable BstLean.Part264b.N12310.covarianceEvent12310_payment
    BstLean.Part264b.N12310.frame12310 (fun t c hw hc => ⟨root12310 t c hw hc⟩)
    BstLean.Part262.allocation12310 compatible12310

theorem energy12311 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12311.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12311, BstLean.Part263.cell12311]

noncomputable def root12311 (t : ℝ) (c : Ret 12311)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12311 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12311) :
    BstLean.Part243.RootInputs 12311 t c BstLean.Part259.agent12311.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12311
    BstLean.Part264b.N12311.sourceNumerics12311
    (by norm_num [BstLean.Part263.scalarRow12311])
    (by norm_num [BstLean.Part263.scalarRow12311])
    (by norm_num [BstLean.Part263.scalarRow12311])
    energy12311 BstLean.Part262.actualCertificate12311 t c hw hc

noncomputable def master12311 :
    MasterCertificate 12311 (BstLean.Part260.worldParameters 12311) BstLean.Part259.agent12311 := by
  rw [BstLean.Part260.parameters12311]
  exact BstLean.Part261.master12311

theorem compatible12311 : BstLean.Part259.agent12311.charge ≤ master12311.retainedCharge := by
  change BstLean.Part259.agent12311.charge ≤ BstLean.Part261.master12311.retainedCharge
  rw [show BstLean.Part261.master12311.retainedCharge =
    BstLean.Part259.scalar12311.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12311]
  norm_num [BstLean.Part259.agent12311, BstLean.Part259.scalar12311]

noncomputable def row12311 : BstLean.Part259.RowInputs 12311 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12311
    master12311 BstLean.Part262.actualCertificate12311
    BstLean.Part264b.N12311.covarianceEvent12311
    (BstLean.Part263.cell BstLean.Part263.scalarRow12311.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12311)
    BstLean.Part264b.N12311.covarianceEvent12311_measurable BstLean.Part264b.N12311.covarianceEvent12311_payment
    BstLean.Part264b.N12311.frame12311 (fun t c hw hc => ⟨root12311 t c hw hc⟩)
    BstLean.Part262.allocation12311 compatible12311

theorem energy12312 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12312.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12312, BstLean.Part263.cell12312]

noncomputable def root12312 (t : ℝ) (c : Ret 12312)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12312 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12312) :
    BstLean.Part243.RootInputs 12312 t c BstLean.Part259.agent12312.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12312
    BstLean.Part264b.N12312.sourceNumerics12312
    (by norm_num [BstLean.Part263.scalarRow12312])
    (by norm_num [BstLean.Part263.scalarRow12312])
    (by norm_num [BstLean.Part263.scalarRow12312])
    energy12312 BstLean.Part262.actualCertificate12312 t c hw hc

noncomputable def master12312 :
    MasterCertificate 12312 (BstLean.Part260.worldParameters 12312) BstLean.Part259.agent12312 := by
  rw [BstLean.Part260.parameters12312]
  exact BstLean.Part261.master12312

theorem compatible12312 : BstLean.Part259.agent12312.charge ≤ master12312.retainedCharge := by
  change BstLean.Part259.agent12312.charge ≤ BstLean.Part261.master12312.retainedCharge
  rw [show BstLean.Part261.master12312.retainedCharge =
    BstLean.Part259.scalar12312.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12312]
  norm_num [BstLean.Part259.agent12312, BstLean.Part259.scalar12312]

noncomputable def row12312 : BstLean.Part259.RowInputs 12312 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12312
    master12312 BstLean.Part262.actualCertificate12312
    BstLean.Part264b.N12312.covarianceEvent12312
    (BstLean.Part263.cell BstLean.Part263.scalarRow12312.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12312)
    BstLean.Part264b.N12312.covarianceEvent12312_measurable BstLean.Part264b.N12312.covarianceEvent12312_payment
    BstLean.Part264b.N12312.frame12312 (fun t c hw hc => ⟨root12312 t c hw hc⟩)
    BstLean.Part262.allocation12312 compatible12312

theorem energy12313 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12313.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12313, BstLean.Part263.cell12313]

noncomputable def root12313 (t : ℝ) (c : Ret 12313)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12313 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12313) :
    BstLean.Part243.RootInputs 12313 t c BstLean.Part259.agent12313.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12313
    BstLean.Part264b.N12313.sourceNumerics12313
    (by norm_num [BstLean.Part263.scalarRow12313])
    (by norm_num [BstLean.Part263.scalarRow12313])
    (by norm_num [BstLean.Part263.scalarRow12313])
    energy12313 BstLean.Part262.actualCertificate12313 t c hw hc

noncomputable def master12313 :
    MasterCertificate 12313 (BstLean.Part260.worldParameters 12313) BstLean.Part259.agent12313 := by
  rw [BstLean.Part260.parameters12313]
  exact BstLean.Part261.master12313

theorem compatible12313 : BstLean.Part259.agent12313.charge ≤ master12313.retainedCharge := by
  change BstLean.Part259.agent12313.charge ≤ BstLean.Part261.master12313.retainedCharge
  rw [show BstLean.Part261.master12313.retainedCharge =
    BstLean.Part259.scalar12313.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12313]
  norm_num [BstLean.Part259.agent12313, BstLean.Part259.scalar12313]

noncomputable def row12313 : BstLean.Part259.RowInputs 12313 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12313
    master12313 BstLean.Part262.actualCertificate12313
    BstLean.Part264b.N12313.covarianceEvent12313
    (BstLean.Part263.cell BstLean.Part263.scalarRow12313.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12313)
    BstLean.Part264b.N12313.covarianceEvent12313_measurable BstLean.Part264b.N12313.covarianceEvent12313_payment
    BstLean.Part264b.N12313.frame12313 (fun t c hw hc => ⟨root12313 t c hw hc⟩)
    BstLean.Part262.allocation12313 compatible12313

theorem energy12314 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12314.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12314, BstLean.Part263.cell12314]

noncomputable def root12314 (t : ℝ) (c : Ret 12314)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12314 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12314) :
    BstLean.Part243.RootInputs 12314 t c BstLean.Part259.agent12314.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12314
    BstLean.Part264b.N12314.sourceNumerics12314
    (by norm_num [BstLean.Part263.scalarRow12314])
    (by norm_num [BstLean.Part263.scalarRow12314])
    (by norm_num [BstLean.Part263.scalarRow12314])
    energy12314 BstLean.Part262.actualCertificate12314 t c hw hc

noncomputable def master12314 :
    MasterCertificate 12314 (BstLean.Part260.worldParameters 12314) BstLean.Part259.agent12314 := by
  rw [BstLean.Part260.parameters12314]
  exact BstLean.Part261.master12314

theorem compatible12314 : BstLean.Part259.agent12314.charge ≤ master12314.retainedCharge := by
  change BstLean.Part259.agent12314.charge ≤ BstLean.Part261.master12314.retainedCharge
  rw [show BstLean.Part261.master12314.retainedCharge =
    BstLean.Part259.scalar12314.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12314]
  norm_num [BstLean.Part259.agent12314, BstLean.Part259.scalar12314]

noncomputable def row12314 : BstLean.Part259.RowInputs 12314 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12314
    master12314 BstLean.Part262.actualCertificate12314
    BstLean.Part264b.N12314.covarianceEvent12314
    (BstLean.Part263.cell BstLean.Part263.scalarRow12314.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12314)
    BstLean.Part264b.N12314.covarianceEvent12314_measurable BstLean.Part264b.N12314.covarianceEvent12314_payment
    BstLean.Part264b.N12314.frame12314 (fun t c hw hc => ⟨root12314 t c hw hc⟩)
    BstLean.Part262.allocation12314 compatible12314

theorem energy12315 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12315.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12315, BstLean.Part263.cell12315]

noncomputable def root12315 (t : ℝ) (c : Ret 12315)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12315 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12315) :
    BstLean.Part243.RootInputs 12315 t c BstLean.Part259.agent12315.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12315
    BstLean.Part264b.N12315.sourceNumerics12315
    (by norm_num [BstLean.Part263.scalarRow12315])
    (by norm_num [BstLean.Part263.scalarRow12315])
    (by norm_num [BstLean.Part263.scalarRow12315])
    energy12315 BstLean.Part262.actualCertificate12315 t c hw hc

noncomputable def master12315 :
    MasterCertificate 12315 (BstLean.Part260.worldParameters 12315) BstLean.Part259.agent12315 := by
  rw [BstLean.Part260.parameters12315]
  exact BstLean.Part261.master12315

theorem compatible12315 : BstLean.Part259.agent12315.charge ≤ master12315.retainedCharge := by
  change BstLean.Part259.agent12315.charge ≤ BstLean.Part261.master12315.retainedCharge
  rw [show BstLean.Part261.master12315.retainedCharge =
    BstLean.Part259.scalar12315.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12315]
  norm_num [BstLean.Part259.agent12315, BstLean.Part259.scalar12315]

noncomputable def row12315 : BstLean.Part259.RowInputs 12315 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12315
    master12315 BstLean.Part262.actualCertificate12315
    BstLean.Part264b.N12315.covarianceEvent12315
    (BstLean.Part263.cell BstLean.Part263.scalarRow12315.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12315)
    BstLean.Part264b.N12315.covarianceEvent12315_measurable BstLean.Part264b.N12315.covarianceEvent12315_payment
    BstLean.Part264b.N12315.frame12315 (fun t c hw hc => ⟨root12315 t c hw hc⟩)
    BstLean.Part262.allocation12315 compatible12315

theorem energy12316 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12316.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12316, BstLean.Part263.cell12316]

noncomputable def root12316 (t : ℝ) (c : Ret 12316)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12316 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12316) :
    BstLean.Part243.RootInputs 12316 t c BstLean.Part259.agent12316.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12316
    BstLean.Part264b.N12316.sourceNumerics12316
    (by norm_num [BstLean.Part263.scalarRow12316])
    (by norm_num [BstLean.Part263.scalarRow12316])
    (by norm_num [BstLean.Part263.scalarRow12316])
    energy12316 BstLean.Part262.actualCertificate12316 t c hw hc

noncomputable def master12316 :
    MasterCertificate 12316 (BstLean.Part260.worldParameters 12316) BstLean.Part259.agent12316 := by
  rw [BstLean.Part260.parameters12316]
  exact BstLean.Part261.master12316

theorem compatible12316 : BstLean.Part259.agent12316.charge ≤ master12316.retainedCharge := by
  change BstLean.Part259.agent12316.charge ≤ BstLean.Part261.master12316.retainedCharge
  rw [show BstLean.Part261.master12316.retainedCharge =
    BstLean.Part259.scalar12316.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12316]
  norm_num [BstLean.Part259.agent12316, BstLean.Part259.scalar12316]

noncomputable def row12316 : BstLean.Part259.RowInputs 12316 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12316
    master12316 BstLean.Part262.actualCertificate12316
    BstLean.Part264b.N12316.covarianceEvent12316
    (BstLean.Part263.cell BstLean.Part263.scalarRow12316.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12316)
    BstLean.Part264b.N12316.covarianceEvent12316_measurable BstLean.Part264b.N12316.covarianceEvent12316_payment
    BstLean.Part264b.N12316.frame12316 (fun t c hw hc => ⟨root12316 t c hw hc⟩)
    BstLean.Part262.allocation12316 compatible12316

theorem energy12317 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12317.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12317, BstLean.Part263.cell12317]

noncomputable def root12317 (t : ℝ) (c : Ret 12317)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12317 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12317) :
    BstLean.Part243.RootInputs 12317 t c BstLean.Part259.agent12317.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12317
    BstLean.Part264b.N12317.sourceNumerics12317
    (by norm_num [BstLean.Part263.scalarRow12317])
    (by norm_num [BstLean.Part263.scalarRow12317])
    (by norm_num [BstLean.Part263.scalarRow12317])
    energy12317 BstLean.Part262.actualCertificate12317 t c hw hc

noncomputable def master12317 :
    MasterCertificate 12317 (BstLean.Part260.worldParameters 12317) BstLean.Part259.agent12317 := by
  rw [BstLean.Part260.parameters12317]
  exact BstLean.Part261.master12317

theorem compatible12317 : BstLean.Part259.agent12317.charge ≤ master12317.retainedCharge := by
  change BstLean.Part259.agent12317.charge ≤ BstLean.Part261.master12317.retainedCharge
  rw [show BstLean.Part261.master12317.retainedCharge =
    BstLean.Part259.scalar12317.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12317]
  norm_num [BstLean.Part259.agent12317, BstLean.Part259.scalar12317]

noncomputable def row12317 : BstLean.Part259.RowInputs 12317 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12317
    master12317 BstLean.Part262.actualCertificate12317
    BstLean.Part264b.N12317.covarianceEvent12317
    (BstLean.Part263.cell BstLean.Part263.scalarRow12317.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12317)
    BstLean.Part264b.N12317.covarianceEvent12317_measurable BstLean.Part264b.N12317.covarianceEvent12317_payment
    BstLean.Part264b.N12317.frame12317 (fun t c hw hc => ⟨root12317 t c hw hc⟩)
    BstLean.Part262.allocation12317 compatible12317

theorem energy12318 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12318.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12318, BstLean.Part263.cell12318]

noncomputable def root12318 (t : ℝ) (c : Ret 12318)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12318 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12318) :
    BstLean.Part243.RootInputs 12318 t c BstLean.Part259.agent12318.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12318
    BstLean.Part264b.N12318.sourceNumerics12318
    (by norm_num [BstLean.Part263.scalarRow12318])
    (by norm_num [BstLean.Part263.scalarRow12318])
    (by norm_num [BstLean.Part263.scalarRow12318])
    energy12318 BstLean.Part262.actualCertificate12318 t c hw hc

noncomputable def master12318 :
    MasterCertificate 12318 (BstLean.Part260.worldParameters 12318) BstLean.Part259.agent12318 := by
  rw [BstLean.Part260.parameters12318]
  exact BstLean.Part261.master12318

theorem compatible12318 : BstLean.Part259.agent12318.charge ≤ master12318.retainedCharge := by
  change BstLean.Part259.agent12318.charge ≤ BstLean.Part261.master12318.retainedCharge
  rw [show BstLean.Part261.master12318.retainedCharge =
    BstLean.Part259.scalar12318.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12318]
  norm_num [BstLean.Part259.agent12318, BstLean.Part259.scalar12318]

noncomputable def row12318 : BstLean.Part259.RowInputs 12318 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12318
    master12318 BstLean.Part262.actualCertificate12318
    BstLean.Part264b.N12318.covarianceEvent12318
    (BstLean.Part263.cell BstLean.Part263.scalarRow12318.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12318)
    BstLean.Part264b.N12318.covarianceEvent12318_measurable BstLean.Part264b.N12318.covarianceEvent12318_payment
    BstLean.Part264b.N12318.frame12318 (fun t c hw hc => ⟨root12318 t c hw hc⟩)
    BstLean.Part262.allocation12318 compatible12318

theorem energy12319 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12319.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12319, BstLean.Part263.cell12319]

noncomputable def root12319 (t : ℝ) (c : Ret 12319)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12319 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12319) :
    BstLean.Part243.RootInputs 12319 t c BstLean.Part259.agent12319.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12319
    BstLean.Part264b.N12319.sourceNumerics12319
    (by norm_num [BstLean.Part263.scalarRow12319])
    (by norm_num [BstLean.Part263.scalarRow12319])
    (by norm_num [BstLean.Part263.scalarRow12319])
    energy12319 BstLean.Part262.actualCertificate12319 t c hw hc

noncomputable def master12319 :
    MasterCertificate 12319 (BstLean.Part260.worldParameters 12319) BstLean.Part259.agent12319 := by
  rw [BstLean.Part260.parameters12319]
  exact BstLean.Part261.master12319

theorem compatible12319 : BstLean.Part259.agent12319.charge ≤ master12319.retainedCharge := by
  change BstLean.Part259.agent12319.charge ≤ BstLean.Part261.master12319.retainedCharge
  rw [show BstLean.Part261.master12319.retainedCharge =
    BstLean.Part259.scalar12319.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12319]
  norm_num [BstLean.Part259.agent12319, BstLean.Part259.scalar12319]

noncomputable def row12319 : BstLean.Part259.RowInputs 12319 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12319
    master12319 BstLean.Part262.actualCertificate12319
    BstLean.Part264b.N12319.covarianceEvent12319
    (BstLean.Part263.cell BstLean.Part263.scalarRow12319.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12319)
    BstLean.Part264b.N12319.covarianceEvent12319_measurable BstLean.Part264b.N12319.covarianceEvent12319_payment
    BstLean.Part264b.N12319.frame12319 (fun t c hw hc => ⟨root12319 t c hw hc⟩)
    BstLean.Part262.allocation12319 compatible12319

theorem energy12320 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12320.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12320, BstLean.Part263.cell12320]

noncomputable def root12320 (t : ℝ) (c : Ret 12320)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12320 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12320) :
    BstLean.Part243.RootInputs 12320 t c BstLean.Part259.agent12320.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12320
    BstLean.Part264b.N12320.sourceNumerics12320
    (by norm_num [BstLean.Part263.scalarRow12320])
    (by norm_num [BstLean.Part263.scalarRow12320])
    (by norm_num [BstLean.Part263.scalarRow12320])
    energy12320 BstLean.Part262.actualCertificate12320 t c hw hc

noncomputable def master12320 :
    MasterCertificate 12320 (BstLean.Part260.worldParameters 12320) BstLean.Part259.agent12320 := by
  rw [BstLean.Part260.parameters12320]
  exact BstLean.Part261.master12320

theorem compatible12320 : BstLean.Part259.agent12320.charge ≤ master12320.retainedCharge := by
  change BstLean.Part259.agent12320.charge ≤ BstLean.Part261.master12320.retainedCharge
  rw [show BstLean.Part261.master12320.retainedCharge =
    BstLean.Part259.scalar12320.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12320]
  norm_num [BstLean.Part259.agent12320, BstLean.Part259.scalar12320]

noncomputable def row12320 : BstLean.Part259.RowInputs 12320 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12320
    master12320 BstLean.Part262.actualCertificate12320
    BstLean.Part264b.N12320.covarianceEvent12320
    (BstLean.Part263.cell BstLean.Part263.scalarRow12320.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12320)
    BstLean.Part264b.N12320.covarianceEvent12320_measurable BstLean.Part264b.N12320.covarianceEvent12320_payment
    BstLean.Part264b.N12320.frame12320 (fun t c hw hc => ⟨root12320 t c hw hc⟩)
    BstLean.Part262.allocation12320 compatible12320

theorem energy12321 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12321.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12321, BstLean.Part263.cell12321]

noncomputable def root12321 (t : ℝ) (c : Ret 12321)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12321 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12321) :
    BstLean.Part243.RootInputs 12321 t c BstLean.Part259.agent12321.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12321
    BstLean.Part264b.N12321.sourceNumerics12321
    (by norm_num [BstLean.Part263.scalarRow12321])
    (by norm_num [BstLean.Part263.scalarRow12321])
    (by norm_num [BstLean.Part263.scalarRow12321])
    energy12321 BstLean.Part262.actualCertificate12321 t c hw hc

noncomputable def master12321 :
    MasterCertificate 12321 (BstLean.Part260.worldParameters 12321) BstLean.Part259.agent12321 := by
  rw [BstLean.Part260.parameters12321]
  exact BstLean.Part261.master12321

theorem compatible12321 : BstLean.Part259.agent12321.charge ≤ master12321.retainedCharge := by
  change BstLean.Part259.agent12321.charge ≤ BstLean.Part261.master12321.retainedCharge
  rw [show BstLean.Part261.master12321.retainedCharge =
    BstLean.Part259.scalar12321.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12321]
  norm_num [BstLean.Part259.agent12321, BstLean.Part259.scalar12321]

noncomputable def row12321 : BstLean.Part259.RowInputs 12321 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12321
    master12321 BstLean.Part262.actualCertificate12321
    BstLean.Part264b.N12321.covarianceEvent12321
    (BstLean.Part263.cell BstLean.Part263.scalarRow12321.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12321)
    BstLean.Part264b.N12321.covarianceEvent12321_measurable BstLean.Part264b.N12321.covarianceEvent12321_payment
    BstLean.Part264b.N12321.frame12321 (fun t c hw hc => ⟨root12321 t c hw hc⟩)
    BstLean.Part262.allocation12321 compatible12321

theorem energy12322 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12322.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12322, BstLean.Part263.cell12322]

noncomputable def root12322 (t : ℝ) (c : Ret 12322)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12322 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12322) :
    BstLean.Part243.RootInputs 12322 t c BstLean.Part259.agent12322.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12322
    BstLean.Part264b.N12322.sourceNumerics12322
    (by norm_num [BstLean.Part263.scalarRow12322])
    (by norm_num [BstLean.Part263.scalarRow12322])
    (by norm_num [BstLean.Part263.scalarRow12322])
    energy12322 BstLean.Part262.actualCertificate12322 t c hw hc

noncomputable def master12322 :
    MasterCertificate 12322 (BstLean.Part260.worldParameters 12322) BstLean.Part259.agent12322 := by
  rw [BstLean.Part260.parameters12322]
  exact BstLean.Part261.master12322

theorem compatible12322 : BstLean.Part259.agent12322.charge ≤ master12322.retainedCharge := by
  change BstLean.Part259.agent12322.charge ≤ BstLean.Part261.master12322.retainedCharge
  rw [show BstLean.Part261.master12322.retainedCharge =
    BstLean.Part259.scalar12322.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12322]
  norm_num [BstLean.Part259.agent12322, BstLean.Part259.scalar12322]

noncomputable def row12322 : BstLean.Part259.RowInputs 12322 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12322
    master12322 BstLean.Part262.actualCertificate12322
    BstLean.Part264b.N12322.covarianceEvent12322
    (BstLean.Part263.cell BstLean.Part263.scalarRow12322.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12322)
    BstLean.Part264b.N12322.covarianceEvent12322_measurable BstLean.Part264b.N12322.covarianceEvent12322_payment
    BstLean.Part264b.N12322.frame12322 (fun t c hw hc => ⟨root12322 t c hw hc⟩)
    BstLean.Part262.allocation12322 compatible12322

theorem energy12323 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12323.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12323, BstLean.Part263.cell12323]

noncomputable def root12323 (t : ℝ) (c : Ret 12323)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12323 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12323) :
    BstLean.Part243.RootInputs 12323 t c BstLean.Part259.agent12323.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12323
    BstLean.Part264b.N12323.sourceNumerics12323
    (by norm_num [BstLean.Part263.scalarRow12323])
    (by norm_num [BstLean.Part263.scalarRow12323])
    (by norm_num [BstLean.Part263.scalarRow12323])
    energy12323 BstLean.Part262.actualCertificate12323 t c hw hc

noncomputable def master12323 :
    MasterCertificate 12323 (BstLean.Part260.worldParameters 12323) BstLean.Part259.agent12323 := by
  rw [BstLean.Part260.parameters12323]
  exact BstLean.Part261.master12323

theorem compatible12323 : BstLean.Part259.agent12323.charge ≤ master12323.retainedCharge := by
  change BstLean.Part259.agent12323.charge ≤ BstLean.Part261.master12323.retainedCharge
  rw [show BstLean.Part261.master12323.retainedCharge =
    BstLean.Part259.scalar12323.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12323]
  norm_num [BstLean.Part259.agent12323, BstLean.Part259.scalar12323]

noncomputable def row12323 : BstLean.Part259.RowInputs 12323 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12323
    master12323 BstLean.Part262.actualCertificate12323
    BstLean.Part264b.N12323.covarianceEvent12323
    (BstLean.Part263.cell BstLean.Part263.scalarRow12323.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12323)
    BstLean.Part264b.N12323.covarianceEvent12323_measurable BstLean.Part264b.N12323.covarianceEvent12323_payment
    BstLean.Part264b.N12323.frame12323 (fun t c hw hc => ⟨root12323 t c hw hc⟩)
    BstLean.Part262.allocation12323 compatible12323

theorem energy12324 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12324.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12324, BstLean.Part263.cell12324]

noncomputable def root12324 (t : ℝ) (c : Ret 12324)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12324 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12324) :
    BstLean.Part243.RootInputs 12324 t c BstLean.Part259.agent12324.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12324
    BstLean.Part264b.N12324.sourceNumerics12324
    (by norm_num [BstLean.Part263.scalarRow12324])
    (by norm_num [BstLean.Part263.scalarRow12324])
    (by norm_num [BstLean.Part263.scalarRow12324])
    energy12324 BstLean.Part262.actualCertificate12324 t c hw hc

noncomputable def master12324 :
    MasterCertificate 12324 (BstLean.Part260.worldParameters 12324) BstLean.Part259.agent12324 := by
  rw [BstLean.Part260.parameters12324]
  exact BstLean.Part261.master12324

theorem compatible12324 : BstLean.Part259.agent12324.charge ≤ master12324.retainedCharge := by
  change BstLean.Part259.agent12324.charge ≤ BstLean.Part261.master12324.retainedCharge
  rw [show BstLean.Part261.master12324.retainedCharge =
    BstLean.Part259.scalar12324.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12324]
  norm_num [BstLean.Part259.agent12324, BstLean.Part259.scalar12324]

noncomputable def row12324 : BstLean.Part259.RowInputs 12324 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12324
    master12324 BstLean.Part262.actualCertificate12324
    BstLean.Part264b.N12324.covarianceEvent12324
    (BstLean.Part263.cell BstLean.Part263.scalarRow12324.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12324)
    BstLean.Part264b.N12324.covarianceEvent12324_measurable BstLean.Part264b.N12324.covarianceEvent12324_payment
    BstLean.Part264b.N12324.frame12324 (fun t c hw hc => ⟨root12324 t c hw hc⟩)
    BstLean.Part262.allocation12324 compatible12324

theorem energy12325 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part263.scalarRow12325.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part263.scalarRow12325, BstLean.Part263.cell12325]

noncomputable def root12325 (t : ℝ) (c : Ret 12325)
    (hw : c ∈ BstLean.Part159.Hof
      (BstLean.Part260.worldPackage 12325 (by constructor <;> norm_num)).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase 12325) :
    BstLean.Part243.RootInputs 12325 t c BstLean.Part259.agent12325.root :=
  root_from_sources (by constructor <;> norm_num) BstLean.Part263.scalarRow12325
    BstLean.Part264b.N12325.sourceNumerics12325
    (by norm_num [BstLean.Part263.scalarRow12325])
    (by norm_num [BstLean.Part263.scalarRow12325])
    (by norm_num [BstLean.Part263.scalarRow12325])
    energy12325 BstLean.Part262.actualCertificate12325 t c hw hc

noncomputable def master12325 :
    MasterCertificate 12325 (BstLean.Part260.worldParameters 12325) BstLean.Part259.agent12325 := by
  rw [BstLean.Part260.parameters12325]
  exact BstLean.Part261.master12325

theorem compatible12325 : BstLean.Part259.agent12325.charge ≤ master12325.retainedCharge := by
  change BstLean.Part259.agent12325.charge ≤ BstLean.Part261.master12325.retainedCharge
  rw [show BstLean.Part261.master12325.retainedCharge =
    BstLean.Part259.scalar12325.retainedCharge from
      congrArg (fun C => C.retainedCharge) BstLean.Part261.preserves12325]
  norm_num [BstLean.Part259.agent12325, BstLean.Part259.scalar12325]

noncomputable def row12325 : BstLean.Part259.RowInputs 12325 :=
  row_from_supplies (by constructor <;> norm_num) BstLean.Part259.agent12325
    master12325 BstLean.Part262.actualCertificate12325
    BstLean.Part264b.N12325.covarianceEvent12325
    (BstLean.Part263.cell BstLean.Part263.scalarRow12325.grid)
    (BstLean.Part264.caps BstLean.Part264.repair12325)
    BstLean.Part264b.N12325.covarianceEvent12325_measurable BstLean.Part264b.N12325.covarianceEvent12325_payment
    BstLean.Part264b.N12325.frame12325 (fun t c hw hc => ⟨root12325 t c hw hc⟩)
    BstLean.Part262.allocation12325 compatible12325

end BstLean.Part267
