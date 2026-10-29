import BstLean.Part286Bridge
import BstLean.Part269Frames34
import BstLean.Part268Master34
import BstLean.Part266Exports34

/-! Part 287: the rows 13200–13224 (Part269 shard 34) and the stated program on them.
Generated from Part286 records by reports/p287-lower34-generate.py. -/

namespace BstLean.Part287.Lower34
open BstLean.Part286 (localRoot_from_numerics stated_from_row)

open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part192

theorem energy13200 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13200.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13200, BstLean.Part268.cell13200]

theorem compatible13200 :
    BstLean.Part268.agent13200.charge ≤ BstLean.Part268.master13200.retainedCharge := by
  rw [show BstLean.Part268.master13200.retainedCharge = BstLean.Part268.scalar13200.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13200]
  norm_num [BstLean.Part268.agent13200, BstLean.Part268.scalar13200]

noncomputable def row13200 : BstLean.Part259.RowInputs 13200 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13200.worldPackage
    BstLean.Part268.agent13200 BstLean.Part268.master13200 BstLean.Part266.actualCertificate13200
    BstLean.Part269.N13200.frameData13200.covarianceEvent BstLean.Part269.N13200.frameData13200.cell BstLean.Part269.N13200.frameData13200.caps
    BstLean.Part269.N13200.frameData13200.covariance_measurable BstLean.Part269.N13200.frameData13200.covariance_payment BstLean.Part269.N13200.frameData13200.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13200.worldPackage rfl
      BstLean.Part268.WorldRow13200.product_lower (BstLean.Part268.WorldRow13200.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13200 (fun i hi => BstLean.Part269.N13200.sourceNumerics13200 hi)
      (by norm_num [BstLean.Part269.scalarRow13200]) (by norm_num [BstLean.Part269.scalarRow13200]) (by norm_num [BstLean.Part269.scalarRow13200]) energy13200)
    (by norm_num [BstLean.Part268.agent13200]) compatible13200

theorem energy13201 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13201.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13201, BstLean.Part268.cell13201]

theorem compatible13201 :
    BstLean.Part268.agent13201.charge ≤ BstLean.Part268.master13201.retainedCharge := by
  rw [show BstLean.Part268.master13201.retainedCharge = BstLean.Part268.scalar13201.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13201]
  norm_num [BstLean.Part268.agent13201, BstLean.Part268.scalar13201]

noncomputable def row13201 : BstLean.Part259.RowInputs 13201 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13201.worldPackage
    BstLean.Part268.agent13201 BstLean.Part268.master13201 BstLean.Part266.actualCertificate13201
    BstLean.Part269.N13201.frameData13201.covarianceEvent BstLean.Part269.N13201.frameData13201.cell BstLean.Part269.N13201.frameData13201.caps
    BstLean.Part269.N13201.frameData13201.covariance_measurable BstLean.Part269.N13201.frameData13201.covariance_payment BstLean.Part269.N13201.frameData13201.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13201.worldPackage rfl
      BstLean.Part268.WorldRow13201.product_lower (BstLean.Part268.WorldRow13201.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13201 (fun i hi => BstLean.Part269.N13201.sourceNumerics13201 hi)
      (by norm_num [BstLean.Part269.scalarRow13201]) (by norm_num [BstLean.Part269.scalarRow13201]) (by norm_num [BstLean.Part269.scalarRow13201]) energy13201)
    (by norm_num [BstLean.Part268.agent13201]) compatible13201

theorem energy13202 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13202.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13202, BstLean.Part268.cell13202]

theorem compatible13202 :
    BstLean.Part268.agent13202.charge ≤ BstLean.Part268.master13202.retainedCharge := by
  rw [show BstLean.Part268.master13202.retainedCharge = BstLean.Part268.scalar13202.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13202]
  norm_num [BstLean.Part268.agent13202, BstLean.Part268.scalar13202]

noncomputable def row13202 : BstLean.Part259.RowInputs 13202 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13202.worldPackage
    BstLean.Part268.agent13202 BstLean.Part268.master13202 BstLean.Part266.actualCertificate13202
    BstLean.Part269.N13202.frameData13202.covarianceEvent BstLean.Part269.N13202.frameData13202.cell BstLean.Part269.N13202.frameData13202.caps
    BstLean.Part269.N13202.frameData13202.covariance_measurable BstLean.Part269.N13202.frameData13202.covariance_payment BstLean.Part269.N13202.frameData13202.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13202.worldPackage rfl
      BstLean.Part268.WorldRow13202.product_lower (BstLean.Part268.WorldRow13202.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13202 (fun i hi => BstLean.Part269.N13202.sourceNumerics13202 hi)
      (by norm_num [BstLean.Part269.scalarRow13202]) (by norm_num [BstLean.Part269.scalarRow13202]) (by norm_num [BstLean.Part269.scalarRow13202]) energy13202)
    (by norm_num [BstLean.Part268.agent13202]) compatible13202

theorem energy13203 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13203.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13203, BstLean.Part268.cell13203]

theorem compatible13203 :
    BstLean.Part268.agent13203.charge ≤ BstLean.Part268.master13203.retainedCharge := by
  rw [show BstLean.Part268.master13203.retainedCharge = BstLean.Part268.scalar13203.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13203]
  norm_num [BstLean.Part268.agent13203, BstLean.Part268.scalar13203]

noncomputable def row13203 : BstLean.Part259.RowInputs 13203 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13203.worldPackage
    BstLean.Part268.agent13203 BstLean.Part268.master13203 BstLean.Part266.actualCertificate13203
    BstLean.Part269.N13203.frameData13203.covarianceEvent BstLean.Part269.N13203.frameData13203.cell BstLean.Part269.N13203.frameData13203.caps
    BstLean.Part269.N13203.frameData13203.covariance_measurable BstLean.Part269.N13203.frameData13203.covariance_payment BstLean.Part269.N13203.frameData13203.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13203.worldPackage rfl
      BstLean.Part268.WorldRow13203.product_lower (BstLean.Part268.WorldRow13203.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13203 (fun i hi => BstLean.Part269.N13203.sourceNumerics13203 hi)
      (by norm_num [BstLean.Part269.scalarRow13203]) (by norm_num [BstLean.Part269.scalarRow13203]) (by norm_num [BstLean.Part269.scalarRow13203]) energy13203)
    (by norm_num [BstLean.Part268.agent13203]) compatible13203

theorem energy13204 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13204.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13204, BstLean.Part268.cell13204]

theorem compatible13204 :
    BstLean.Part268.agent13204.charge ≤ BstLean.Part268.master13204.retainedCharge := by
  rw [show BstLean.Part268.master13204.retainedCharge = BstLean.Part268.scalar13204.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13204]
  norm_num [BstLean.Part268.agent13204, BstLean.Part268.scalar13204]

noncomputable def row13204 : BstLean.Part259.RowInputs 13204 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13204.worldPackage
    BstLean.Part268.agent13204 BstLean.Part268.master13204 BstLean.Part266.actualCertificate13204
    BstLean.Part269.N13204.frameData13204.covarianceEvent BstLean.Part269.N13204.frameData13204.cell BstLean.Part269.N13204.frameData13204.caps
    BstLean.Part269.N13204.frameData13204.covariance_measurable BstLean.Part269.N13204.frameData13204.covariance_payment BstLean.Part269.N13204.frameData13204.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13204.worldPackage rfl
      BstLean.Part268.WorldRow13204.product_lower (BstLean.Part268.WorldRow13204.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13204 (fun i hi => BstLean.Part269.N13204.sourceNumerics13204 hi)
      (by norm_num [BstLean.Part269.scalarRow13204]) (by norm_num [BstLean.Part269.scalarRow13204]) (by norm_num [BstLean.Part269.scalarRow13204]) energy13204)
    (by norm_num [BstLean.Part268.agent13204]) compatible13204

theorem energy13205 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13205.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13205, BstLean.Part268.cell13205]

theorem compatible13205 :
    BstLean.Part268.agent13205.charge ≤ BstLean.Part268.master13205.retainedCharge := by
  rw [show BstLean.Part268.master13205.retainedCharge = BstLean.Part268.scalar13205.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13205]
  norm_num [BstLean.Part268.agent13205, BstLean.Part268.scalar13205]

noncomputable def row13205 : BstLean.Part259.RowInputs 13205 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13205.worldPackage
    BstLean.Part268.agent13205 BstLean.Part268.master13205 BstLean.Part266.actualCertificate13205
    BstLean.Part269.N13205.frameData13205.covarianceEvent BstLean.Part269.N13205.frameData13205.cell BstLean.Part269.N13205.frameData13205.caps
    BstLean.Part269.N13205.frameData13205.covariance_measurable BstLean.Part269.N13205.frameData13205.covariance_payment BstLean.Part269.N13205.frameData13205.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13205.worldPackage rfl
      BstLean.Part268.WorldRow13205.product_lower (BstLean.Part268.WorldRow13205.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13205 (fun i hi => BstLean.Part269.N13205.sourceNumerics13205 hi)
      (by norm_num [BstLean.Part269.scalarRow13205]) (by norm_num [BstLean.Part269.scalarRow13205]) (by norm_num [BstLean.Part269.scalarRow13205]) energy13205)
    (by norm_num [BstLean.Part268.agent13205]) compatible13205

theorem energy13206 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13206.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13206, BstLean.Part268.cell13206]

theorem compatible13206 :
    BstLean.Part268.agent13206.charge ≤ BstLean.Part268.master13206.retainedCharge := by
  rw [show BstLean.Part268.master13206.retainedCharge = BstLean.Part268.scalar13206.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13206]
  norm_num [BstLean.Part268.agent13206, BstLean.Part268.scalar13206]

noncomputable def row13206 : BstLean.Part259.RowInputs 13206 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13206.worldPackage
    BstLean.Part268.agent13206 BstLean.Part268.master13206 BstLean.Part266.actualCertificate13206
    BstLean.Part269.N13206.frameData13206.covarianceEvent BstLean.Part269.N13206.frameData13206.cell BstLean.Part269.N13206.frameData13206.caps
    BstLean.Part269.N13206.frameData13206.covariance_measurable BstLean.Part269.N13206.frameData13206.covariance_payment BstLean.Part269.N13206.frameData13206.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13206.worldPackage rfl
      BstLean.Part268.WorldRow13206.product_lower (BstLean.Part268.WorldRow13206.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13206 (fun i hi => BstLean.Part269.N13206.sourceNumerics13206 hi)
      (by norm_num [BstLean.Part269.scalarRow13206]) (by norm_num [BstLean.Part269.scalarRow13206]) (by norm_num [BstLean.Part269.scalarRow13206]) energy13206)
    (by norm_num [BstLean.Part268.agent13206]) compatible13206

theorem energy13207 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13207.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13207, BstLean.Part268.cell13207]

theorem compatible13207 :
    BstLean.Part268.agent13207.charge ≤ BstLean.Part268.master13207.retainedCharge := by
  rw [show BstLean.Part268.master13207.retainedCharge = BstLean.Part268.scalar13207.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13207]
  norm_num [BstLean.Part268.agent13207, BstLean.Part268.scalar13207]

noncomputable def row13207 : BstLean.Part259.RowInputs 13207 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13207.worldPackage
    BstLean.Part268.agent13207 BstLean.Part268.master13207 BstLean.Part266.actualCertificate13207
    BstLean.Part269.N13207.frameData13207.covarianceEvent BstLean.Part269.N13207.frameData13207.cell BstLean.Part269.N13207.frameData13207.caps
    BstLean.Part269.N13207.frameData13207.covariance_measurable BstLean.Part269.N13207.frameData13207.covariance_payment BstLean.Part269.N13207.frameData13207.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13207.worldPackage rfl
      BstLean.Part268.WorldRow13207.product_lower (BstLean.Part268.WorldRow13207.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13207 (fun i hi => BstLean.Part269.N13207.sourceNumerics13207 hi)
      (by norm_num [BstLean.Part269.scalarRow13207]) (by norm_num [BstLean.Part269.scalarRow13207]) (by norm_num [BstLean.Part269.scalarRow13207]) energy13207)
    (by norm_num [BstLean.Part268.agent13207]) compatible13207

theorem energy13208 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13208.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13208, BstLean.Part268.cell13208]

theorem compatible13208 :
    BstLean.Part268.agent13208.charge ≤ BstLean.Part268.master13208.retainedCharge := by
  rw [show BstLean.Part268.master13208.retainedCharge = BstLean.Part268.scalar13208.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13208]
  norm_num [BstLean.Part268.agent13208, BstLean.Part268.scalar13208]

noncomputable def row13208 : BstLean.Part259.RowInputs 13208 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13208.worldPackage
    BstLean.Part268.agent13208 BstLean.Part268.master13208 BstLean.Part266.actualCertificate13208
    BstLean.Part269.N13208.frameData13208.covarianceEvent BstLean.Part269.N13208.frameData13208.cell BstLean.Part269.N13208.frameData13208.caps
    BstLean.Part269.N13208.frameData13208.covariance_measurable BstLean.Part269.N13208.frameData13208.covariance_payment BstLean.Part269.N13208.frameData13208.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13208.worldPackage rfl
      BstLean.Part268.WorldRow13208.product_lower (BstLean.Part268.WorldRow13208.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13208 (fun i hi => BstLean.Part269.N13208.sourceNumerics13208 hi)
      (by norm_num [BstLean.Part269.scalarRow13208]) (by norm_num [BstLean.Part269.scalarRow13208]) (by norm_num [BstLean.Part269.scalarRow13208]) energy13208)
    (by norm_num [BstLean.Part268.agent13208]) compatible13208

theorem energy13209 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13209.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13209, BstLean.Part268.cell13209]

theorem compatible13209 :
    BstLean.Part268.agent13209.charge ≤ BstLean.Part268.master13209.retainedCharge := by
  rw [show BstLean.Part268.master13209.retainedCharge = BstLean.Part268.scalar13209.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13209]
  norm_num [BstLean.Part268.agent13209, BstLean.Part268.scalar13209]

noncomputable def row13209 : BstLean.Part259.RowInputs 13209 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13209.worldPackage
    BstLean.Part268.agent13209 BstLean.Part268.master13209 BstLean.Part266.actualCertificate13209
    BstLean.Part269.N13209.frameData13209.covarianceEvent BstLean.Part269.N13209.frameData13209.cell BstLean.Part269.N13209.frameData13209.caps
    BstLean.Part269.N13209.frameData13209.covariance_measurable BstLean.Part269.N13209.frameData13209.covariance_payment BstLean.Part269.N13209.frameData13209.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13209.worldPackage rfl
      BstLean.Part268.WorldRow13209.product_lower (BstLean.Part268.WorldRow13209.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13209 (fun i hi => BstLean.Part269.N13209.sourceNumerics13209 hi)
      (by norm_num [BstLean.Part269.scalarRow13209]) (by norm_num [BstLean.Part269.scalarRow13209]) (by norm_num [BstLean.Part269.scalarRow13209]) energy13209)
    (by norm_num [BstLean.Part268.agent13209]) compatible13209

theorem energy13210 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13210.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13210, BstLean.Part268.cell13210]

theorem compatible13210 :
    BstLean.Part268.agent13210.charge ≤ BstLean.Part268.master13210.retainedCharge := by
  rw [show BstLean.Part268.master13210.retainedCharge = BstLean.Part268.scalar13210.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13210]
  norm_num [BstLean.Part268.agent13210, BstLean.Part268.scalar13210]

noncomputable def row13210 : BstLean.Part259.RowInputs 13210 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13210.worldPackage
    BstLean.Part268.agent13210 BstLean.Part268.master13210 BstLean.Part266.actualCertificate13210
    BstLean.Part269.N13210.frameData13210.covarianceEvent BstLean.Part269.N13210.frameData13210.cell BstLean.Part269.N13210.frameData13210.caps
    BstLean.Part269.N13210.frameData13210.covariance_measurable BstLean.Part269.N13210.frameData13210.covariance_payment BstLean.Part269.N13210.frameData13210.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13210.worldPackage rfl
      BstLean.Part268.WorldRow13210.product_lower (BstLean.Part268.WorldRow13210.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13210 (fun i hi => BstLean.Part269.N13210.sourceNumerics13210 hi)
      (by norm_num [BstLean.Part269.scalarRow13210]) (by norm_num [BstLean.Part269.scalarRow13210]) (by norm_num [BstLean.Part269.scalarRow13210]) energy13210)
    (by norm_num [BstLean.Part268.agent13210]) compatible13210

theorem energy13211 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13211.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13211, BstLean.Part268.cell13211]

theorem compatible13211 :
    BstLean.Part268.agent13211.charge ≤ BstLean.Part268.master13211.retainedCharge := by
  rw [show BstLean.Part268.master13211.retainedCharge = BstLean.Part268.scalar13211.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13211]
  norm_num [BstLean.Part268.agent13211, BstLean.Part268.scalar13211]

noncomputable def row13211 : BstLean.Part259.RowInputs 13211 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13211.worldPackage
    BstLean.Part268.agent13211 BstLean.Part268.master13211 BstLean.Part266.actualCertificate13211
    BstLean.Part269.N13211.frameData13211.covarianceEvent BstLean.Part269.N13211.frameData13211.cell BstLean.Part269.N13211.frameData13211.caps
    BstLean.Part269.N13211.frameData13211.covariance_measurable BstLean.Part269.N13211.frameData13211.covariance_payment BstLean.Part269.N13211.frameData13211.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13211.worldPackage rfl
      BstLean.Part268.WorldRow13211.product_lower (BstLean.Part268.WorldRow13211.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13211 (fun i hi => BstLean.Part269.N13211.sourceNumerics13211 hi)
      (by norm_num [BstLean.Part269.scalarRow13211]) (by norm_num [BstLean.Part269.scalarRow13211]) (by norm_num [BstLean.Part269.scalarRow13211]) energy13211)
    (by norm_num [BstLean.Part268.agent13211]) compatible13211

theorem energy13212 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13212.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13212, BstLean.Part268.cell13212]

theorem compatible13212 :
    BstLean.Part268.agent13212.charge ≤ BstLean.Part268.master13212.retainedCharge := by
  rw [show BstLean.Part268.master13212.retainedCharge = BstLean.Part268.scalar13212.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13212]
  norm_num [BstLean.Part268.agent13212, BstLean.Part268.scalar13212]

noncomputable def row13212 : BstLean.Part259.RowInputs 13212 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13212.worldPackage
    BstLean.Part268.agent13212 BstLean.Part268.master13212 BstLean.Part266.actualCertificate13212
    BstLean.Part269.N13212.frameData13212.covarianceEvent BstLean.Part269.N13212.frameData13212.cell BstLean.Part269.N13212.frameData13212.caps
    BstLean.Part269.N13212.frameData13212.covariance_measurable BstLean.Part269.N13212.frameData13212.covariance_payment BstLean.Part269.N13212.frameData13212.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13212.worldPackage rfl
      BstLean.Part268.WorldRow13212.product_lower (BstLean.Part268.WorldRow13212.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13212 (fun i hi => BstLean.Part269.N13212.sourceNumerics13212 hi)
      (by norm_num [BstLean.Part269.scalarRow13212]) (by norm_num [BstLean.Part269.scalarRow13212]) (by norm_num [BstLean.Part269.scalarRow13212]) energy13212)
    (by norm_num [BstLean.Part268.agent13212]) compatible13212

theorem energy13213 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13213.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13213, BstLean.Part268.cell13213]

theorem compatible13213 :
    BstLean.Part268.agent13213.charge ≤ BstLean.Part268.master13213.retainedCharge := by
  rw [show BstLean.Part268.master13213.retainedCharge = BstLean.Part268.scalar13213.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13213]
  norm_num [BstLean.Part268.agent13213, BstLean.Part268.scalar13213]

noncomputable def row13213 : BstLean.Part259.RowInputs 13213 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13213.worldPackage
    BstLean.Part268.agent13213 BstLean.Part268.master13213 BstLean.Part266.actualCertificate13213
    BstLean.Part269.N13213.frameData13213.covarianceEvent BstLean.Part269.N13213.frameData13213.cell BstLean.Part269.N13213.frameData13213.caps
    BstLean.Part269.N13213.frameData13213.covariance_measurable BstLean.Part269.N13213.frameData13213.covariance_payment BstLean.Part269.N13213.frameData13213.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13213.worldPackage rfl
      BstLean.Part268.WorldRow13213.product_lower (BstLean.Part268.WorldRow13213.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13213 (fun i hi => BstLean.Part269.N13213.sourceNumerics13213 hi)
      (by norm_num [BstLean.Part269.scalarRow13213]) (by norm_num [BstLean.Part269.scalarRow13213]) (by norm_num [BstLean.Part269.scalarRow13213]) energy13213)
    (by norm_num [BstLean.Part268.agent13213]) compatible13213

theorem energy13214 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13214.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13214, BstLean.Part268.cell13214]

theorem compatible13214 :
    BstLean.Part268.agent13214.charge ≤ BstLean.Part268.master13214.retainedCharge := by
  rw [show BstLean.Part268.master13214.retainedCharge = BstLean.Part268.scalar13214.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13214]
  norm_num [BstLean.Part268.agent13214, BstLean.Part268.scalar13214]

noncomputable def row13214 : BstLean.Part259.RowInputs 13214 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13214.worldPackage
    BstLean.Part268.agent13214 BstLean.Part268.master13214 BstLean.Part266.actualCertificate13214
    BstLean.Part269.N13214.frameData13214.covarianceEvent BstLean.Part269.N13214.frameData13214.cell BstLean.Part269.N13214.frameData13214.caps
    BstLean.Part269.N13214.frameData13214.covariance_measurable BstLean.Part269.N13214.frameData13214.covariance_payment BstLean.Part269.N13214.frameData13214.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13214.worldPackage rfl
      BstLean.Part268.WorldRow13214.product_lower (BstLean.Part268.WorldRow13214.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13214 (fun i hi => BstLean.Part269.N13214.sourceNumerics13214 hi)
      (by norm_num [BstLean.Part269.scalarRow13214]) (by norm_num [BstLean.Part269.scalarRow13214]) (by norm_num [BstLean.Part269.scalarRow13214]) energy13214)
    (by norm_num [BstLean.Part268.agent13214]) compatible13214

theorem energy13215 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13215.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13215, BstLean.Part268.cell13215]

theorem compatible13215 :
    BstLean.Part268.agent13215.charge ≤ BstLean.Part268.master13215.retainedCharge := by
  rw [show BstLean.Part268.master13215.retainedCharge = BstLean.Part268.scalar13215.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13215]
  norm_num [BstLean.Part268.agent13215, BstLean.Part268.scalar13215]

noncomputable def row13215 : BstLean.Part259.RowInputs 13215 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13215.worldPackage
    BstLean.Part268.agent13215 BstLean.Part268.master13215 BstLean.Part266.actualCertificate13215
    BstLean.Part269.N13215.frameData13215.covarianceEvent BstLean.Part269.N13215.frameData13215.cell BstLean.Part269.N13215.frameData13215.caps
    BstLean.Part269.N13215.frameData13215.covariance_measurable BstLean.Part269.N13215.frameData13215.covariance_payment BstLean.Part269.N13215.frameData13215.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13215.worldPackage rfl
      BstLean.Part268.WorldRow13215.product_lower (BstLean.Part268.WorldRow13215.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13215 (fun i hi => BstLean.Part269.N13215.sourceNumerics13215 hi)
      (by norm_num [BstLean.Part269.scalarRow13215]) (by norm_num [BstLean.Part269.scalarRow13215]) (by norm_num [BstLean.Part269.scalarRow13215]) energy13215)
    (by norm_num [BstLean.Part268.agent13215]) compatible13215

theorem energy13216 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13216.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13216, BstLean.Part268.cell13216]

theorem compatible13216 :
    BstLean.Part268.agent13216.charge ≤ BstLean.Part268.master13216.retainedCharge := by
  rw [show BstLean.Part268.master13216.retainedCharge = BstLean.Part268.scalar13216.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13216]
  norm_num [BstLean.Part268.agent13216, BstLean.Part268.scalar13216]

noncomputable def row13216 : BstLean.Part259.RowInputs 13216 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13216.worldPackage
    BstLean.Part268.agent13216 BstLean.Part268.master13216 BstLean.Part266.actualCertificate13216
    BstLean.Part269.N13216.frameData13216.covarianceEvent BstLean.Part269.N13216.frameData13216.cell BstLean.Part269.N13216.frameData13216.caps
    BstLean.Part269.N13216.frameData13216.covariance_measurable BstLean.Part269.N13216.frameData13216.covariance_payment BstLean.Part269.N13216.frameData13216.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13216.worldPackage rfl
      BstLean.Part268.WorldRow13216.product_lower (BstLean.Part268.WorldRow13216.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13216 (fun i hi => BstLean.Part269.N13216.sourceNumerics13216 hi)
      (by norm_num [BstLean.Part269.scalarRow13216]) (by norm_num [BstLean.Part269.scalarRow13216]) (by norm_num [BstLean.Part269.scalarRow13216]) energy13216)
    (by norm_num [BstLean.Part268.agent13216]) compatible13216

theorem energy13217 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13217.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13217, BstLean.Part268.cell13217]

theorem compatible13217 :
    BstLean.Part268.agent13217.charge ≤ BstLean.Part268.master13217.retainedCharge := by
  rw [show BstLean.Part268.master13217.retainedCharge = BstLean.Part268.scalar13217.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13217]
  norm_num [BstLean.Part268.agent13217, BstLean.Part268.scalar13217]

noncomputable def row13217 : BstLean.Part259.RowInputs 13217 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13217.worldPackage
    BstLean.Part268.agent13217 BstLean.Part268.master13217 BstLean.Part266.actualCertificate13217
    BstLean.Part269.N13217.frameData13217.covarianceEvent BstLean.Part269.N13217.frameData13217.cell BstLean.Part269.N13217.frameData13217.caps
    BstLean.Part269.N13217.frameData13217.covariance_measurable BstLean.Part269.N13217.frameData13217.covariance_payment BstLean.Part269.N13217.frameData13217.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13217.worldPackage rfl
      BstLean.Part268.WorldRow13217.product_lower (BstLean.Part268.WorldRow13217.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13217 (fun i hi => BstLean.Part269.N13217.sourceNumerics13217 hi)
      (by norm_num [BstLean.Part269.scalarRow13217]) (by norm_num [BstLean.Part269.scalarRow13217]) (by norm_num [BstLean.Part269.scalarRow13217]) energy13217)
    (by norm_num [BstLean.Part268.agent13217]) compatible13217

theorem energy13218 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13218.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13218, BstLean.Part268.cell13218]

theorem compatible13218 :
    BstLean.Part268.agent13218.charge ≤ BstLean.Part268.master13218.retainedCharge := by
  rw [show BstLean.Part268.master13218.retainedCharge = BstLean.Part268.scalar13218.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13218]
  norm_num [BstLean.Part268.agent13218, BstLean.Part268.scalar13218]

noncomputable def row13218 : BstLean.Part259.RowInputs 13218 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13218.worldPackage
    BstLean.Part268.agent13218 BstLean.Part268.master13218 BstLean.Part266.actualCertificate13218
    BstLean.Part269.N13218.frameData13218.covarianceEvent BstLean.Part269.N13218.frameData13218.cell BstLean.Part269.N13218.frameData13218.caps
    BstLean.Part269.N13218.frameData13218.covariance_measurable BstLean.Part269.N13218.frameData13218.covariance_payment BstLean.Part269.N13218.frameData13218.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13218.worldPackage rfl
      BstLean.Part268.WorldRow13218.product_lower (BstLean.Part268.WorldRow13218.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13218 (fun i hi => BstLean.Part269.N13218.sourceNumerics13218 hi)
      (by norm_num [BstLean.Part269.scalarRow13218]) (by norm_num [BstLean.Part269.scalarRow13218]) (by norm_num [BstLean.Part269.scalarRow13218]) energy13218)
    (by norm_num [BstLean.Part268.agent13218]) compatible13218

theorem energy13219 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13219.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13219, BstLean.Part268.cell13219]

theorem compatible13219 :
    BstLean.Part268.agent13219.charge ≤ BstLean.Part268.master13219.retainedCharge := by
  rw [show BstLean.Part268.master13219.retainedCharge = BstLean.Part268.scalar13219.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13219]
  norm_num [BstLean.Part268.agent13219, BstLean.Part268.scalar13219]

noncomputable def row13219 : BstLean.Part259.RowInputs 13219 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13219.worldPackage
    BstLean.Part268.agent13219 BstLean.Part268.master13219 BstLean.Part266.actualCertificate13219
    BstLean.Part269.N13219.frameData13219.covarianceEvent BstLean.Part269.N13219.frameData13219.cell BstLean.Part269.N13219.frameData13219.caps
    BstLean.Part269.N13219.frameData13219.covariance_measurable BstLean.Part269.N13219.frameData13219.covariance_payment BstLean.Part269.N13219.frameData13219.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13219.worldPackage rfl
      BstLean.Part268.WorldRow13219.product_lower (BstLean.Part268.WorldRow13219.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13219 (fun i hi => BstLean.Part269.N13219.sourceNumerics13219 hi)
      (by norm_num [BstLean.Part269.scalarRow13219]) (by norm_num [BstLean.Part269.scalarRow13219]) (by norm_num [BstLean.Part269.scalarRow13219]) energy13219)
    (by norm_num [BstLean.Part268.agent13219]) compatible13219

theorem energy13220 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13220.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13220, BstLean.Part268.cell13220]

theorem compatible13220 :
    BstLean.Part268.agent13220.charge ≤ BstLean.Part268.master13220.retainedCharge := by
  rw [show BstLean.Part268.master13220.retainedCharge = BstLean.Part268.scalar13220.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13220]
  norm_num [BstLean.Part268.agent13220, BstLean.Part268.scalar13220]

noncomputable def row13220 : BstLean.Part259.RowInputs 13220 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13220.worldPackage
    BstLean.Part268.agent13220 BstLean.Part268.master13220 BstLean.Part266.actualCertificate13220
    BstLean.Part269.N13220.frameData13220.covarianceEvent BstLean.Part269.N13220.frameData13220.cell BstLean.Part269.N13220.frameData13220.caps
    BstLean.Part269.N13220.frameData13220.covariance_measurable BstLean.Part269.N13220.frameData13220.covariance_payment BstLean.Part269.N13220.frameData13220.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13220.worldPackage rfl
      BstLean.Part268.WorldRow13220.product_lower (BstLean.Part268.WorldRow13220.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13220 (fun i hi => BstLean.Part269.N13220.sourceNumerics13220 hi)
      (by norm_num [BstLean.Part269.scalarRow13220]) (by norm_num [BstLean.Part269.scalarRow13220]) (by norm_num [BstLean.Part269.scalarRow13220]) energy13220)
    (by norm_num [BstLean.Part268.agent13220]) compatible13220

theorem energy13221 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13221.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13221, BstLean.Part268.cell13221]

theorem compatible13221 :
    BstLean.Part268.agent13221.charge ≤ BstLean.Part268.master13221.retainedCharge := by
  rw [show BstLean.Part268.master13221.retainedCharge = BstLean.Part268.scalar13221.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13221]
  norm_num [BstLean.Part268.agent13221, BstLean.Part268.scalar13221]

noncomputable def row13221 : BstLean.Part259.RowInputs 13221 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13221.worldPackage
    BstLean.Part268.agent13221 BstLean.Part268.master13221 BstLean.Part266.actualCertificate13221
    BstLean.Part269.N13221.frameData13221.covarianceEvent BstLean.Part269.N13221.frameData13221.cell BstLean.Part269.N13221.frameData13221.caps
    BstLean.Part269.N13221.frameData13221.covariance_measurable BstLean.Part269.N13221.frameData13221.covariance_payment BstLean.Part269.N13221.frameData13221.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13221.worldPackage rfl
      BstLean.Part268.WorldRow13221.product_lower (BstLean.Part268.WorldRow13221.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13221 (fun i hi => BstLean.Part269.N13221.sourceNumerics13221 hi)
      (by norm_num [BstLean.Part269.scalarRow13221]) (by norm_num [BstLean.Part269.scalarRow13221]) (by norm_num [BstLean.Part269.scalarRow13221]) energy13221)
    (by norm_num [BstLean.Part268.agent13221]) compatible13221

theorem energy13222 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13222.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13222, BstLean.Part268.cell13222]

theorem compatible13222 :
    BstLean.Part268.agent13222.charge ≤ BstLean.Part268.master13222.retainedCharge := by
  rw [show BstLean.Part268.master13222.retainedCharge = BstLean.Part268.scalar13222.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13222]
  norm_num [BstLean.Part268.agent13222, BstLean.Part268.scalar13222]

noncomputable def row13222 : BstLean.Part259.RowInputs 13222 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13222.worldPackage
    BstLean.Part268.agent13222 BstLean.Part268.master13222 BstLean.Part266.actualCertificate13222
    BstLean.Part269.N13222.frameData13222.covarianceEvent BstLean.Part269.N13222.frameData13222.cell BstLean.Part269.N13222.frameData13222.caps
    BstLean.Part269.N13222.frameData13222.covariance_measurable BstLean.Part269.N13222.frameData13222.covariance_payment BstLean.Part269.N13222.frameData13222.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13222.worldPackage rfl
      BstLean.Part268.WorldRow13222.product_lower (BstLean.Part268.WorldRow13222.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13222 (fun i hi => BstLean.Part269.N13222.sourceNumerics13222 hi)
      (by norm_num [BstLean.Part269.scalarRow13222]) (by norm_num [BstLean.Part269.scalarRow13222]) (by norm_num [BstLean.Part269.scalarRow13222]) energy13222)
    (by norm_num [BstLean.Part268.agent13222]) compatible13222

theorem energy13223 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13223.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13223, BstLean.Part268.cell13223]

theorem compatible13223 :
    BstLean.Part268.agent13223.charge ≤ BstLean.Part268.master13223.retainedCharge := by
  rw [show BstLean.Part268.master13223.retainedCharge = BstLean.Part268.scalar13223.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13223]
  norm_num [BstLean.Part268.agent13223, BstLean.Part268.scalar13223]

noncomputable def row13223 : BstLean.Part259.RowInputs 13223 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13223.worldPackage
    BstLean.Part268.agent13223 BstLean.Part268.master13223 BstLean.Part266.actualCertificate13223
    BstLean.Part269.N13223.frameData13223.covarianceEvent BstLean.Part269.N13223.frameData13223.cell BstLean.Part269.N13223.frameData13223.caps
    BstLean.Part269.N13223.frameData13223.covariance_measurable BstLean.Part269.N13223.frameData13223.covariance_payment BstLean.Part269.N13223.frameData13223.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13223.worldPackage rfl
      BstLean.Part268.WorldRow13223.product_lower (BstLean.Part268.WorldRow13223.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13223 (fun i hi => BstLean.Part269.N13223.sourceNumerics13223 hi)
      (by norm_num [BstLean.Part269.scalarRow13223]) (by norm_num [BstLean.Part269.scalarRow13223]) (by norm_num [BstLean.Part269.scalarRow13223]) energy13223)
    (by norm_num [BstLean.Part268.agent13223]) compatible13223

theorem energy13224 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (BstLean.Part269.scalarRow13224.table i).energy ≤ (702/1000 : ℝ) := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [BstLean.Part269.scalarRow13224, BstLean.Part269.cell13224]

theorem compatible13224 :
    BstLean.Part268.agent13224.charge ≤ BstLean.Part268.master13224.retainedCharge := by
  rw [show BstLean.Part268.master13224.retainedCharge = BstLean.Part268.scalar13224.retainedCharge from
    congrArg (fun C => C.retainedCharge) BstLean.Part268.preserves13224]
  norm_num [BstLean.Part268.agent13224, BstLean.Part268.scalar13224]

noncomputable def row13224 : BstLean.Part259.RowInputs 13224 :=
  BstLean.Part270.row_from_supplies BstLean.Part268.WorldRow13224.worldPackage
    BstLean.Part268.agent13224 BstLean.Part268.master13224 BstLean.Part266.actualCertificate13224
    BstLean.Part269.N13224.frameData13224.covarianceEvent BstLean.Part269.N13224.frameData13224.cell BstLean.Part269.N13224.frameData13224.caps
    BstLean.Part269.N13224.frameData13224.covariance_measurable BstLean.Part269.N13224.frameData13224.covariance_payment BstLean.Part269.N13224.frameData13224.frame
    (localRoot_from_numerics (by norm_num) (by norm_num) BstLean.Part268.WorldRow13224.worldPackage rfl
      BstLean.Part268.WorldRow13224.product_lower (BstLean.Part268.WorldRow13224.producthi.2.trans (by norm_num))
      BstLean.Part269.scalarRow13224 (fun i hi => BstLean.Part269.N13224.sourceNumerics13224 hi)
      (by norm_num [BstLean.Part269.scalarRow13224]) (by norm_num [BstLean.Part269.scalarRow13224]) (by norm_num [BstLean.Part269.scalarRow13224]) energy13224)
    (by norm_num [BstLean.Part268.agent13224]) compatible13224

/-- The stated program on 13200–13224, odd and even. -/
theorem stated_shard34 : ∀ n ∈ Set.Icc (13200 : ℕ) 13224, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  intro n hn t
  obtain ⟨hl, hu⟩ := hn
  interval_cases n
  · exact stated_from_row row13200 (by norm_num) rfl t
  · exact stated_from_row row13201 (by norm_num) rfl t
  · exact stated_from_row row13202 (by norm_num) rfl t
  · exact stated_from_row row13203 (by norm_num) rfl t
  · exact stated_from_row row13204 (by norm_num) rfl t
  · exact stated_from_row row13205 (by norm_num) rfl t
  · exact stated_from_row row13206 (by norm_num) rfl t
  · exact stated_from_row row13207 (by norm_num) rfl t
  · exact stated_from_row row13208 (by norm_num) rfl t
  · exact stated_from_row row13209 (by norm_num) rfl t
  · exact stated_from_row row13210 (by norm_num) rfl t
  · exact stated_from_row row13211 (by norm_num) rfl t
  · exact stated_from_row row13212 (by norm_num) rfl t
  · exact stated_from_row row13213 (by norm_num) rfl t
  · exact stated_from_row row13214 (by norm_num) rfl t
  · exact stated_from_row row13215 (by norm_num) rfl t
  · exact stated_from_row row13216 (by norm_num) rfl t
  · exact stated_from_row row13217 (by norm_num) rfl t
  · exact stated_from_row row13218 (by norm_num) rfl t
  · exact stated_from_row row13219 (by norm_num) rfl t
  · exact stated_from_row row13220 (by norm_num) rfl t
  · exact stated_from_row row13221 (by norm_num) rfl t
  · exact stated_from_row row13222 (by norm_num) rfl t
  · exact stated_from_row row13223 (by norm_num) rfl t
  · exact stated_from_row row13224 (by norm_num) rfl t

end BstLean.Part287.Lower34

/-- info: 'BstLean.Part287.Lower34.stated_shard34' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part287.Lower34.stated_shard34
