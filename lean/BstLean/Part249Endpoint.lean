import BstLean.Part243Row

/-! A scalar sensitivity certificate at 12225. The Agent frame allowance increases by
26e-6. These endpoint bounds do not supply the corresponding network frame. -/
namespace BstLean.Part249
open Real BstLean.Part156 BstLean.Part160 BstLean.Part243

noncomputable def optionBAgentFrame : ℝ := 146006785 / 10 ^ 8
noncomputable def optionBPositiveExponent : ℝ := 505921532 / 10 ^ 12
noncomputable def optionBNegativeExponent : ℝ := 495199992 / 10 ^ 12
noncomputable def optionBPositiveBase : ℝ := 461574715492 / 10 ^ 12
noncomputable def optionBNegativeBase : ℝ := 469199378042 / 10 ^ 12

theorem optionB_positive_enclosure :
    Eplus aL (rowRoot + dsL) rowRadius rowWorldFrame optionBAgentFrame rowPositiveTilt ≤
      -optionBPositiveExponent := by
  have hT : Tfun rowWorldFrame rowPositiveTilt ≤
      ((1156668570196 / 10 ^ 12) - 1) / rowWorldFrame := by
    unfold Tfun
    apply div_le_div_of_nonneg_right _ (by norm_num [rowWorldFrame])
    have he : exp (rowPositiveTilt * rowWorldFrame) ≤ 1156668570196 / 10 ^ 12 := by
      apply exp_le_taylor (b := 1) 20 <;>
        norm_num [rowPositiveTilt, rowWorldFrame, Finset.sum_range_succ, Nat.factorial]
    linarith
  have he : exp (371490087057 / 10 ^ 12) ≤ 1449893473319 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have h := Eplus_le_of_bounds (a := aL) (h := rowRoot + dsL)
    (hW := rowRadius) (cW := rowWorldFrame) (cf := optionBAgentFrame)
    (τ := rowPositiveTilt) (x0lo := 66630010657559783 / 10 ^ 18)
    (x0hi := 66630010657559784 / 10 ^ 18)
    (Thi := ((1156668570196 / 10 ^ 12) - 1) / rowWorldFrame)
    (y := 371490087057 / 10 ^ 12) (ehi := 1449893473319 / 10 ^ 12)
    (by norm_num [rowRoot, dsL]) (by norm_num [rowRadius])
    (by norm_num [rowWorldFrame]) (by norm_num [optionBAgentFrame])
    (by norm_num [rowPositiveTilt]) (by norm_num) x0_lo x0_hi hT
    (by norm_num [optionBAgentFrame, rowWorldFrame, rowRadius, rowRoot, dsL]) he
  apply h.trans
  norm_num [rowPositiveTilt, rowWorldFrame, rowRadius, optionBAgentFrame,
    rowRoot, dsL, optionBPositiveExponent]

theorem optionB_negative_enclosure :
    Eminus aL (rowRoot + dsL) rowRadius rowWorldFrame optionBAgentFrame rowNegativeTilt ≤
      -optionBNegativeExponent := by
  have hlo : 681812223715 / 10 ^ 12 ≤ exp (rowNegativeTilt * rowWorldFrame) := by
    apply le_exp_taylor (b := 1) 20 <;>
      norm_num [rowNegativeTilt, rowWorldFrame, Finset.sum_range_succ, Nat.factorial]
  have hhi : exp (rowNegativeTilt * rowWorldFrame) ≤ 681812223717 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [rowNegativeTilt, rowWorldFrame, Finset.sum_range_succ, Nat.factorial]
  have he : exp (-(708503385397 / 10 ^ 12)) ≤ 492380550228 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hTlo : ((681812223715 / 10 ^ 12) - 1) / rowWorldFrame ≤
      Tfun rowWorldFrame rowNegativeTilt := by
    unfold Tfun
    apply div_le_div_of_nonneg_right _ (by norm_num [rowWorldFrame])
    linarith
  have hThi : Tfun rowWorldFrame rowNegativeTilt ≤
      ((681812223717 / 10 ^ 12) - 1) / rowWorldFrame := by
    unfold Tfun
    apply div_le_div_of_nonneg_right _ (by norm_num [rowWorldFrame])
    linarith
  have h := Eminus_le_of_bounds (a := aL) (h := rowRoot + dsL)
    (hW := rowRadius) (cW := rowWorldFrame) (cf := optionBAgentFrame)
    (τ := rowNegativeTilt) (x0lo := 66630010657559783 / 10 ^ 18)
    (x0hi := 66630010657559784 / 10 ^ 18)
    (Tlo := ((681812223715 / 10 ^ 12) - 1) / rowWorldFrame)
    (Thi := ((681812223717 / 10 ^ 12) - 1) / rowWorldFrame)
    (y := -(708503385397 / 10 ^ 12)) (ehi := 492380550228 / 10 ^ 12)
    (by norm_num [rowRadius]) (by norm_num [rowWorldFrame])
    (by norm_num [optionBAgentFrame]) (by norm_num [rowNegativeTilt])
    (by norm_num [rowRoot, rowRadius, dsL]) x0_lo x0_hi
    hTlo hThi
    (by norm_num [rowWorldFrame])
    (by norm_num [optionBAgentFrame, rowWorldFrame, rowRadius, rowRoot, dsL]) he
    (by norm_num)
  apply h.trans
  norm_num [rowNegativeTilt, rowWorldFrame, rowRadius, optionBAgentFrame,
    rowRoot, dsL, optionBNegativeExponent]

theorem optionB_positive_tail :
    exp (-((12225 : ℝ) * optionBPositiveExponent)) ≤ optionBPositiveBase ^ 8 := by
  apply tail8 (le_refl (12225 : ℝ)) (by norm_num [optionBPositiveExponent])
  apply exp_le_taylor (b := 1) 20 <;>
    norm_num [optionBPositiveExponent, optionBPositiveBase, Finset.sum_range_succ, Nat.factorial]

theorem optionB_negative_tail :
    exp (-((12225 : ℝ) * optionBNegativeExponent)) ≤ optionBNegativeBase ^ 8 := by
  apply tail8 (le_refl (12225 : ℝ)) (by norm_num [optionBNegativeExponent])
  apply exp_le_taylor (b := 1) 20 <;>
    norm_num [optionBNegativeExponent, optionBNegativeBase, Finset.sum_range_succ, Nat.factorial]

end BstLean.Part249
