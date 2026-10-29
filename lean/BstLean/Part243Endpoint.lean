import BstLean.Part160Ledger2Gen

/-! Part 243: the prescribed 12225 endpoint has checked scalar bounds.
The combined hidden and retained event charge remains an explicit premise. -/
namespace BstLean.Part243
open Real BstLean.Part156 BstLean.Part160

noncomputable def rowRoot : ℝ := 8849839910 / 10 ^ 12
noncomputable def rowRadius : ℝ := 20484550 / 10 ^ 10
noncomputable def rowWorldFrame : ℝ := 632463444785 / 10 ^ 12
noncomputable def rowAgentFrame : ℝ := 146004185 / 10 ^ 8
noncomputable def rowMoment : ℝ := 1042120867 / 10 ^ 17
noncomputable def rowPositiveTilt : ℝ := 2301223133 / 10 ^ 10
noncomputable def rowNegativeTilt : ℝ := -(6055701622 / 10 ^ 10)
noncomputable def rowPositiveExponent : ℝ := 505927698 / 10 ^ 12
noncomputable def rowNegativeExponent : ℝ := 495206453 / 10 ^ 12
noncomputable def rowPositiveBase : ℝ := 461570366362 / 10 ^ 12
noncomputable def rowNegativeBase : ℝ := 469194745559 / 10 ^ 12

theorem row_positive_enclosure :
    Eplus aL (rowRoot + dsL) rowRadius rowWorldFrame rowAgentFrame rowPositiveTilt ≤
      -rowPositiveExponent := by
  have hT : Tfun rowWorldFrame rowPositiveTilt ≤
      ((1156668570196 / 10 ^ 12) - 1) / rowWorldFrame := by
    unfold Tfun
    apply div_le_div_of_nonneg_right _ (by norm_num [rowWorldFrame])
    have he : exp (rowPositiveTilt * rowWorldFrame) ≤ 1156668570196 / 10 ^ 12 := by
      apply exp_le_taylor (b := 1) 20 <;>
        norm_num [rowPositiveTilt, rowWorldFrame, Finset.sum_range_succ, Nat.factorial]
    linarith
  have he : exp (371483471787 / 10 ^ 12) ≤ 1449883881914 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have h := Eplus_le_of_bounds (a := aL) (h := rowRoot + dsL)
    (hW := rowRadius) (cW := rowWorldFrame) (cf := rowAgentFrame)
    (τ := rowPositiveTilt) (x0lo := 66630010657559783 / 10 ^ 18)
    (x0hi := 66630010657559784 / 10 ^ 18)
    (Thi := ((1156668570196 / 10 ^ 12) - 1) / rowWorldFrame)
    (y := 371483471787 / 10 ^ 12) (ehi := 1449883881914 / 10 ^ 12)
    (by norm_num [rowRoot, dsL]) (by norm_num [rowRadius])
    (by norm_num [rowWorldFrame]) (by norm_num [rowAgentFrame])
    (by norm_num [rowPositiveTilt]) (by norm_num) x0_lo x0_hi hT
    (by norm_num [rowAgentFrame, rowWorldFrame, rowRadius, rowRoot, dsL]) he
  apply h.trans
  norm_num [rowPositiveTilt, rowWorldFrame, rowRadius, rowAgentFrame,
    rowRoot, dsL, rowPositiveExponent]

theorem row_negative_enclosure :
    Eminus aL (rowRoot + dsL) rowRadius rowWorldFrame rowAgentFrame rowNegativeTilt ≤
      -rowNegativeExponent := by
  have hlo : 681812223715 / 10 ^ 12 ≤ exp (rowNegativeTilt * rowWorldFrame) := by
    apply le_exp_taylor (b := 1) 20 <;>
      norm_num [rowNegativeTilt, rowWorldFrame, Finset.sum_range_succ, Nat.factorial]
  have hhi : exp (rowNegativeTilt * rowWorldFrame) ≤ 681812223717 / 10 ^ 12 := by
    apply exp_le_taylor (b := 1) 20 <;>
      norm_num [rowNegativeTilt, rowWorldFrame, Finset.sum_range_succ, Nat.factorial]
  have he : exp (-(708490768800 / 10 ^ 12)) ≤ 492386762434 / 10 ^ 12 := by
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
    (hW := rowRadius) (cW := rowWorldFrame) (cf := rowAgentFrame)
    (τ := rowNegativeTilt) (x0lo := 66630010657559783 / 10 ^ 18)
    (x0hi := 66630010657559784 / 10 ^ 18)
    (Tlo := ((681812223715 / 10 ^ 12) - 1) / rowWorldFrame)
    (Thi := ((681812223717 / 10 ^ 12) - 1) / rowWorldFrame)
    (y := -(708490768800 / 10 ^ 12)) (ehi := 492386762434 / 10 ^ 12)
    (by norm_num [rowRadius]) (by norm_num [rowWorldFrame])
    (by norm_num [rowAgentFrame]) (by norm_num [rowNegativeTilt])
    (by norm_num [rowRoot, rowRadius, dsL]) x0_lo x0_hi
    hTlo hThi
    (by norm_num [rowWorldFrame])
    (by norm_num [rowAgentFrame, rowWorldFrame, rowRadius, rowRoot, dsL]) he
    (by norm_num)
  apply h.trans
  norm_num [rowNegativeTilt, rowWorldFrame, rowRadius, rowAgentFrame,
    rowRoot, dsL, rowNegativeExponent]

theorem row_positive_tail :
    exp (-((12225 : ℝ) * rowPositiveExponent)) ≤ rowPositiveBase ^ 8 := by
  apply tail8 (le_refl (12225 : ℝ)) (by norm_num [rowPositiveExponent])
  apply exp_le_taylor (b := 1) 20 <;>
    norm_num [rowPositiveExponent, rowPositiveBase, Finset.sum_range_succ, Nat.factorial]

theorem row_negative_tail :
    exp (-((12225 : ℝ) * rowNegativeExponent)) ≤ rowNegativeBase ^ 8 := by
  apply tail8 (le_refl (12225 : ℝ)) (by norm_num [rowNegativeExponent])
  apply exp_le_taylor (b := 1) 20 <;>
    norm_num [rowNegativeExponent, rowNegativeBase, Finset.sum_range_succ, Nat.factorial]

theorem row_radius_guards :
    rowRoot + dsL + rowRadius < √(1 / 100 / aL) ∧
      2 * (rowRoot + dsL) ≤ √(1 / 100 / aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [rowRoot, dsL, rowRadius]
  · apply le_trans _ x0_lo
    norm_num [rowRoot, dsL]

/-- This ledger certifies scalar acceptance, conditional on one combined charge.
The stated charge is an allowance, not a proved network-event supply. -/
theorem row_ledger {hidden retained : ℝ} (h : hidden + retained ≤ 31033 / 10 ^ 7) :
    hidden + rowMoment / rowRadius ^ 2 + retained + 1 / 10 ^ 6 +
      rowPositiveBase ^ 8 + rowNegativeBase ^ 8 ≤ 999667 / 10 ^ 8 := by
  have hn : rowMoment / rowRadius ^ 2 + 1 / 10 ^ 6 +
      rowPositiveBase ^ 8 + rowNegativeBase ^ 8 ≤
      (999667 / 10 ^ 8 : ℝ) - 31033 / 10 ^ 7 := by
    norm_num [rowMoment, rowRadius, rowPositiveBase, rowNegativeBase]
  linarith

theorem row_budget : (999667 / 10 ^ 8 : ℝ) < 1 / 100 := by norm_num

end BstLean.Part243
#print axioms BstLean.Part243.row_positive_enclosure
#print axioms BstLean.Part243.row_negative_enclosure
#print axioms BstLean.Part243.row_positive_tail
#print axioms BstLean.Part243.row_negative_tail
#print axioms BstLean.Part243.row_radius_guards
#print axioms BstLean.Part243.row_ledger
#print axioms BstLean.Part243.row_budget
