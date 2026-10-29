import BstLean.Part227Hidden

/-! Part 227: the hidden charge with a parameterized exact mean-field bound. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part140 BstLean.Part143 BstLean.Part157 BstLean.Part159

noncomputable def hiddenChargeWithDistance (n : ℕ) (sp p₂ dT eB distancePayment : ℝ) : ℝ :=
  372 / 1000 * sp ^ 2 + 448 / 1000 * p₂ + distancePayment +
    4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) +
    10 ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) + 9 / 10 ^ 8 +
    (1716 / 1000) ^ 2 / ((mW n : ℝ) * eB ^ 2)

/-- The direct distance payment replaces the older distance payment. -/
theorem hidden_charge_of_distance {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB distancePayment : ℝ} (hsp : 0 < sp) (hp₂ : 0 < p₂)
    (hdT : 0 < dT) (heB : 0 < eB)
    (hDist : (hidGauss (2 * n) (mW n)).real (goodDist n Xc)ᶜ ≤ distancePayment) :
    (hidGauss (2 * n) (mW n)).real (hidden n sp p₂ Xc dT eB)ᶜ ≤
      hiddenChargeWithDistance n sp p₂ dT eB distancePayment := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hsub : (hidden n sp p₂ Xc dT eB)ᶜ ⊆
      (((((goodHid (2 * n) (mW n) (sp ^ 2) p₂)ᶜ ∪ (goodDist n Xc)ᶜ) ∪
        (goodT n dT)ᶜ) ∪ (goodS n)ᶜ) ∪ (goodAo n)ᶜ) ∪ (goodB n eB)ᶜ := by
    intro θ hθ
    simpa only [hidden, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or,
      Set.mem_union] using hθ
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have hu := measureReal_union_le (μ := hidGauss (2 * n) (mW n))
  exact (hu _ _).trans (add_le_add
    ((hu _ _).trans (add_le_add
      ((hu _ _).trans (add_le_add
        ((hu _ _).trans (add_le_add
          ((hu _ _).trans (add_le_add (goodHid_charge hn hsp hp₂) hDist))
            (goodT_prob143 hn hdT))) (goodS_charge (by omega) hm)))
              (goodAo_charge hn))) (goodB_charge hn heB))

/-- The squared-deviation estimate retains its source centre qN - kap1. -/
theorem distance_charge_of_mean {n : ℕ} (hn : 4096 ≤ n) {Xc g0 : ℝ}
    (hgap : g0 < Xc)
    (hmean : qN (2 * n) - kap1 (2 * n) ≤ g0 / ((2 * n : ℕ) : ℝ)) :
    (hidGauss (2 * n) (mW n)).real (goodDist n Xc)ᶜ ≤
      31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (Xc - g0) ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hNp : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  let e : ℝ := 2 / ((2 * n : ℕ) : ℝ) * ((Xc - g0) / ((2 * n : ℕ) : ℝ))
  have he : 0 < e := by dsimp [e]; positivity
  have h := abs_charge (dist2_L2_143s hN hm) he
  have hsub : (goodDist n Xc)ᶜ ⊆
      {θ | |dist2 (2 * n) (mW n) θ -
        2 / ((2 * n : ℕ) : ℝ) * (qN (2 * n) - kap1 (2 * n))| ≤ e}ᶜ := by
    intro θ hθ
    change ¬ |dist2 (2 * n) (mW n) θ -
      2 / ((2 * n : ℕ) : ℝ) * (qN (2 * n) - kap1 (2 * n))| ≤ e
    change ¬ dist2 (2 * n) (mW n) θ ≤
      2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) at hθ
    have hm' := mul_le_mul_of_nonneg_left hmean hγ.le
    have hθ' := not_le.mp hθ
    have heq : e = 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) -
        2 / ((2 * n : ℕ) : ℝ) * (g0 / ((2 * n : ℕ) : ℝ)) := by dsimp [e]; ring
    rw [not_le]
    exact lt_of_lt_of_le (by rw [heq]; linarith) (le_abs_self _)
  refine ((measureReal_mono hsub (measure_ne_top _ _)).trans h).trans ?_
  have heq : (2 / ((2 * n : ℕ) : ℝ) * cDst143s (2 * n) (mW n)) ^ 2 / e ^ 2 =
      ((2 * n : ℕ) : ℝ) ^ 2 * cDst143s (2 * n) (mW n) ^ 2 / (Xc - g0) ^ 2 := by
    dsimp [e]
    field_simp
  rw [heq]
  have hc := mul_le_mul_of_nonneg_left (cDst143s_sq_le hn) (sq_nonneg (((2 * n : ℕ) : ℝ)))
  have he' : ((2 * n : ℕ) : ℝ) ^ 2 * (7794 / 100 / (mW n : ℝ)) =
      31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by push_cast; ring
  rw [he'] at hc
  exact div_le_div_of_nonneg_right hc (sq_nonneg _)

noncomputable def hiddenChargeSharp (n : ℕ) (sp p₂ Xc dT eB g0 : ℝ) : ℝ :=
  372 / 1000 * sp ^ 2 + 448 / 1000 * p₂ +
    31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (Xc - g0) ^ 2 +
    4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) +
    10 ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) + 9 / 10 ^ 8 +
    (1716 / 1000) ^ 2 / ((mW n : ℝ) * eB ^ 2)

/-- The parameterized mean-field bound changes only the distance payment. -/
theorem hidden_charge_sharp {n : ℕ} (hn : 4096 ≤ n) {sp p₂ Xc dT eB g0 : ℝ}
    (hsp : 0 < sp) (hp₂ : 0 < p₂) (hgap : g0 < Xc)
    (hmean : qN (2 * n) - kap1 (2 * n) ≤ g0 / ((2 * n : ℕ) : ℝ))
    (hdT : 0 < dT) (heB : 0 < eB) :
    (hidGauss (2 * n) (mW n)).real (hidden n sp p₂ Xc dT eB)ᶜ ≤
      hiddenChargeSharp n sp p₂ Xc dT eB g0 := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hsub : (hidden n sp p₂ Xc dT eB)ᶜ ⊆
      (((((goodHid (2 * n) (mW n) (sp ^ 2) p₂)ᶜ ∪ (goodDist n Xc)ᶜ) ∪
        (goodT n dT)ᶜ) ∪ (goodS n)ᶜ) ∪ (goodAo n)ᶜ) ∪ (goodB n eB)ᶜ := by
    intro θ hθ
    simpa only [hidden, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or,
      Set.mem_union] using hθ
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have hu := measureReal_union_le (μ := hidGauss (2 * n) (mW n))
  exact (hu _ _).trans (add_le_add
    ((hu _ _).trans (add_le_add
      ((hu _ _).trans (add_le_add
        ((hu _ _).trans (add_le_add
          ((hu _ _).trans (add_le_add (goodHid_charge hn hsp hp₂)
            (distance_charge_of_mean hn hgap hmean))) (goodT_prob143 hn hdT)))
              (goodS_charge (by omega) hm))) (goodAo_charge hn))) (goodB_charge hn heB))

end BstLean.Part227
#print axioms BstLean.Part227.distance_charge_of_mean
#print axioms BstLean.Part227.hidden_charge_sharp
#print axioms BstLean.Part227.hidden_charge_of_distance
