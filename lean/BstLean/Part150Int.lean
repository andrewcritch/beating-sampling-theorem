import BstLean.Part150Peak2

/-!
# Part 150, item 2: the two integrals `∫_0^∞ |dChar J t|/t^p dt`, `p = 2, 3`

Paper source: `onW45-opus-prover.md` §2, Lemma B-F, Steps 2 to 4.

* `Mmaj c J p`: a majorant of `|dChar J t|/t^p` on `(0, ∞)`: Region A (constant `c`), the Gaussian
  tail beyond `√J`, and the peaks beyond `(π/2)√J`.
* `dChar_le_Mmaj`: the majorant property. `int_M2`, `int_M3`: integrability and the two bounds
  `∫ Mmaj c J 2 ≤ (c√(π/2) + √(2π)/6 + (44/9)(√(2π)/90)/J + e^{−J/2}/√J)/J`,
  `∫ Mmaj c J 3 ≤ (c + √(2π)·(56807/(6750π³))/√J + e^{−J/2}/J)/J`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology

/-- The majorant of `|dChar J t|/t^p`. -/
noncomputable def Mmaj (c : ℝ) (J p : ℕ) (t : ℝ) : ℝ :=
  c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ p +
    (Ioi (√(J : ℝ))).indicator (fun t => t * rexp (-(t ^ 2 / 2)) / √(J : ℝ) ^ (p + 1)) t +
    (Ioi (π / 2 * √(J : ℝ))).indicator (fun t => |Real.cos (t / √(J : ℝ))| ^ J / t ^ p) t

lemma tail_term {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (p : ℕ) :
    rexp (-(t ^ 2 / 2)) / t ^ p ≤ t * rexp (-(t ^ 2 / 2)) / s ^ (p + 1) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  rw [div_le_div_iff₀ (pow_pos ht p) (pow_pos hs (p + 1))]
  have h1 : s ^ (p + 1) ≤ t ^ (p + 1) := pow_le_pow_left₀ hs.le hst (p + 1)
  calc rexp (-(t ^ 2 / 2)) * s ^ (p + 1) ≤ rexp (-(t ^ 2 / 2)) * t ^ (p + 1) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = t * rexp (-(t ^ 2 / 2)) * t ^ p := by ring

/-- **The majorant property.** -/
theorem dChar_le_Mmaj {c : ℝ} (hc0 : 0 ≤ c) (hc : RegA c) {J : ℕ} (hJ : 1 ≤ J) (p : ℕ) {t : ℝ}
    (ht : 0 < t) : |dChar J t| / t ^ p ≤ Mmaj c J p t := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hs : 0 < √(J : ℝ) := Real.sqrt_pos.mpr hJpos
  have hpi : √(J : ℝ) ≤ π / 2 * √(J : ℝ) := by nlinarith [Real.pi_gt_three]
  have htp : 0 < t ^ p := pow_pos ht p
  have hA0 : 0 ≤ c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ p := by positivity
  unfold Mmaj
  rcases le_or_gt t (√(J : ℝ)) with h1 | h1
  · rw [indicator_of_notMem (show t ∉ Ioi (√(J : ℝ)) from not_lt.mpr h1),
      indicator_of_notMem (show t ∉ Ioi (π / 2 * √(J : ℝ)) from not_lt.mpr (h1.trans hpi)),
      add_zero, add_zero]
    have h0 := (dChar_B hJ ht.le (h1.trans hpi)).1
    rw [abs_of_nonneg h0]
    exact div_le_div_of_nonneg_right (dChar_A hc hJ ht.le h1) htp.le
  · rw [indicator_of_mem (show t ∈ Ioi (√(J : ℝ)) from h1)]
    have hT := tail_term hs h1.le p
    rcases le_or_gt t (π / 2 * √(J : ℝ)) with h2 | h2
    · rw [indicator_of_notMem (show t ∉ Ioi (π / 2 * √(J : ℝ)) from not_lt.mpr h2), add_zero]
      obtain ⟨h0, hle⟩ := dChar_B hJ ht.le h2
      rw [abs_of_nonneg h0]
      have := div_le_div_of_nonneg_right hle htp.le
      linarith
    · rw [indicator_of_mem (show t ∈ Ioi (π / 2 * √(J : ℝ)) from h2)]
      have := div_le_div_of_nonneg_right (dChar_C J t) htp.le
      rw [add_div] at this
      linarith

/-! ## The three parts of the integral -/

/-- The Gaussian tail part. -/
lemma int_tail {a : ℝ} (ha : 0 ≤ a) (K : ℝ) :
    IntegrableOn ((Ioi a).indicator (fun t : ℝ => t * rexp (-(t ^ 2 / 2)) / K)) (Ioi 0) ∧
    ∫ t in Ioi 0, (Ioi a).indicator (fun t : ℝ => t * rexp (-(t ^ 2 / 2)) / K) t =
      rexp (-(a ^ 2 / 2)) / K := by
  constructor
  · exact (((integral_mul_exp_Ioi 0).1).div_const K).indicator measurableSet_Ioi
  · rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr ha,
      integral_div, (integral_mul_exp_Ioi a).2]

/-- The peak part. -/
lemma int_peak {J : ℕ} (hJ : 1 ≤ J) {p : ℕ} (hp : 2 ≤ p) :
    IntegrableOn ((Ioi (π / 2 * √(J : ℝ))).indicator
      (fun t : ℝ => |Real.cos (t / √(J : ℝ))| ^ J / t ^ p)) (Ioi 0) ∧
    ∫ t in Ioi 0, (Ioi (π / 2 * √(J : ℝ))).indicator
      (fun t : ℝ => |Real.cos (t / √(J : ℝ))| ^ J / t ^ p) t =
      √(J : ℝ) / √(J : ℝ) ^ p * ∫ u in Ioi (π / 2), pk J p u := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hs : 0 < √(J : ℝ) := Real.sqrt_pos.mpr hJpos
  have ha : 0 < π / 2 * √(J : ℝ) := by positivity
  set q : ℝ → ℝ := fun t => |Real.cos (t / √(J : ℝ))| ^ J / t ^ p with hq
  have hqi : IntegrableOn q (Ioi (π / 2 * √(J : ℝ))) := by
    have hD : IntegrableOn (fun t : ℝ => t ^ (-(p : ℝ))) (Ioi (π / 2 * √(J : ℝ))) :=
      integrableOn_Ioi_rpow_of_lt (by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp
        linarith) ha
    have hm : Measurable q := by simp only [hq]; fun_prop
    refine Integrable.mono' hD hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans ha hu
    have hq0 : 0 ≤ q u := by simp only [hq]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hq0, Real.rpow_neg hu0.le, Real.rpow_natCast]
    simp only [hq]
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity)
      (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))
  constructor
  · rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi]
    exact hqi.mono_measure Measure.restrict_le_self
  · rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr ha.le]
    have h := integral_comp_mul_left_Ioi (pk J p) (π / 2 * √(J : ℝ)) (inv_pos.mpr hs)
    have e : ∀ t : ℝ, q t = ((√(J : ℝ))⁻¹) ^ p * pk J p ((√(J : ℝ))⁻¹ * t) := by
      intro t
      simp only [hq, pk]
      rcases eq_or_ne t 0 with rfl | ht
      · rcases Nat.eq_zero_or_pos p with rfl | hp0
        · omega
        · simp [zero_pow hp0.ne']
      · rw [show (√(J : ℝ))⁻¹ * t = t / √(J : ℝ) by rw [div_eq_inv_mul], div_pow, inv_pow]
        field_simp
    simp_rw [e]
    rw [integral_const_mul, h, smul_eq_mul, inv_inv,
      show (√(J : ℝ))⁻¹ * (π / 2 * √(J : ℝ)) = π / 2 by field_simp]
    rw [inv_pow]
    field_simp

/-- The Region A part, second power. -/
lemma int_A2 (c : ℝ) (J : ℕ) :
    IntegrableOn (fun t : ℝ => c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 2) (Ioi 0) ∧
    ∫ t in Ioi 0, c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 2 = c * √(π / 2) / J := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have e : ∀ t ∈ Ioi (0 : ℝ), c / J * (t ^ 2 * rexp (-(1 / 2) * t ^ 2)) =
      c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 2 := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    rw [show -(1 / 2) * t ^ 2 = -(t ^ 2 / 2) by ring]
    field_simp
  constructor
  · have h1 : IntegrableOn (fun t : ℝ => c / J * (t ^ 2 * rexp (-(1 / 2) * t ^ 2))) (Ioi 0) :=
      (integrableOn_sq_exp hb).const_mul (c / J)
    exact h1.congr_fun e measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, integral_sq_exp_Ioi hb]
    have e2 : √(π / 2) = √(π / (1 / 2)) / 2 := by
      rw [show π / 2 = (π / (1 / 2)) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [e2]; ring

/-- The Region A part, third power. -/
lemma int_A3 (c : ℝ) (J : ℕ) :
    IntegrableOn (fun t : ℝ => c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 3) (Ioi 0) ∧
    ∫ t in Ioi 0, c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 3 = c / J := by
  have e : ∀ t ∈ Ioi (0 : ℝ), c / J * (t * rexp (-(t ^ 2 / 2))) =
      c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 3 := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
  constructor
  · have h1 : IntegrableOn (fun t : ℝ => c / J * (t * rexp (-(t ^ 2 / 2)))) (Ioi 0) :=
      ((integral_mul_exp_Ioi 0).1).const_mul (c / J)
    exact h1.congr_fun e measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      (integral_mul_exp_Ioi 0).2]
    simp

/-- **The integral of the majorant, second power.** -/
theorem int_M2 (c : ℝ) {J : ℕ} (hJ : 1 ≤ J) :
    IntegrableOn (Mmaj c J 2) (Ioi 0) ∧
    ∫ t in Ioi 0, Mmaj c J 2 t ≤
      (c * √(π / 2) + √(2 * π) / 6 + 44 / 9 * (√(2 * π) / 90) / J + rexp (-((J : ℝ) / 2)) / √(J : ℝ)) /
        J := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hs : 0 < √(J : ℝ) := Real.sqrt_pos.mpr hJpos
  obtain ⟨hA, hAe⟩ := int_A2 c J
  obtain ⟨hT, hTe⟩ := int_tail hs.le (√(J : ℝ) ^ (2 + 1))
  obtain ⟨hP, hPe⟩ := int_peak hJ (p := 2) le_rfl
  refine ⟨(hA.add hT).add hP, ?_⟩
  have hsplit : ∫ t in Ioi 0, Mmaj c J 2 t =
      c * √(π / 2) / J + rexp (-(√(J : ℝ) ^ 2 / 2)) / √(J : ℝ) ^ (2 + 1) +
        √(J : ℝ) / √(J : ℝ) ^ 2 * ∫ u in Ioi (π / 2), pk J 2 u := by
    have hAT : IntegrableOn (fun t : ℝ => c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 2 +
        (Ioi (√(J : ℝ))).indicator (fun t => t * rexp (-(t ^ 2 / 2)) / √(J : ℝ) ^ (2 + 1)) t)
        (Ioi 0) := hA.add hT
    unfold Mmaj
    rw [integral_add hAT hP, integral_add hA hT, hAe, hTe, hPe]
  rw [hsplit, Real.sq_sqrt hJpos.le]
  have hpk := peak2 hJ
  have hsq : √(J : ℝ) ^ 2 = J := Real.sq_sqrt hJpos.le
  have h2pi : √(2 * π / J) = √(2 * π) / √(J : ℝ) := Real.sqrt_div' _ hJpos.le
  have h1 : √(J : ℝ) / J * ∫ u in Ioi (π / 2), pk J 2 u ≤
      √(J : ℝ) / J * (√(2 * π) / √(J : ℝ) * (1 / 6 + 22 / (405 * J))) := by
    rw [← h2pi]
    exact mul_le_mul_of_nonneg_left hpk (by positivity)
  have e : (c * √(π / 2) + √(2 * π) / 6 + 44 / 9 * (√(2 * π) / 90) / J +
      rexp (-((J : ℝ) / 2)) / √(J : ℝ)) / J =
      c * √(π / 2) / J + rexp (-((J : ℝ) / 2)) / √(J : ℝ) ^ (2 + 1) +
        √(J : ℝ) / J * (√(2 * π) / √(J : ℝ) * (1 / 6 + 22 / (405 * J))) := by
    rw [pow_succ, hsq]
    field_simp
    ring
  rw [e]
  linarith

/-- **The integral of the majorant, third power.** -/
theorem int_M3 (c : ℝ) {J : ℕ} (hJ : 1 ≤ J) :
    IntegrableOn (Mmaj c J 3) (Ioi 0) ∧
    ∫ t in Ioi 0, Mmaj c J 3 t ≤
      (c + √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) + rexp (-((J : ℝ) / 2)) / J) / J := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hs : 0 < √(J : ℝ) := Real.sqrt_pos.mpr hJpos
  have hpi := Real.pi_pos
  obtain ⟨hA, hAe⟩ := int_A3 c J
  obtain ⟨hT, hTe⟩ := int_tail hs.le (√(J : ℝ) ^ (3 + 1))
  obtain ⟨hP, hPe⟩ := int_peak hJ (p := 3) (by norm_num)
  refine ⟨(hA.add hT).add hP, ?_⟩
  have hsplit : ∫ t in Ioi 0, Mmaj c J 3 t =
      c / J + rexp (-(√(J : ℝ) ^ 2 / 2)) / √(J : ℝ) ^ (3 + 1) +
        √(J : ℝ) / √(J : ℝ) ^ 3 * ∫ u in Ioi (π / 2), pk J 3 u := by
    have hAT : IntegrableOn (fun t : ℝ => c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J / t ^ 3 +
        (Ioi (√(J : ℝ))).indicator (fun t => t * rexp (-(t ^ 2 / 2)) / √(J : ℝ) ^ (3 + 1)) t)
        (Ioi 0) := hA.add hT
    unfold Mmaj
    rw [integral_add hAT hP, integral_add hA hT, hAe, hTe, hPe]
  rw [hsplit, Real.sq_sqrt hJpos.le]
  have hpk := peak3 hJ
  have hsq : √(J : ℝ) ^ 2 = J := Real.sq_sqrt hJpos.le
  have h4 : √(J : ℝ) ^ (3 + 1) = (J : ℝ) ^ 2 := by
    rw [show 3 + 1 = 2 * 2 from rfl, pow_mul, hsq]
  have h3 : √(J : ℝ) / √(J : ℝ) ^ 3 = 1 / J := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hsq]; field_simp
  have h2pi : √(2 * π / J) = √(2 * π) / √(J : ℝ) := Real.sqrt_div' _ hJpos.le
  have h1 : 1 / (J : ℝ) * ∫ u in Ioi (π / 2), pk J 3 u ≤
      1 / (J : ℝ) * (56807 / (6750 * π ^ 3) * (√(2 * π) / √(J : ℝ))) := by
    rw [← h2pi]
    exact mul_le_mul_of_nonneg_left hpk (by positivity)
  rw [h3, h4]
  have e : (c + √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) + rexp (-((J : ℝ) / 2)) / J) / J =
      c / J + rexp (-((J : ℝ) / 2)) / (J : ℝ) ^ 2 +
        1 / (J : ℝ) * (56807 / (6750 * π ^ 3) * (√(2 * π) / √(J : ℝ))) := by
    field_simp
    ring
  rw [e]
  linarith

end BstLean.Part150
