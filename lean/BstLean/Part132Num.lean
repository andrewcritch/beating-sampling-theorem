import BstLean.Part130Kappa
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Part 132, numerics: polynomial bounds of `κ` and rational bounds of its iterates at `0`

* `arcsin_ge_poly`: `t + t³/6 + 3t⁵/40 ≤ arcsin t` on `[0, 1]`.
* `arcsin_le_poly`: `arcsin t ≤ t + t³/5` on `[0, 2/5]`.
* `kappa_ge_poly`, `kappa_le_poly`: polynomial lower and upper bounds of `κ`.
* `kappa2_zero_le`, `kappa2_zero_ge`, `kappa3_zero_ge`, …, `kappa6_zero_ge`: rational bounds of
  `κ^[j] 0`.
-/

namespace BstLean.Part132

open Real Set BstLean.Part130

lemma interior_Icc_01 : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc

/-- `1 + t²/2 + 3t⁴/8 ≤ 1/√(1 − t²)` on `(−1, 1)`. -/
lemma inv_sqrt_ge_poly {t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 ≤ 1 / Real.sqrt (1 - t ^ 2) := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
  have hq : 0 < 1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 := by positivity
  have hss : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hpos.le
  have hid : (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8) ^ 2 * (1 - t ^ 2)
      = 1 - (5 / 8 * t ^ 6 + 15 / 64 * t ^ 8 + 9 / 64 * t ^ 10) := by ring
  have hnn : 0 ≤ 5 / 8 * t ^ 6 + 15 / 64 * t ^ 8 + 9 / 64 * t ^ 10 := by positivity
  have hsq : ((1 + t ^ 2 / 2 + 3 * t ^ 4 / 8) * Real.sqrt (1 - t ^ 2)) ^ 2 ≤ 1 := by
    rw [mul_pow, hss, hid]; linarith
  have hle : (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8) * Real.sqrt (1 - t ^ 2) ≤ 1 := by
    have hm := mul_pos hq hs
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [le_div_iff₀ hs]
  exact hle

/-- `1/√(1 − t²) ≤ 1 + (3/5)t²` for `0 ≤ t ≤ 2/5`. -/
lemma inv_sqrt_le_poly {t : ℝ} (h1 : 0 ≤ t) (h2 : t ≤ 2 / 5) :
    1 / Real.sqrt (1 - t ^ 2) ≤ 1 + 3 / 5 * t ^ 2 := by
  have hu : t ^ 2 ≤ 4 / 25 := by nlinarith
  have hu0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hpos : 0 < 1 - t ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
  have hq : 0 < 1 + 3 / 5 * t ^ 2 := by positivity
  have hss : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hpos.le
  have hid : (1 + 3 / 5 * t ^ 2) ^ 2 * (1 - t ^ 2)
      = 1 + t ^ 2 * (1 / 5 - 21 / 25 * t ^ 2 - 9 / 25 * (t ^ 2) ^ 2) := by ring
  have hin : 0 ≤ 1 / 5 - 21 / 25 * t ^ 2 - 9 / 25 * (t ^ 2) ^ 2 := by nlinarith
  have hsq : 1 ≤ ((1 + 3 / 5 * t ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 := by
    rw [mul_pow, hss, hid]
    have := mul_nonneg hu0 hin
    linarith
  have hle : 1 ≤ (1 + 3 / 5 * t ^ 2) * Real.sqrt (1 - t ^ 2) := by
    have hm := mul_pos hq hs
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [div_le_iff₀ hs]
  exact hle

lemma hasDerivAt_polyA (t : ℝ) :
    HasDerivAt (fun t : ℝ => t + t ^ 3 / 6 + 3 * t ^ 5 / 40) (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8) t := by
  have h := ((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 6)).add
    (((hasDerivAt_pow 5 t).const_mul 3).div_const 40)
  refine h.congr_deriv ?_
  norm_num
  ring

lemma hasDerivAt_polyB (t : ℝ) :
    HasDerivAt (fun t : ℝ => t + t ^ 3 / 5) (1 + 3 / 5 * t ^ 2) t := by
  have h := (hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 5)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `t + t³/6 + 3t⁵/40 ≤ arcsin t` on `[0, 1]`. -/
theorem arcsin_ge_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t + t ^ 3 / 6 + 3 * t ^ 5 / 40 ≤ Real.arcsin t := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40))
      (1 / Real.sqrt (1 - x ^ 2) - (1 + x ^ 2 / 2 + 3 * x ^ 4 / 8)) x := fun x hx =>
    (Real.hasDerivAt_arcsin (by linarith [hx.1]) hx.2.ne).sub (hasDerivAt_polyA x)
  have hmono : MonotoneOn (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40))
      (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := Real.continuous_arcsin
      exact (by fun_prop : Continuous
        (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40))).continuousOn
    · rw [interior_Icc_01]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc_01]
      intro x hx
      rw [(hd x hx).deriv]
      have := inv_sqrt_ge_poly (t := x) (by linarith [hx.1]) hx.2
      linarith
  have h := hmono (left_mem_Icc.mpr zero_le_one) ⟨h0, h1⟩ h0
  simp only [Real.arcsin_zero] at h
  norm_num at h
  linarith

/-- `arcsin t ≤ t + t³/5` on `[0, 2/5]`. -/
theorem arcsin_le_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 2 / 5) :
    Real.arcsin t ≤ t + t ^ 3 / 5 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) (2 / 5), HasDerivAt
      (fun x : ℝ => (x + x ^ 3 / 5) - Real.arcsin x)
      ((1 + 3 / 5 * x ^ 2) - 1 / Real.sqrt (1 - x ^ 2)) x := fun x hx =>
    (hasDerivAt_polyB x).sub
      (Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2]))
  have hmono : MonotoneOn (fun x : ℝ => (x + x ^ 3 / 5) - Real.arcsin x) (Icc 0 (2 / 5)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := Real.continuous_arcsin
      exact (by fun_prop : Continuous
        (fun x : ℝ => (x + x ^ 3 / 5) - Real.arcsin x)).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x hx).deriv]
      have := inv_sqrt_le_poly (t := x) hx.1.le hx.2.le
      linarith
  have h := hmono (left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  simp only [Real.arcsin_zero] at h
  norm_num at h
  linarith

lemma hasDerivAt_polyK (t : ℝ) :
    HasDerivAt (fun t : ℝ => 1 / π + t / 2 + (t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 80) / π)
      (1 / 2 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40) / π) t := by
  have h := ((hasDerivAt_const t (1 / π)).add ((hasDerivAt_id' t).div_const 2)).add
    (((((hasDerivAt_pow 2 t).div_const 2).add ((hasDerivAt_pow 4 t).div_const 24)).add
      ((hasDerivAt_pow 6 t).div_const 80)).div_const π)
  refine h.congr_deriv ?_
  norm_num
  ring

lemma hasDerivAt_polyL (t : ℝ) :
    HasDerivAt (fun t : ℝ => 1 / π + t / 2 + (t ^ 2 / 2 + t ^ 4 / 20) / π)
      (1 / 2 + (t + t ^ 3 / 5) / π) t := by
  have h := ((hasDerivAt_const t (1 / π)).add ((hasDerivAt_id' t).div_const 2)).add
    ((((hasDerivAt_pow 2 t).div_const 2).add ((hasDerivAt_pow 4 t).div_const 20)).div_const π)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `κ′(t) = 1/2 + arcsin(t)/π`. -/
lemma kappa_deriv_eq (t : ℝ) : (π - Real.arccos t) / π = 1 / 2 + Real.arcsin t / π := by
  have hp := Real.pi_pos
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  field_simp
  ring

/-- Polynomial lower bound of `κ` on `[0, 1]`. -/
theorem kappa_ge_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 / π + t / 2 + (t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 80) / π ≤ kappa t := by
  have hp := Real.pi_pos
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => kappa x - (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80) / π))
      ((π - Real.arccos x) / π - (1 / 2 + (x + x ^ 3 / 6 + 3 * x ^ 5 / 40) / π)) x := fun x hx =>
    (hasDerivAt_kappa (by linarith [hx.1]) hx.2).sub (hasDerivAt_polyK x)
  have hmono : MonotoneOn
      (fun x : ℝ => kappa x - (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80) / π))
      (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := continuous_kappa
      exact (by fun_prop : Continuous (fun x : ℝ =>
        kappa x - (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80) / π))).continuousOn
    · rw [interior_Icc_01]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc_01]
      intro x hx
      rw [(hd x hx).deriv, kappa_deriv_eq]
      have := div_le_div_of_nonneg_right (arcsin_ge_poly hx.1.le hx.2.le) hp.le
      linarith
  have h := hmono (left_mem_Icc.mpr zero_le_one) ⟨h0, h1⟩ h0
  simp only [kappa_zero] at h
  norm_num at h
  rw [one_div]
  linarith

/-- Polynomial upper bound of `κ` on `[0, 2/5]`. -/
theorem kappa_le_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 2 / 5) :
    kappa t ≤ 1 / π + t / 2 + (t ^ 2 / 2 + t ^ 4 / 20) / π := by
  have hp := Real.pi_pos
  have hd : ∀ x ∈ Ioo (0 : ℝ) (2 / 5), HasDerivAt
      (fun x : ℝ => (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 20) / π) - kappa x)
      ((1 / 2 + (x + x ^ 3 / 5) / π) - (π - Real.arccos x) / π) x := fun x hx =>
    (hasDerivAt_polyL x).sub (hasDerivAt_kappa (by linarith [hx.1]) (by linarith [hx.2]))
  have hmono : MonotoneOn
      (fun x : ℝ => (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 20) / π) - kappa x)
      (Icc 0 (2 / 5)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := continuous_kappa
      exact (by fun_prop : Continuous (fun x : ℝ =>
        (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 20) / π) - kappa x)).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x hx).deriv, kappa_deriv_eq]
      have := div_le_div_of_nonneg_right (arcsin_le_poly hx.1.le hx.2.le) hp.le
      linarith
  have h := hmono (left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  simp only [kappa_zero] at h
  norm_num at h
  rw [one_div]
  linarith

lemma one_div_pi_gt : (1 : ℝ) / 3.141593 < 1 / π :=
  one_div_lt_one_div_of_lt Real.pi_pos Real.pi_lt_d6

lemma one_div_pi_lt : 1 / π < (1 : ℝ) / 3.141592 :=
  one_div_lt_one_div_of_lt (by norm_num) Real.pi_gt_d6

/-- One step of the rational lower bound: from `0 ≤ a ≤ s ≤ 1`, a lower bound of `κ(s)`. -/
theorem kappa_ge_of_le {a s c : ℝ} (ha : 0 ≤ a) (has : a ≤ s) (hs : s ≤ 1)
    (hc : c ≤ (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80)) / 3.141593 + a / 2) :
    c ≤ kappa s := by
  have h1 := kappa_monotoneOn (a := a) (b := s) ⟨by linarith, has.trans hs⟩
    ⟨by linarith, hs⟩ has
  have h2 := kappa_ge_poly ha (has.trans hs)
  have hP : 0 ≤ 1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80) := by positivity
  have h3 := mul_le_mul_of_nonneg_left one_div_pi_gt.le hP
  have e1 : (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80)) * (1 / 3.141593)
      = (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80)) / 3.141593 := by ring
  have e2 : (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80)) * (1 / π)
      = 1 / π + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80) / π := by ring
  rw [e1, e2] at h3
  linarith

/-- One step of the rational upper bound: from `0 ≤ s ≤ a ≤ 2/5`, an upper bound of `κ(s)`. -/
theorem kappa_le_of_le {a s c : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (ha : a ≤ 2 / 5)
    (hc : (1 + (a ^ 2 / 2 + a ^ 4 / 20)) / 3.141592 + a / 2 ≤ c) :
    kappa s ≤ c := by
  have h1 := kappa_monotoneOn (a := s) (b := a) ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ hsa
  have h2 := kappa_le_poly (hs.trans hsa) ha
  have hP : 0 ≤ 1 + (a ^ 2 / 2 + a ^ 4 / 20) := by positivity
  have h3 := mul_le_mul_of_nonneg_left one_div_pi_lt.le hP
  have e1 : (1 + (a ^ 2 / 2 + a ^ 4 / 20)) * (1 / 3.141592)
      = (1 + (a ^ 2 / 2 + a ^ 4 / 20)) / 3.141592 := by ring
  have e2 : (1 + (a ^ 2 / 2 + a ^ 4 / 20)) * (1 / π)
      = 1 / π + (a ^ 2 / 2 + a ^ 4 / 20) / π := by ring
  rw [e1, e2] at h3
  linarith

theorem kappa_zero_ge : (318309 : ℝ) / 1000000 ≤ kappa 0 := by
  rw [kappa_zero]
  have := one_div_pi_gt
  norm_num at this ⊢
  linarith

theorem kappa_zero_le : kappa 0 ≤ (31831 : ℝ) / 100000 := by
  rw [kappa_zero]
  have := one_div_pi_lt
  norm_num at this ⊢
  linarith

theorem kappa2_zero_le : kappa (kappa 0) ≤ 49376 / 100000 :=
  kappa_le_of_le (a := 31831 / 100000) (by linarith [kappa_zero_ge]) kappa_zero_le
    (by norm_num) (by norm_num)

theorem kappa2_zero_ge : 49372 / 100000 ≤ kappa (kappa 0) :=
  kappa_ge_of_le (a := 318309 / 1000000) (by norm_num) kappa_zero_ge
    (by linarith [kappa_zero_le]) (by norm_num)

theorem kappa3_zero_ge : 6048 / 10000 ≤ kappa (kappa (kappa 0)) :=
  kappa_ge_of_le (a := 49372 / 100000) (by norm_num) kappa2_zero_ge
    (by linarith [kappa2_zero_le]) (by norm_num)

theorem kappa3_zero_le_one : kappa (kappa (kappa 0)) ≤ 1 :=
  (kappa_mem (by linarith [kappa2_zero_ge]) (by linarith [kappa2_zero_le])).2

theorem kappa4_zero_ge : 68088 / 100000 ≤ kappa (kappa (kappa (kappa 0))) :=
  kappa_ge_of_le (a := 6048 / 10000) (by norm_num) kappa3_zero_ge
    kappa3_zero_le_one (by norm_num)

theorem kappa4_zero_le_one : kappa (kappa (kappa (kappa 0))) ≤ 1 :=
  (kappa_mem (by linarith [kappa3_zero_ge]) kappa3_zero_le_one).2

theorem kappa5_zero_ge : 73577 / 100000 ≤ kappa (kappa (kappa (kappa (kappa 0)))) :=
  kappa_ge_of_le (a := 68088 / 100000) (by norm_num) kappa4_zero_ge
    kappa4_zero_le_one (by norm_num)

theorem kappa5_zero_le_one : kappa (kappa (kappa (kappa (kappa 0)))) ≤ 1 :=
  (kappa_mem (by linarith [kappa4_zero_ge]) kappa4_zero_le_one).2

theorem kappa6_zero_ge : 7768 / 10000 ≤ kappa^[6] 0 := by
  have h : kappa^[6] 0 = kappa (kappa (kappa (kappa (kappa (kappa 0))))) := rfl
  rw [h]
  exact kappa_ge_of_le (a := 73577 / 100000) (by norm_num) kappa5_zero_ge
    kappa5_zero_le_one (by norm_num)

end BstLean.Part132

open BstLean.Part132 in
#print axioms arcsin_ge_poly
open BstLean.Part132 in
#print axioms arcsin_le_poly
open BstLean.Part132 in
#print axioms kappa_ge_poly
open BstLean.Part132 in
#print axioms kappa_le_poly
open BstLean.Part132 in
#print axioms kappa2_zero_le
open BstLean.Part132 in
#print axioms kappa2_zero_ge
open BstLean.Part132 in
#print axioms kappa3_zero_ge
open BstLean.Part132 in
#print axioms kappa4_zero_ge
open BstLean.Part132 in
#print axioms kappa5_zero_ge
open BstLean.Part132 in
#print axioms kappa6_zero_ge
