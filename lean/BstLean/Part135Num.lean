import BstLean.Part132Quad

/-!
# Part 135, numerics: upper bounds of `κ^[3] 0` and `κ^[4] 0`

* `inv_sqrt_le_poly9`: `1/√(1 − t²) ≤ 1 + t²/2 + 3t⁴/8 + 5t⁶/16 + (3/5)t⁸` on `[0, 7/10]`.
* `arcsin_le_poly9`: `arcsin t ≤ t + t³/6 + 3t⁵/40 + 5t⁷/112 + t⁹/15` on `[0, 7/10]`.
* `kappa_le_poly9`: polynomial upper bound of `κ` on `[0, 7/10]`.
* `kappa3_zero_le`: `κ^[3] 0 ≤ 60485/100000`.
* `kappa4_zero_le`: `κ^[4] 0 ≤ 6810/10000`.
-/

namespace BstLean.Part135

open Real Set BstLean.Part130 BstLean.Part132

/-- `1/√(1 − t²) ≤ 1 + t²/2 + 3t⁴/8 + 5t⁶/16 + (3/5)t⁸` for `0 ≤ t ≤ 7/10`. -/
lemma inv_sqrt_le_poly9 {t : ℝ} (h1 : 0 ≤ t) (h2 : t ≤ 7 / 10) :
    1 / Real.sqrt (1 - t ^ 2)
      ≤ 1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16 + 3 / 5 * t ^ 8 := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t ^ 2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := hu ▸ sq_nonneg t
  have hu1 : u ≤ 1 / 2 := by rw [hu]; nlinarith
  have e4 : t ^ 4 = u ^ 2 := by rw [hu]; ring
  have e6 : t ^ 6 = u ^ 3 := by rw [hu]; ring
  have e8 : t ^ 8 = u ^ 4 := by rw [hu]; ring
  rw [e4, e6, e8, ← hu]
  have hpos : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr hpos
  have hq : 0 < 1 + u / 2 + 3 * u ^ 2 / 8 + 5 * u ^ 3 / 16 + 3 / 5 * u ^ 4 := by positivity
  have hss : Real.sqrt (1 - u) ^ 2 = 1 - u := Real.sq_sqrt hpos.le
  have hid : (1 + u / 2 + 3 * u ^ 2 / 8 + 5 * u ^ 3 / 16 + 3 / 5 * u ^ 4) ^ 2 * (1 - u)
      = 1 + u ^ 4 * (209 / 320 - 131 / 160 * u - 367 / 1280 * u ^ 2 - 221 / 1280 * u ^ 3
        - 3 / 200 * u ^ 4 - 9 / 25 * u ^ 5) := by ring
  have p2 : u ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
  have p3 : u ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hu0 hu1 3
  have p4 : u ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ hu0 hu1 4
  have p5 : u ^ 5 ≤ (1 / 2) ^ 5 := pow_le_pow_left₀ hu0 hu1 5
  have hin : 0 ≤ 209 / 320 - 131 / 160 * u - 367 / 1280 * u ^ 2 - 221 / 1280 * u ^ 3
      - 3 / 200 * u ^ 4 - 9 / 25 * u ^ 5 := by
    norm_num at p2 p3 p4 p5
    linarith
  have hu4 : 0 ≤ u ^ 4 := by positivity
  have hsq : 1 ≤ ((1 + u / 2 + 3 * u ^ 2 / 8 + 5 * u ^ 3 / 16 + 3 / 5 * u ^ 4)
      * Real.sqrt (1 - u)) ^ 2 := by
    rw [mul_pow, hss, hid]
    have := mul_nonneg hu4 hin
    linarith
  have hle : 1 ≤ (1 + u / 2 + 3 * u ^ 2 / 8 + 5 * u ^ 3 / 16 + 3 / 5 * u ^ 4)
      * Real.sqrt (1 - u) := by
    have hm := mul_pos hq hs
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [div_le_iff₀ hs]
  exact hle

lemma hasDerivAt_polyB9 (t : ℝ) :
    HasDerivAt (fun t : ℝ => t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + 5 * t ^ 7 / 112 + t ^ 9 / 15)
      (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16 + 3 / 5 * t ^ 8) t := by
  have h := ((((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 6)).add
    (((hasDerivAt_pow 5 t).const_mul 3).div_const 40)).add
    (((hasDerivAt_pow 7 t).const_mul 5).div_const 112)).add
    ((hasDerivAt_pow 9 t).div_const 15)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `arcsin t ≤ t + t³/6 + 3t⁵/40 + 5t⁷/112 + t⁹/15` on `[0, 7/10]`. -/
theorem arcsin_le_poly9 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 7 / 10) :
    Real.arcsin t ≤ t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + 5 * t ^ 7 / 112 + t ^ 9 / 15 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) (7 / 10), HasDerivAt
      (fun x : ℝ => (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112 + x ^ 9 / 15)
        - Real.arcsin x)
      ((1 + x ^ 2 / 2 + 3 * x ^ 4 / 8 + 5 * x ^ 6 / 16 + 3 / 5 * x ^ 8)
        - 1 / Real.sqrt (1 - x ^ 2)) x := fun x hx =>
    (hasDerivAt_polyB9 x).sub
      (Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2]))
  have hmono : MonotoneOn
      (fun x : ℝ => (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112 + x ^ 9 / 15)
        - Real.arcsin x) (Icc 0 (7 / 10)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := Real.continuous_arcsin
      exact (by fun_prop : Continuous (fun x : ℝ =>
        (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112 + x ^ 9 / 15)
          - Real.arcsin x)).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x hx).deriv]
      have := inv_sqrt_le_poly9 (t := x) hx.1.le hx.2.le
      linarith
  have h := hmono (left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  simp only [Real.arcsin_zero] at h
  norm_num at h
  linarith

lemma hasDerivAt_polyL9 (t : ℝ) :
    HasDerivAt
      (fun t : ℝ => 1 / π + t / 2
        + (t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 80 + 5 * t ^ 8 / 896 + t ^ 10 / 150) / π)
      (1 / 2 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + 5 * t ^ 7 / 112 + t ^ 9 / 15) / π) t := by
  have h := ((hasDerivAt_const t (1 / π)).add ((hasDerivAt_id' t).div_const 2)).add
    (((((((hasDerivAt_pow 2 t).div_const 2).add ((hasDerivAt_pow 4 t).div_const 24)).add
      ((hasDerivAt_pow 6 t).div_const 80)).add
      (((hasDerivAt_pow 8 t).const_mul 5).div_const 896)).add
      ((hasDerivAt_pow 10 t).div_const 150)).div_const π)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- Polynomial upper bound of `κ` on `[0, 7/10]`. -/
theorem kappa_le_poly9 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 7 / 10) :
    kappa t ≤ 1 / π + t / 2
      + (t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 80 + 5 * t ^ 8 / 896 + t ^ 10 / 150) / π := by
  have hp := Real.pi_pos
  have hd : ∀ x ∈ Ioo (0 : ℝ) (7 / 10), HasDerivAt
      (fun x : ℝ => (1 / π + x / 2
        + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80 + 5 * x ^ 8 / 896 + x ^ 10 / 150) / π)
        - kappa x)
      ((1 / 2 + (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112 + x ^ 9 / 15) / π)
        - (π - Real.arccos x) / π) x := fun x hx =>
    (hasDerivAt_polyL9 x).sub (hasDerivAt_kappa (by linarith [hx.1]) (by linarith [hx.2]))
  have hmono : MonotoneOn
      (fun x : ℝ => (1 / π + x / 2
        + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80 + 5 * x ^ 8 / 896 + x ^ 10 / 150) / π)
        - kappa x) (Icc 0 (7 / 10)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := continuous_kappa
      exact (by fun_prop : Continuous (fun x : ℝ => (1 / π + x / 2
        + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80 + 5 * x ^ 8 / 896 + x ^ 10 / 150) / π)
        - kappa x)).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x hx).deriv, kappa_deriv_eq]
      have := div_le_div_of_nonneg_right (arcsin_le_poly9 hx.1.le hx.2.le) hp.le
      linarith
  have h := hmono (left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  simp only [kappa_zero] at h
  norm_num at h
  rw [one_div]
  linarith

/-- One step of the rational upper bound: from `0 ≤ s ≤ a ≤ 7/10`, an upper bound of `κ(s)`. -/
theorem kappa_le_of_le9 {a s c : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (ha : a ≤ 7 / 10)
    (hc : (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896 + a ^ 10 / 150))
      / 3.141592 + a / 2 ≤ c) :
    kappa s ≤ c := by
  have h1 := kappa_monotoneOn (a := s) (b := a) ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ hsa
  have h2 := kappa_le_poly9 (hs.trans hsa) ha
  have hP : 0 ≤ 1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896 + a ^ 10 / 150) := by
    positivity
  have h3 := mul_le_mul_of_nonneg_left one_div_pi_lt.le hP
  have e1 : (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896 + a ^ 10 / 150))
      * (1 / 3.141592)
      = (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896 + a ^ 10 / 150))
        / 3.141592 := by ring
  have e2 : (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896 + a ^ 10 / 150))
      * (1 / π)
      = 1 / π + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896 + a ^ 10 / 150) / π := by
    ring
  rw [e1, e2] at h3
  linarith

/-- `κ^[3] 0 ≤ 0.60485` (true value `0.604823`). -/
theorem kappa3_zero_le' : kappa (kappa (kappa 0)) ≤ 60485 / 100000 :=
  kappa_le_of_le9 (a := 49376 / 100000) (by linarith [kappa2_zero_ge]) kappa2_zero_le
    (by norm_num) (by norm_num)

theorem kappa3_zero_le : kappa (kappa (kappa 0)) ≤ 60490 / 100000 :=
  kappa3_zero_le'.trans (by norm_num)

/-- `κ^[4] 0 ≤ 0.6810` (true value `0.680952`). -/
theorem kappa4_zero_le' : kappa^[4] 0 ≤ 6810 / 10000 := by
  show kappa (kappa (kappa (kappa 0))) ≤ 6810 / 10000
  exact kappa_le_of_le9 (a := 60485 / 100000) (by linarith [kappa3_zero_ge]) kappa3_zero_le'
    (by norm_num) (by norm_num)

theorem kappa4_zero_le : kappa^[4] 0 ≤ 6811 / 10000 :=
  kappa4_zero_le'.trans (by norm_num)

end BstLean.Part135

open BstLean.Part135 in
#print axioms kappa3_zero_le
open BstLean.Part135 in
#print axioms kappa4_zero_le'
open BstLean.Part135 in
#print axioms kappa4_zero_le
