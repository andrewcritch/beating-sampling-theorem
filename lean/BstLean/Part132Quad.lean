import BstLean.Part132Num

/-!
# Part 132, quadratic bound of `κ∘κ` around `0`, and a sharper bound of `κ^[6] 0`

* `kappa_le_quad`: `κ(t) ≤ κ(0) + t/2 + t²/4` on `[−1, 1]`.
* `kappa_ge_lin`: `κ(0) + t/2 ≤ κ(t)` on `[−1, 1]`.
* `kappa_le_quad_at`: `κ(s) ≤ κ(u) + β(s − u) + (2912/10000)(s − u)²` on `[0, 1]`, with `u = κ(0)`,
  `β = κ′(u)`.
* `kk_quad`: `κ(κ(t)) ≤ κ(κ(0)) + b·t + (8/25)t²` on `[−1, 1]`.
* `kappa6_zero_ge'`: `7771/10000 ≤ κ^[6] 0`.
-/

namespace BstLean.Part132

open Real Set BstLean.Part130

/-- If `f′ ≤ 0` on `(a, c)` and `f′ ≥ 0` on `(c, b)` then `f(c) ≤ f` on `[a, b]`. -/
lemma ge_of_deriv_sign {f f' : ℝ → ℝ} {a b c : ℝ} (hf : Continuous f)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hpos : ∀ x ∈ Ioo c b, 0 ≤ f' x) (hneg : ∀ x ∈ Ioo a c, f' x ≤ 0) :
    ∀ x ∈ Icc a b, f c ≤ f x := by
  intro x hx
  rcases le_total c x with h | h
  · have hmono : MonotoneOn f (Icc c b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hf.continuousOn ?_ ?_
      · rw [interior_Icc]
        exact fun y hy =>
          (hd y ⟨lt_of_le_of_lt hac hy.1, hy.2⟩).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro y hy
        rw [(hd y ⟨lt_of_le_of_lt hac hy.1, hy.2⟩).deriv]
        exact hpos y hy
    exact hmono ⟨le_refl _, hcb⟩ ⟨h, hx.2⟩ h
  · have hanti : AntitoneOn f (Icc a c) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hf.continuousOn ?_ ?_
      · rw [interior_Icc]
        exact fun y hy =>
          (hd y ⟨hy.1, lt_of_lt_of_le hy.2 hcb⟩).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro y hy
        rw [(hd y ⟨hy.1, lt_of_lt_of_le hy.2 hcb⟩).deriv]
        exact hneg y hy
    exact hanti ⟨hx.1, h⟩ ⟨hac, le_refl _⟩ h

lemma hasDerivAt_quadQ (c m C u x : ℝ) :
    HasDerivAt (fun x : ℝ => c + m * (x - u) + C * (x - u) ^ 2) (m + 2 * C * (x - u)) x := by
  have h := ((hasDerivAt_const x c).add (((hasDerivAt_id' x).sub_const u).const_mul m)).add
    ((((hasDerivAt_id' x).sub_const u).pow 2).const_mul C)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `arcsin t ≤ (π/2)·t` on `[0, 1]`. -/
lemma arcsin_le_half_pi_mul {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.arcsin t ≤ π / 2 * t := by
  have hp := Real.pi_pos
  have hx0 : 0 ≤ π / 2 * t := by positivity
  have hx1 : π / 2 * t ≤ π / 2 := by nlinarith
  have h := Real.mul_le_sin hx0 hx1
  have e : 2 / π * (π / 2 * t) = t := by field_simp
  rw [e] at h
  have h2 := Real.monotone_arcsin h
  rwa [Real.arcsin_sin (by linarith) hx1] at h2

/-- (U1) `κ(t) ≤ κ(0) + t/2 + t²/4` on `[−1, 1]`. -/
theorem kappa_le_quad {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    kappa t ≤ kappa 0 + t / 2 + t ^ 2 / 4 := by
  have hp := Real.pi_pos
  have h := ge_of_deriv_sign
    (f := fun x : ℝ => (kappa 0 + 1 / 2 * (x - 0) + 1 / 4 * (x - 0) ^ 2) - kappa x)
    (f' := fun x : ℝ => (1 / 2 + 2 * (1 / 4) * (x - 0)) - (π - Real.arccos x) / π)
    (a := -1) (b := 1) (c := 0)
    (by have := continuous_kappa; fun_prop)
    (fun x hx => (hasDerivAt_quadQ _ _ _ _ x).sub (hasDerivAt_kappa hx.1 hx.2))
    (by norm_num) (by norm_num)
    (by
      intro x hx
      simp only [kappa_deriv_eq]
      have ha := arcsin_le_half_pi_mul hx.1.le hx.2.le
      have hb : Real.arcsin x / π ≤ x / 2 := by
        rw [div_le_iff₀ hp]; linarith
      linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq]
      have ha := arcsin_le_half_pi_mul (t := -x) (by linarith [hx.2]) (by linarith [hx.1])
      rw [Real.arcsin_neg] at ha
      have hb : x / 2 ≤ Real.arcsin x / π := by
        rw [le_div_iff₀ hp]; linarith
      linarith)
    t ⟨h1, h2⟩
  beta_reduce at h
  linarith

/-- (L1) `κ(0) + t/2 ≤ κ(t)` on `[−1, 1]`. -/
theorem kappa_ge_lin {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    kappa 0 + t / 2 ≤ kappa t := by
  have hp := Real.pi_pos
  have h := ge_of_deriv_sign
    (f := fun x : ℝ => kappa x - (kappa 0 + 1 / 2 * (x - 0) + 0 * (x - 0) ^ 2))
    (f' := fun x : ℝ => (π - Real.arccos x) / π - (1 / 2 + 2 * 0 * (x - 0)))
    (a := -1) (b := 1) (c := 0)
    (by have := continuous_kappa; fun_prop)
    (fun x hx => (hasDerivAt_kappa hx.1 hx.2).sub (hasDerivAt_quadQ _ _ _ _ x))
    (by norm_num) (by norm_num)
    (by
      intro x hx
      simp only [kappa_deriv_eq]
      have hb : 0 ≤ Real.arcsin x / π := div_nonneg (Real.arcsin_nonneg.mpr hx.1.le) hp.le
      linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq]
      have hb : Real.arcsin x / π ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (Real.arcsin_nonpos.mpr hx.2.le) hp.le
      linarith)
    t ⟨h1, h2⟩
  beta_reduce at h
  linarith

/-- `arcsin` is convex on `[0, 1]`. -/
lemma arcsin_convexOn : ConvexOn ℝ (Icc (0 : ℝ) 1) Real.arcsin := by
  refine MonotoneOn.convexOn_of_deriv (convex_Icc _ _) Real.continuous_arcsin.continuousOn ?_ ?_
  · rw [interior_Icc_01]
    exact fun t ht => (Real.hasDerivAt_arcsin (by linarith [ht.1])
      ht.2.ne).differentiableAt.differentiableWithinAt
  · rw [interior_Icc_01]
    intro s hs t ht hst
    rw [(Real.hasDerivAt_arcsin (by linarith [hs.1]) hs.2.ne).deriv,
      (Real.hasDerivAt_arcsin (by linarith [ht.1]) ht.2.ne).deriv]
    have hpt : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hle : 1 - t ^ 2 ≤ 1 - s ^ 2 := by nlinarith [hs.1, ht.1]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpt) (Real.sqrt_le_sqrt hle)

lemma arcsin_kappa_zero_ge : (3239 : ℝ) / 10000 ≤ Real.arcsin (kappa 0) := by
  have h := Real.monotone_arcsin kappa_zero_ge
  have h2 := arcsin_ge_poly (t := 318309 / 1000000) (by norm_num) (by norm_num)
  have h3 : (3239 : ℝ) / 10000 ≤ 318309 / 1000000 + (318309 / 1000000) ^ 3 / 6
      + 3 * (318309 / 1000000) ^ 5 / 40 := by norm_num
  linarith

lemma arcsin_kappa_zero_le : Real.arcsin (kappa 0) ≤ (3248 : ℝ) / 10000 := by
  have h := Real.monotone_arcsin kappa_zero_le
  have h2 := arcsin_le_poly (t := 31831 / 100000) (by norm_num) (by norm_num)
  have h3 : (31831 : ℝ) / 100000 + (31831 / 100000) ^ 3 / 5 ≤ 3248 / 10000 := by norm_num
  linarith

/-- `0 ≤ β ≤ 6034/10000` for `β = κ′(κ(0))`. -/
lemma kappa_beta_bounds : 0 ≤ (π - Real.arccos (kappa 0)) / π ∧
    (π - Real.arccos (kappa 0)) / π ≤ 6034 / 10000 := by
  have hp := Real.pi_pos
  refine ⟨(kappa_deriv_bounds _).1, ?_⟩
  rw [kappa_deriv_eq]
  have h1 := arcsin_kappa_zero_le
  have h2 := Real.pi_gt_d6
  have hb : Real.arcsin (kappa 0) / π ≤ 1034 / 10000 := by
    rw [div_le_iff₀ hp]
    norm_num at h2 ⊢
    linarith
  linarith

/-- The slopes of `arcsin` from `κ(0)` are at most `2π·(2912/10000)` on `[0, 1]`. -/
lemma arcsin_slope_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hne : s ≠ kappa 0) :
    (Real.arcsin s - Real.arcsin (kappa 0)) / (s - kappa 0) ≤ 2 * (2912 / 10000) * π := by
  have hu0 := kappa_zero_ge
  have hu1 := kappa_zero_le
  have hu : kappa 0 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hne1 : (1 : ℝ) ≠ kappa 0 := by
    intro h; linarith
  have h := arcsin_convexOn.secant_mono hu ⟨hs0, hs1⟩ (right_mem_Icc.mpr zero_le_one)
    hne hne1 hs1
  rw [Real.arcsin_one] at h
  refine h.trans ?_
  have h1u : 0 < 1 - kappa 0 := by linarith
  rw [div_le_iff₀ h1u]
  have ha := arcsin_kappa_zero_ge
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hm := mul_le_mul_of_nonneg_right hp1.le h1u.le
  norm_num at hp1 hp2 hm
  nlinarith

/-- (U2) `κ(s) ≤ κ(u) + β(s − u) + (2912/10000)(s − u)²` on `[0, 1]`, `u = κ(0)`, `β = κ′(u)`. -/
theorem kappa_le_quad_at {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    kappa s ≤ kappa (kappa 0) + (π - Real.arccos (kappa 0)) / π * (s - kappa 0)
      + 2912 / 10000 * (s - kappa 0) ^ 2 := by
  have hp := Real.pi_pos
  have hu0 := kappa_zero_ge
  have hu1 := kappa_zero_le
  have h := ge_of_deriv_sign
    (f := fun x : ℝ => (kappa (kappa 0) + (π - Real.arccos (kappa 0)) / π * (x - kappa 0)
      + 2912 / 10000 * (x - kappa 0) ^ 2) - kappa x)
    (f' := fun x : ℝ => ((π - Real.arccos (kappa 0)) / π + 2 * (2912 / 10000) * (x - kappa 0))
      - (π - Real.arccos x) / π)
    (a := 0) (b := 1) (c := kappa 0)
    (by have := continuous_kappa; fun_prop)
    (fun x hx => (hasDerivAt_quadQ _ _ _ _ x).sub
      (hasDerivAt_kappa (by linarith [hx.1]) hx.2))
    (by linarith) (by linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq]
      have hpos : 0 < x - kappa 0 := by linarith [hx.1]
      have ha := arcsin_slope_le (s := x) (by linarith [hx.1]) hx.2.le hx.1.ne'
      rw [div_le_iff₀ hpos] at ha
      have hb : (Real.arcsin x - Real.arcsin (kappa 0)) / π
          ≤ 2 * (2912 / 10000) * (x - kappa 0) := by
        rw [div_le_iff₀ hp]; linarith
      rw [sub_div] at hb
      linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq]
      have hneg : x - kappa 0 < 0 := by linarith [hx.2]
      have ha := arcsin_slope_le (s := x) hx.1.le (by linarith [hx.2]) hx.2.ne
      rw [div_le_iff_of_neg hneg] at ha
      have hb : 2 * (2912 / 10000) * (x - kappa 0)
          ≤ (Real.arcsin x - Real.arcsin (kappa 0)) / π := by
        rw [le_div_iff₀ hp]; linarith
      rw [sub_div] at hb
      linarith)
    s ⟨h0, h1⟩
  beta_reduce at h
  nlinarith

/-- A quadratic upper bound of `κ∘κ` around `0`, on all of `[−1, 1]`. -/
theorem kk_quad : ∃ b : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1,
    kappa (kappa t) ≤ kappa (kappa 0) + b * t + 8 / 25 * t ^ 2 := by
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (π - Real.arccos (kappa 0)) / π := ⟨_, rfl⟩
  refine ⟨β / 2, fun t ht => ?_⟩
  have hβ0 : 0 ≤ β := hβ ▸ kappa_beta_bounds.1
  have hβ1 : β ≤ 6034 / 10000 := hβ ▸ kappa_beta_bounds.2
  have hs := kappa_mem ht.1 ht.2
  have hU := kappa_le_quad ht.1 ht.2
  have hL := kappa_ge_lin ht.1 ht.2
  have h2 := kappa_le_quad_at hs.1 hs.2
  rw [← hβ] at h2
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = kappa t - kappa 0 := ⟨_, rfl⟩
  rw [← hδ] at h2
  have hδ1 : t / 2 ≤ δ := by linarith
  have hδ2 : δ ≤ t / 2 + t ^ 2 / 4 := by linarith
  have hsq : δ ^ 2 ≤ 9 / 16 * t ^ 2 := by
    rcases le_total 0 t with h0 | h0
    · have hδ0 : 0 ≤ δ := by linarith
      have hδ3 : δ ≤ 3 / 4 * t := by nlinarith [ht.2]
      have := mul_le_mul hδ3 hδ3 hδ0 (by linarith)
      nlinarith
    · have hδ0 : 0 ≤ -δ := by nlinarith [ht.1]
      have hδ3 : -δ ≤ -t / 2 := by linarith
      have := mul_le_mul hδ3 hδ3 hδ0 (by linarith)
      nlinarith [sq_nonneg t]
  have h3 : β * δ ≤ β * (t / 2 + t ^ 2 / 4) := mul_le_mul_of_nonneg_left hδ2 hβ0
  have h4 : β * t ^ 2 ≤ 6034 / 10000 * t ^ 2 := mul_le_mul_of_nonneg_right hβ1 (sq_nonneg t)
  nlinarith [sq_nonneg t]

/-! ## A sharper lower bound of `κ^[6] 0` -/

/-- `1 + t²/2 + 3t⁴/8 + 5t⁶/16 ≤ 1/√(1 − t²)` on `(−1, 1)`. -/
lemma inv_sqrt_ge_poly7 {t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16 ≤ 1 / Real.sqrt (1 - t ^ 2) := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
  have hq : 0 < 1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16 := by positivity
  have hss : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hpos.le
  have hid : (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16) ^ 2 * (1 - t ^ 2)
      = 1 - (35 / 64 * t ^ 8 + 14 / 64 * t ^ 10 + 35 / 256 * t ^ 12 + 25 / 256 * t ^ 14) := by
    ring
  have hnn : 0 ≤ 35 / 64 * t ^ 8 + 14 / 64 * t ^ 10 + 35 / 256 * t ^ 12 + 25 / 256 * t ^ 14 := by
    positivity
  have hsq : ((1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16) * Real.sqrt (1 - t ^ 2)) ^ 2
      ≤ 1 := by
    rw [mul_pow, hss, hid]; linarith
  have hle : (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16) * Real.sqrt (1 - t ^ 2) ≤ 1 := by
    have hm := mul_pos hq hs
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [le_div_iff₀ hs]
  exact hle

lemma hasDerivAt_polyA7 (t : ℝ) :
    HasDerivAt (fun t : ℝ => t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + 5 * t ^ 7 / 112)
      (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + 5 * t ^ 6 / 16) t := by
  have h := (((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 6)).add
    (((hasDerivAt_pow 5 t).const_mul 3).div_const 40)).add
    (((hasDerivAt_pow 7 t).const_mul 5).div_const 112)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `t + t³/6 + 3t⁵/40 + 5t⁷/112 ≤ arcsin t` on `[0, 1]`. -/
theorem arcsin_ge_poly7 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + 5 * t ^ 7 / 112 ≤ Real.arcsin t := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112))
      (1 / Real.sqrt (1 - x ^ 2) - (1 + x ^ 2 / 2 + 3 * x ^ 4 / 8 + 5 * x ^ 6 / 16)) x :=
    fun x hx =>
      (Real.hasDerivAt_arcsin (by linarith [hx.1]) hx.2.ne).sub (hasDerivAt_polyA7 x)
  have hmono : MonotoneOn
      (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112))
      (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := Real.continuous_arcsin
      exact (by fun_prop : Continuous (fun x : ℝ =>
        Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112))).continuousOn
    · rw [interior_Icc_01]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc_01]
      intro x hx
      rw [(hd x hx).deriv]
      have := inv_sqrt_ge_poly7 (t := x) (by linarith [hx.1]) hx.2
      linarith
  have h := hmono (left_mem_Icc.mpr zero_le_one) ⟨h0, h1⟩ h0
  simp only [Real.arcsin_zero] at h
  norm_num at h
  linarith

lemma hasDerivAt_polyK7 (t : ℝ) :
    HasDerivAt
      (fun t : ℝ => 1 / π + t / 2 + (t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 80 + 5 * t ^ 8 / 896) / π)
      (1 / 2 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + 5 * t ^ 7 / 112) / π) t := by
  have h := ((hasDerivAt_const t (1 / π)).add ((hasDerivAt_id' t).div_const 2)).add
    ((((((hasDerivAt_pow 2 t).div_const 2).add ((hasDerivAt_pow 4 t).div_const 24)).add
      ((hasDerivAt_pow 6 t).div_const 80)).add
      (((hasDerivAt_pow 8 t).const_mul 5).div_const 896)).div_const π)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- Polynomial lower bound of `κ` on `[0, 1]`, one more term than `kappa_ge_poly`. -/
theorem kappa_ge_poly7 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 / π + t / 2 + (t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 80 + 5 * t ^ 8 / 896) / π ≤ kappa t := by
  have hp := Real.pi_pos
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => kappa x
        - (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80 + 5 * x ^ 8 / 896) / π))
      ((π - Real.arccos x) / π
        - (1 / 2 + (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112) / π)) x := fun x hx =>
    (hasDerivAt_kappa (by linarith [hx.1]) hx.2).sub (hasDerivAt_polyK7 x)
  have hmono : MonotoneOn
      (fun x : ℝ => kappa x
        - (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80 + 5 * x ^ 8 / 896) / π))
      (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := continuous_kappa
      exact (by fun_prop : Continuous (fun x : ℝ => kappa x
        - (1 / π + x / 2 + (x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 80 + 5 * x ^ 8 / 896) / π))
        ).continuousOn
    · rw [interior_Icc_01]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc_01]
      intro x hx
      rw [(hd x hx).deriv, kappa_deriv_eq]
      have := div_le_div_of_nonneg_right (arcsin_ge_poly7 hx.1.le hx.2.le) hp.le
      linarith
  have h := hmono (left_mem_Icc.mpr zero_le_one) ⟨h0, h1⟩ h0
  simp only [kappa_zero] at h
  norm_num at h
  rw [one_div]
  linarith

/-- One step of the sharper rational lower bound: from `0 ≤ a ≤ s ≤ 1`, a lower bound of
`κ(s)`. -/
theorem kappa_ge_of_le7 {a s c : ℝ} (ha : 0 ≤ a) (has : a ≤ s) (hs : s ≤ 1)
    (hc : c ≤ (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896)) / 3.141593 + a / 2) :
    c ≤ kappa s := by
  have h1 := kappa_monotoneOn (a := a) (b := s) ⟨by linarith, has.trans hs⟩
    ⟨by linarith, hs⟩ has
  have h2 := kappa_ge_poly7 ha (has.trans hs)
  have hP : 0 ≤ 1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896) := by positivity
  have h3 := mul_le_mul_of_nonneg_left one_div_pi_gt.le hP
  have e1 : (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896)) * (1 / 3.141593)
      = (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896)) / 3.141593 := by ring
  have e2 : (1 + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896)) * (1 / π)
      = 1 / π + (a ^ 2 / 2 + a ^ 4 / 24 + a ^ 6 / 80 + 5 * a ^ 8 / 896) / π := by ring
  rw [e1, e2] at h3
  linarith

theorem kappa2_zero_ge' : 49373 / 100000 ≤ kappa (kappa 0) :=
  kappa_ge_of_le7 (a := 318309 / 1000000) (by norm_num) kappa_zero_ge
    (by linarith [kappa_zero_le]) (by norm_num)

theorem kappa3_zero_ge' : 604823 / 1000000 ≤ kappa (kappa (kappa 0)) :=
  kappa_ge_of_le7 (a := 49373 / 100000) (by norm_num) kappa2_zero_ge'
    (by linarith [kappa2_zero_le]) (by norm_num)

theorem kappa4_zero_ge' : 680943 / 1000000 ≤ kappa (kappa (kappa (kappa 0))) :=
  kappa_ge_of_le7 (a := 604823 / 1000000) (by norm_num) kappa3_zero_ge'
    kappa3_zero_le_one (by norm_num)

theorem kappa5_zero_ge' : 735909 / 1000000 ≤ kappa (kappa (kappa (kappa (kappa 0)))) :=
  kappa_ge_of_le7 (a := 680943 / 1000000) (by norm_num) kappa4_zero_ge'
    kappa4_zero_le_one (by norm_num)

/-- A sharper lower bound of `κ^[6] 0`. -/
theorem kappa6_zero_ge' : 7771 / 10000 ≤ kappa^[6] 0 := by
  have h : kappa^[6] 0 = kappa (kappa (kappa (kappa (kappa (kappa 0))))) := rfl
  rw [h]
  exact kappa_ge_of_le7 (a := 735909 / 1000000) (by norm_num) kappa5_zero_ge'
    kappa5_zero_le_one (by norm_num)

end BstLean.Part132

open BstLean.Part132 in
#print axioms kappa_le_quad
open BstLean.Part132 in
#print axioms kappa_ge_lin
open BstLean.Part132 in
#print axioms kappa_le_quad_at
open BstLean.Part132 in
#print axioms kk_quad
open BstLean.Part132 in
#print axioms arcsin_ge_poly7
open BstLean.Part132 in
#print axioms kappa_ge_poly7
open BstLean.Part132 in
#print axioms kappa6_zero_ge'
