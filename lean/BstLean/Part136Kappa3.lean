import BstLean.Part132Quad

/-!
# Part 136: a cubic bound of `κ∘κ` around `0`

* `kappa_neg`: `κ(−t) = κ(t) − t`.
* `arcsin_sub_le`: `arcsin x ≤ x + (9/10)x²` on `[0, 1]`.
* `kappa_taylor0`: `0 ≤ κ(t) − κ(0) − t/2 − κ(0)t²/2 ≤ (3/10)κ(0)|t|³` on `[−1, 1]`
  (`κ(0) = 1/π`).
* `rho_nonneg`, `rho_le`: `0 ≤ ρ(x) ≤ 6(x − u)²` on `[0, 1]`,
  `ρ(x) = arcsin x − arcsin u − (x − u)/√(1 − u²)`, `u = κ(0)`.
* `kappa_taylor_u`: `|κ(s) − κ(u) − β(s − u) − (c·u/2)(s − u)²| ≤ 2u|s − u|³` on `[0, 1]`.
* `kk_three`: `|κ(κ(t)) − κ(κ(0)) − b·t − (138/1000)t²| ≤ (1/1000)t² + (2/5)|t|³` on `[−1, 1]`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part136

open Real Set BstLean.Part130 BstLean.Part132

lemma kappa_neg (t : ℝ) : kappa (-t) = kappa t - t := by
  have hp := Real.pi_pos
  unfold kappa
  rw [neg_sq, Real.arccos_neg]
  field_simp
  ring

/-- `κ′(x) = 1/2 + κ(0)·arcsin x`. -/
lemma kd (x : ℝ) : (π - Real.arccos x) / π = 1 / 2 + kappa 0 * Real.arcsin x := by
  rw [kappa_deriv_eq, kappa_zero]
  ring

lemma arcsin_sub_le {x : ℝ} (h0 : 0 ≤ x) (_h1 : x ≤ 1) :
    Real.arcsin x ≤ x + 9 / 10 * x ^ 2 := by
  rcases le_total x (9 / 10) with h9 | h9
  · have h := ge_of_deriv_sign
      (f := fun x : ℝ => (0 + 1 * (x - 0) + 9 / 10 * (x - 0) ^ 2) - Real.arcsin x)
      (f' := fun x : ℝ => (1 + 2 * (9 / 10) * (x - 0)) - 1 / Real.sqrt (1 - x ^ 2))
      (a := 0) (b := 9 / 10) (c := 0)
      (by have := Real.continuous_arcsin; fun_prop)
      (fun x hx => (hasDerivAt_quadQ _ _ _ _ x).sub
        (Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])))
      (le_refl _) (by norm_num)
      (by
        intro x hx
        have hx0 := hx.1.le
        have hx9 := hx.2.le
        have hy : (0 : ℝ) < 1 + 9 / 5 * x := by linarith
        have hpx : 0 < 1 - x ^ 2 := by nlinarith
        have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hpx
        have p : 0 ≤ 36 / 10 + 224 / 100 * x - 36 / 10 * x ^ 2 - 324 / 100 * x ^ 3 := by
          nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx9),
            mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx9)]
        have hle : 1 / (1 + 9 / 5 * x) ≤ Real.sqrt (1 - x ^ 2) := by
          rw [Real.le_sqrt' (by positivity), div_pow, one_pow, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hx0 p]
        have h2 : 1 ≤ (1 + 9 / 5 * x) * Real.sqrt (1 - x ^ 2) := by
          have := mul_le_mul_of_nonneg_left hle hy.le
          rwa [mul_one_div_cancel hy.ne'] at this
        have h3 : 1 / Real.sqrt (1 - x ^ 2) ≤ 1 + 9 / 5 * x := by
          rw [div_le_iff₀ hs]; linarith
        linarith)
      (fun x hx => (lt_irrefl _ (hx.1.trans hx.2)).elim)
      x ⟨h0, h9⟩
    beta_reduce at h
    have e : (0 : ℝ) + 1 * (0 - 0) + 9 / 10 * (0 - 0) ^ 2 - Real.arcsin 0 = 0 := by
      rw [Real.arcsin_zero]; ring
    rw [e] at h
    linarith
  · have h := Real.arcsin_le_pi_div_two x
    have hp := Real.pi_lt_d6
    norm_num at hp
    nlinarith

lemma le_arcsin' {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ Real.arcsin x := by
  have h := arcsin_ge_poly h0 h1
  have : 0 ≤ x ^ 3 / 6 + 3 * x ^ 5 / 40 := by positivity
  linarith

lemma kappa_taylor0_pos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ kappa t - kappa 0 - t / 2 - kappa 0 * t ^ 2 / 2 ∧
    kappa t - kappa 0 - t / 2 - kappa 0 * t ^ 2 / 2 ≤ 3 / 10 * kappa 0 * t ^ 3 := by
  have hu0 : 0 ≤ kappa 0 := by linarith [kappa_zero_ge]
  constructor
  · have h := ge_of_deriv_sign
      (f := fun x : ℝ => kappa x - (kappa 0 + 1 / 2 * (x - 0) + kappa 0 / 2 * (x - 0) ^ 2))
      (f' := fun x : ℝ => (π - Real.arccos x) / π - (1 / 2 + 2 * (kappa 0 / 2) * (x - 0)))
      (a := 0) (b := 1) (c := 0)
      (by have := continuous_kappa; fun_prop)
      (fun x hx => (hasDerivAt_kappa (by linarith [hx.1]) hx.2).sub (hasDerivAt_quadQ _ _ _ _ x))
      (le_refl _) (by norm_num)
      (by
        intro x hx
        rw [kd]
        have := le_arcsin' hx.1.le hx.2.le
        nlinarith [mul_nonneg hu0 (sub_nonneg.mpr this)])
      (fun x hx => (lt_irrefl _ (hx.1.trans hx.2)).elim)
      t ⟨h0, h1⟩
    beta_reduce at h
    have e : kappa 0 - (kappa 0 + 1 / 2 * (0 - 0) + kappa 0 / 2 * (0 - 0) ^ 2) = 0 := by ring
    rw [e] at h
    have e2 : kappa 0 / 2 * (t - 0) ^ 2 = kappa 0 * t ^ 2 / 2 := by ring
    rw [e2] at h
    linarith
  · have hc : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 3 / 10 * kappa 0 * x ^ 3)
        (3 * (3 / 10 * kappa 0) * x ^ 2) x := by
      intro x
      have := (hasDerivAt_pow 3 x).const_mul (3 / 10 * kappa 0)
      refine this.congr_deriv ?_
      norm_num
      ring
    have h := ge_of_deriv_sign
      (f := fun x : ℝ => ((kappa 0 + 1 / 2 * (x - 0) + kappa 0 / 2 * (x - 0) ^ 2) +
        3 / 10 * kappa 0 * x ^ 3) - kappa x)
      (f' := fun x : ℝ => ((1 / 2 + 2 * (kappa 0 / 2) * (x - 0)) +
        3 * (3 / 10 * kappa 0) * x ^ 2) - (π - Real.arccos x) / π)
      (a := 0) (b := 1) (c := 0)
      (by have := continuous_kappa; fun_prop)
      (fun x hx => ((hasDerivAt_quadQ _ _ _ _ x).add (hc x)).sub
        (hasDerivAt_kappa (by linarith [hx.1]) hx.2))
      (le_refl _) (by norm_num)
      (by
        intro x hx
        rw [kd]
        have := arcsin_sub_le hx.1.le hx.2.le
        nlinarith [mul_nonneg hu0 (sub_nonneg.mpr this)])
      (fun x hx => (lt_irrefl _ (hx.1.trans hx.2)).elim)
      t ⟨h0, h1⟩
    beta_reduce at h
    have e : kappa 0 + 1 / 2 * (0 - 0) + kappa 0 / 2 * (0 - 0) ^ 2 +
        3 / 10 * kappa 0 * 0 ^ 3 - kappa 0 = 0 := by ring
    rw [e] at h
    have e2 : kappa 0 / 2 * (t - 0) ^ 2 = kappa 0 * t ^ 2 / 2 := by ring
    rw [e2] at h
    linarith

lemma kappa_taylor0 {t : ℝ} (h0 : -1 ≤ t) (h1 : t ≤ 1) :
    0 ≤ kappa t - kappa 0 - t / 2 - kappa 0 * t ^ 2 / 2 ∧
    kappa t - kappa 0 - t / 2 - kappa 0 * t ^ 2 / 2 ≤ 3 / 10 * kappa 0 * |t| ^ 3 := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact kappa_taylor0_pos h h1
  · rw [abs_of_nonpos h]
    have e : kappa (-t) - kappa 0 - -t / 2 - kappa 0 * (-t) ^ 2 / 2 =
        kappa t - kappa 0 - t / 2 - kappa 0 * t ^ 2 / 2 := by
      rw [kappa_neg]; ring
    have this2 := kappa_taylor0_pos (t := -t) (by linarith) (by linarith)
    rw [e] at this2
    exact this2

/-! ## `arcsin` at `u = κ(0)` to second order -/

lemma inv_sqrt_lip {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3 / 4) :
    1 / Real.sqrt (1 - y ^ 2) - 1 / Real.sqrt (1 - x ^ 2) ≤ 12 * (y - x) := by
  have hpx : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hpy : 0 ≤ 1 - y ^ 2 := by nlinarith
  have ha2 := Real.sq_sqrt hpx
  have hb2 := Real.sq_sqrt hpy
  have ha : (66 : ℝ) / 100 ≤ Real.sqrt (1 - x ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  have hb : (66 : ℝ) / 100 ≤ Real.sqrt (1 - y ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  have hab : Real.sqrt (1 - y ^ 2) ≤ Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  obtain ⟨a, haE⟩ : ∃ a : ℝ, a = Real.sqrt (1 - x ^ 2) := ⟨_, rfl⟩
  obtain ⟨b, hbE⟩ : ∃ b : ℝ, b = Real.sqrt (1 - y ^ 2) := ⟨_, rfl⟩
  rw [← haE] at ha ha2 hab
  rw [← hbE] at hb hb2 hab
  rw [← haE, ← hbE]
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have e : 1 / b - 1 / a = (a - b) / (a * b) := by field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h1 : (a - b) * (a + b) = (y - x) * (y + x) := by nlinarith
  have h2 : a - b ≤ 12 / 10 * (y - x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (by linarith : (0 : ℝ) ≤ a + b - 132 / 100),
      mul_nonneg (sub_nonneg.mpr hxy) (by linarith : (0 : ℝ) ≤ 15 / 10 - y - x)]
  have h3 : (4356 : ℝ) / 10000 ≤ a * b := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr h3)]

lemma inv_sqrt_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    1 / Real.sqrt (1 - x ^ 2) ≤ 1 / Real.sqrt (1 - y ^ 2) := by
  have hpy : 0 < 1 - y ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpy) (Real.sqrt_le_sqrt (by nlinarith))

lemma cinv_bounds : (10548 : ℝ) / 10000 ≤ 1 / Real.sqrt (1 - kappa 0 ^ 2) ∧
    1 / Real.sqrt (1 - kappa 0 ^ 2) ≤ 1055 / 1000 := by
  have hu0 := kappa_zero_ge
  have hu1 := kappa_zero_le
  have hlo : (9479 : ℝ) / 10000 ≤ Real.sqrt (1 - kappa 0 ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  have hhi : Real.sqrt (1 - kappa 0 ^ 2) ≤ 948 / 1000 := by
    rw [Real.sqrt_le_iff]; constructor
    · norm_num
    · nlinarith
  have hpos : 0 < Real.sqrt (1 - kappa 0 ^ 2) := by linarith
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

lemma rho_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ Real.arcsin x - Real.arcsin (kappa 0) -
      (x - kappa 0) * (1 / Real.sqrt (1 - kappa 0 ^ 2)) := by
  have hu0 := kappa_zero_ge
  have hu1 := kappa_zero_le
  have h := ge_of_deriv_sign
    (f := fun x : ℝ => Real.arcsin x - (Real.arcsin (kappa 0) +
      1 / Real.sqrt (1 - kappa 0 ^ 2) * (x - kappa 0) + 0 * (x - kappa 0) ^ 2))
    (f' := fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2) -
      (1 / Real.sqrt (1 - kappa 0 ^ 2) + 2 * 0 * (x - kappa 0)))
    (a := 0) (b := 1) (c := kappa 0)
    (by have := Real.continuous_arcsin; fun_prop)
    (fun x hx => (Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])).sub
      (hasDerivAt_quadQ _ _ _ _ x))
    (by linarith) (by linarith)
    (by
      intro x hx
      have := inv_sqrt_mono (by linarith : (0 : ℝ) ≤ kappa 0) hx.1.le hx.2
      linarith)
    (by
      intro x hx
      have := inv_sqrt_mono hx.1.le hx.2.le (by linarith : kappa 0 < 1)
      linarith)
    x ⟨h0, h1⟩
  beta_reduce at h
  have e : Real.arcsin (kappa 0) - (Real.arcsin (kappa 0) +
      1 / Real.sqrt (1 - kappa 0 ^ 2) * (kappa 0 - kappa 0) + 0 * (kappa 0 - kappa 0) ^ 2) = 0 := by
    ring
  rw [e] at h
  linarith

lemma rho_le {x : ℝ} (h0 : 0 ≤ x) (_h1 : x ≤ 1) :
    Real.arcsin x - Real.arcsin (kappa 0) -
      (x - kappa 0) * (1 / Real.sqrt (1 - kappa 0 ^ 2)) ≤ 6 * (x - kappa 0) ^ 2 := by
  have hu0 := kappa_zero_ge
  have hu1 := kappa_zero_le
  obtain ⟨hc0, hc1⟩ := cinv_bounds
  rcases le_total x (3 / 4) with h34 | h34
  · have h := ge_of_deriv_sign
      (f := fun x : ℝ => (Real.arcsin (kappa 0) +
        1 / Real.sqrt (1 - kappa 0 ^ 2) * (x - kappa 0) + 6 * (x - kappa 0) ^ 2) - Real.arcsin x)
      (f' := fun x : ℝ => (1 / Real.sqrt (1 - kappa 0 ^ 2) + 2 * 6 * (x - kappa 0)) -
        1 / Real.sqrt (1 - x ^ 2))
      (a := 0) (b := 3 / 4) (c := kappa 0)
      (by have := Real.continuous_arcsin; fun_prop)
      (fun x hx => (hasDerivAt_quadQ _ _ _ _ x).sub
        (Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])))
      (by linarith) (by linarith)
      (by
        intro x hx
        have := inv_sqrt_lip (by linarith : (0 : ℝ) ≤ kappa 0) hx.1.le hx.2.le
        linarith)
      (by
        intro x hx
        have := inv_sqrt_lip hx.1.le hx.2.le (by linarith : kappa 0 ≤ 3 / 4)
        linarith)
      x ⟨h0, h34⟩
    beta_reduce at h
    have e : Real.arcsin (kappa 0) + 1 / Real.sqrt (1 - kappa 0 ^ 2) * (kappa 0 - kappa 0) +
        6 * (kappa 0 - kappa 0) ^ 2 - Real.arcsin (kappa 0) = 0 := by ring
    rw [e] at h
    linarith
  · have ha := Real.arcsin_le_pi_div_two x
    have hp := Real.pi_lt_d6
    norm_num at hp
    have hau := arcsin_kappa_zero_ge
    have hm : (3 / 4 - kappa 0) * (10548 / 10000) ≤
        (x - kappa 0) * (1 / Real.sqrt (1 - kappa 0 ^ 2)) :=
      mul_le_mul (by linarith) hc0 (by norm_num) (by linarith)
    have hsq : (43169 / 100000 : ℝ) ^ 2 ≤ (x - kappa 0) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    nlinarith

/-- A function with `g u = 0` and `|g′| ≤ 3K(x − u)²` has `|g| ≤ K|s − u|³`. -/
lemma cubic_bound {g g' : ℝ → ℝ} {u K : ℝ} (hg : Continuous g)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' x) x) (hu : u ∈ Icc (0 : ℝ) 1) (hg0 : g u = 0)
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |g' x| ≤ 3 * K * (x - u) ^ 2) :
    ∀ s ∈ Icc (0 : ℝ) 1, |g s| ≤ K * |s - u| ^ 3 := by
  have hcube : ∀ x : ℝ, HasDerivAt (fun x : ℝ => K * (x - u) ^ 3) (3 * K * (x - u) ^ 2) x := by
    intro x
    have := (((hasDerivAt_id' x).sub_const u).pow 3).const_mul K
    refine this.congr_deriv ?_
    norm_num
    ring
  have hF : MonotoneOn (fun x : ℝ => K * (x - u) ^ 3 - g x) (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => ((hcube x).sub (hd x hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hdF : HasDerivAt (fun x : ℝ => K * (x - u) ^ 3 - g x)
          (3 * K * (x - u) ^ 2 - g' x) x := (hcube x).sub (hd x hx)
      rw [hdF.deriv]
      linarith [(abs_le.mp (hb x hx)).2]
  have hG : MonotoneOn (fun x : ℝ => K * (x - u) ^ 3 + g x) (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => ((hcube x).add (hd x hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hdG : HasDerivAt (fun x : ℝ => K * (x - u) ^ 3 + g x)
          (3 * K * (x - u) ^ 2 + g' x) x := (hcube x).add (hd x hx)
      rw [hdG.deriv]
      linarith [(abs_le.mp (hb x hx)).1]
  have e0 : K * (u - u) ^ 3 = 0 := by ring
  intro s hs
  rcases le_total u s with h | h
  · have h1 : K * (u - u) ^ 3 - g u ≤ K * (s - u) ^ 3 - g s := hF hu hs h
    have h2 : K * (u - u) ^ 3 + g u ≤ K * (s - u) ^ 3 + g s := hG hu hs h
    rw [e0, hg0] at h1 h2
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_le]
    constructor <;> linarith
  · have h1 : K * (s - u) ^ 3 - g s ≤ K * (u - u) ^ 3 - g u := hF hs hu h
    have h2 : K * (s - u) ^ 3 + g s ≤ K * (u - u) ^ 3 + g u := hG hs hu h
    rw [e0, hg0] at h1 h2
    have e : |s - u| ^ 3 = -(s - u) ^ 3 := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [e, abs_le]
    constructor <;> linarith

lemma kappa_taylor_u {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |kappa s - (kappa (kappa 0) + (π - Real.arccos (kappa 0)) / π * (s - kappa 0) +
      1 / Real.sqrt (1 - kappa 0 ^ 2) * kappa 0 / 2 * (s - kappa 0) ^ 2)| ≤
      2 * kappa 0 * |s - kappa 0| ^ 3 := by
  have hu0 := kappa_zero_ge
  have hu1 := kappa_zero_le
  have hup : 0 ≤ kappa 0 := by linarith
  refine cubic_bound
    (g := fun x : ℝ => kappa x - (kappa (kappa 0) + (π - Real.arccos (kappa 0)) / π *
      (x - kappa 0) + 1 / Real.sqrt (1 - kappa 0 ^ 2) * kappa 0 / 2 * (x - kappa 0) ^ 2))
    (g' := fun x : ℝ => (π - Real.arccos x) / π - ((π - Real.arccos (kappa 0)) / π +
      2 * (1 / Real.sqrt (1 - kappa 0 ^ 2) * kappa 0 / 2) * (x - kappa 0)))
    (u := kappa 0) (K := 2 * kappa 0)
    (by have := continuous_kappa; fun_prop)
    (fun x hx => (hasDerivAt_kappa (by linarith [hx.1]) hx.2).sub (hasDerivAt_quadQ _ _ _ _ x))
    ⟨by linarith, by linarith⟩ (by ring) ?_ s ⟨h0, h1⟩
  intro x hx
  have e : (π - Real.arccos x) / π - ((π - Real.arccos (kappa 0)) / π +
      2 * (1 / Real.sqrt (1 - kappa 0 ^ 2) * kappa 0 / 2) * (x - kappa 0)) =
      kappa 0 * (Real.arcsin x - Real.arcsin (kappa 0) -
        (x - kappa 0) * (1 / Real.sqrt (1 - kappa 0 ^ 2))) := by
    rw [kd x, kd (kappa 0)]; ring
  rw [e, abs_mul, abs_of_nonneg hup,
    abs_of_nonneg (rho_nonneg hx.1.le hx.2.le)]
  have := mul_le_mul_of_nonneg_left (rho_le hx.1.le hx.2.le) hup
  linarith

/-! ## The cubic bound of `κ∘κ` -/

theorem kk_three : ∃ b : ℝ, 0 ≤ b ∧ b ≤ 3017 / 10000 ∧ ∀ t ∈ Icc (-1 : ℝ) 1,
    |kappa (kappa t) - kappa (kappa 0) - b * t - 138 / 1000 * t ^ 2| ≤
      1 / 1000 * t ^ 2 + 2 / 5 * |t| ^ 3 := by
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (π - Real.arccos (kappa 0)) / π := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := hβ ▸ kappa_beta_bounds.1
  have hβ1 : β ≤ 6034 / 10000 := hβ ▸ kappa_beta_bounds.2
  have hu0 := kappa_zero_ge
  have hu1 := kappa_zero_le
  have hβlo : (6031 : ℝ) / 10000 ≤ β := by
    rw [hβ, kd]
    have := arcsin_kappa_zero_ge
    nlinarith [mul_le_mul hu0 this (by norm_num) (by linarith : (0 : ℝ) ≤ kappa 0)]
  obtain ⟨hc0, hc1⟩ := cinv_bounds
  refine ⟨β / 2, by linarith, by linarith, fun t ht => ?_⟩
  have hs := kappa_mem ht.1 ht.2
  have hU := kappa_le_quad ht.1 ht.2
  have hL := kappa_ge_lin ht.1 ht.2
  have hT0 := kappa_taylor0 ht.1 ht.2
  have hTu := kappa_taylor_u hs.1 hs.2
  rw [← hβ] at hTu
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = kappa 0 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = kappa (kappa 0) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / Real.sqrt (1 - kappa 0 ^ 2) := ⟨_, rfl⟩
  rw [← hc] at hc0 hc1 hTu
  rw [← hq]
  rw [← hq] at hTu
  rw [← hu] at hu0 hu1 hU hL hT0 hTu
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = kappa t - u := ⟨_, rfl⟩
  rw [← hδ] at hT0 hTu
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = |t| := ⟨_, rfl⟩
  rw [← hr] at hT0
  rw [← hr]
  have hr0 : 0 ≤ r := hr ▸ abs_nonneg t
  have hr1 : r ≤ 1 := hr ▸ abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have ht2 : t ^ 2 = r ^ 2 := by rw [hr, sq_abs]
  have htr : t ≤ r := hr ▸ le_abs_self t
  have htr' : -r ≤ t := hr ▸ neg_abs_le t
  have hr2 : r ^ 3 ≤ r ^ 2 := by nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr1)]
  have hr3 : 0 ≤ r ^ 3 := by positivity
  -- `δ` and `δ + t/2`
  have hδ1 : t / 2 ≤ δ := by linarith
  have hδ2 : δ ≤ t / 2 + r ^ 2 / 4 := by linarith
  have hrr : r ^ 2 ≤ r := by nlinarith
  have hδa : |δ| ≤ 3 / 4 * r := by rw [abs_le]; constructor <;> linarith
  have hδp : |δ + t / 2| ≤ 5 / 4 * r := by rw [abs_le]; constructor <;> linarith
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, R1 = δ - t / 2 - u * t ^ 2 / 2 := ⟨_, rfl⟩
  rw [← hR1] at hT0
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, R2 = kappa (kappa t) - (q + β * δ + c * u / 2 * δ ^ 2) := ⟨_, rfl⟩
  rw [← hR2] at hTu
  have key : kappa (kappa t) - q - β / 2 * t - 138 / 1000 * t ^ 2 =
      (β * u / 2 + c * u / 8 - 138 / 1000) * t ^ 2 + β * R1 +
        c * u / 2 * (R1 + u * t ^ 2 / 2) * (δ + t / 2) + R2 := by
    rw [hR1, hR2]; ring
  rw [key]
  have hup : 0 ≤ u := by linarith
  -- numbers
  have n1 : (6031 : ℝ) / 10000 * (318309 / 1000000) ≤ β * u :=
    mul_le_mul hβlo hu0 (by norm_num) (by linarith)
  have n2 : β * u ≤ 6034 / 10000 * (31831 / 100000) :=
    mul_le_mul hβ1 hu1 hup (by norm_num)
  have n3 : (10548 : ℝ) / 10000 * (318309 / 1000000) ≤ c * u :=
    mul_le_mul hc0 hu0 (by norm_num) (by linarith)
  have n4 : c * u ≤ 1055 / 1000 * (31831 / 100000) :=
    mul_le_mul hc1 hu1 hup (by norm_num)
  -- the four terms
  have B1 : |(β * u / 2 + c * u / 8 - 138 / 1000) * t ^ 2| ≤ 1 / 1000 * t ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg t)
    rw [abs_le]; constructor <;> linarith
  have hR1' : R1 ≤ 955 / 10000 * r ^ 3 := by
    have := mul_le_mul_of_nonneg_right hu1 hr3
    linarith [hT0.2]
  have B2 : |β * R1| ≤ 577 / 10000 * r ^ 3 := by
    rw [abs_of_nonneg (mul_nonneg hβ0 hT0.1)]
    have := mul_le_mul hβ1 hR1' hT0.1 (by norm_num)
    linarith
  have hE0 : 0 ≤ R1 + u * t ^ 2 / 2 := by
    have : 0 ≤ u * t ^ 2 / 2 := by positivity
    linarith [hT0.1]
  have hE1 : R1 + u * t ^ 2 / 2 ≤ 2547 / 10000 * r ^ 2 := by
    rw [ht2]
    have := mul_le_mul_of_nonneg_right hu1 (sq_nonneg r)
    linarith
  have hγ0 : 0 ≤ c * u / 2 := by linarith
  have hγ1 : c * u / 2 ≤ 168 / 1000 := by linarith
  have B3 : |c * u / 2 * (R1 + u * t ^ 2 / 2) * (δ + t / 2)| ≤ 535 / 10000 * r ^ 3 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hγ0 hE0)]
    have h1 : c * u / 2 * (R1 + u * t ^ 2 / 2) ≤ 168 / 1000 * (2547 / 10000 * r ^ 2) :=
      mul_le_mul hγ1 hE1 hE0 (by norm_num)
    have h2 := mul_le_mul h1 hδp (abs_nonneg _) (by positivity)
    have e : 168 / 1000 * (2547 / 10000 * r ^ 2) * (5 / 4 * r) =
        168 / 1000 * (2547 / 10000) * (5 / 4) * r ^ 3 := by ring
    rw [e] at h2
    linarith
  have B4 : |R2| ≤ 2686 / 10000 * r ^ 3 := by
    have h1 : |δ| ^ 3 ≤ (3 / 4 * r) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hδa 3
    have h2 : 2 * u * |δ| ^ 3 ≤ 2 * (31831 / 100000) * (3 / 4 * r) ^ 3 :=
      mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
    have e : 2 * (31831 / 100000 : ℝ) * (3 / 4 * r) ^ 3 =
        2 * (31831 / 100000) * (27 / 64) * r ^ 3 := by ring
    rw [e] at h2
    linarith
  have tri := (abs_add_le ((β * u / 2 + c * u / 8 - 138 / 1000) * t ^ 2 + β * R1 +
    c * u / 2 * (R1 + u * t ^ 2 / 2) * (δ + t / 2)) R2).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  linarith

end BstLean.Part136

