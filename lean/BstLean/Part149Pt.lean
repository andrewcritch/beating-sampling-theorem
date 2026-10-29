import BstLean.Part149Defs

/-!
# Part 149: the stage of the Agent network at the stand-in inputs, pointwise in the hidden weights

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md` (the `A`-stage error for FIXED hidden weights
`θ = (A₁, A₂)`). The hidden map is `h = hA c τ θ` on `(ℝⁿ, stdGauss)`; `v = 2/m`; `d = m/n`;
`b = bbar c τ θ`. The hypotheses bound the two kernel errors in units of `d`:
`errKc (d·au) c τ θ ≤ (d·Δ)²` and `errDc c τ θ ≤ (d·δ)²`.

* `stagePt`: `frameA` and `scalarsA` (Part149Frame) with the raw values `d·au`, `d·Δ`, `d`, `d·δ`,
  `d·ε₁`, `d·ε₂`, `d·su`, then `stageA` (Part149Stage) with `τ := tauOut c τ θ`; the right side is
  bounded with constants that are monotone in `Δ ≤ Δmax`, `δ ≤ δmax`, `alo ≤ au ≤ ahi`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)

/-- `d·x/√(d·y) = √d·(x/√y)`. -/
private lemma div_sqrt_scale {d x y : ℝ} (hd : 0 < d) (hy : 0 < y) :
    d * x / √(d * y) = √d * (x / √y) := by
  have hsd : 0 < √d := Real.sqrt_pos.2 hd
  have hsy : 0 < √y := Real.sqrt_pos.2 hy
  rw [Real.sqrt_mul hd.le, div_eq_iff (by positivity)]
  have h1 := Real.mul_self_sqrt hd.le
  have h2 : x / √y * √y = x := div_mul_cancel₀ _ hsy.ne'
  linear_combination (-d) * h2 - (x / √y * √y) * h1

/-- If `1 ≤ r²·x` then `t/√x ≤ r·t` for `t ≥ 0`. -/
private lemma div_sqrt_le {r x t : ℝ} (hr : 0 < r) (hx : 0 < x) (h : 1 ≤ r ^ 2 * x)
    (ht : 0 ≤ t) : t / √x ≤ r * t := by
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have h1 : (1 : ℝ) ^ 2 ≤ (r * √x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx.le]; simpa using h
  have h2 : 1 ≤ r * √x := (le_abs_self 1).trans (abs_le_of_sq_le_sq h1 (by positivity))
  rw [div_le_iff₀ hsx]
  have := mul_le_mul_of_nonneg_left h2 ht
  linarith

/-- **The stage of the Agent network at the stand-in inputs, for fixed hidden weights.** -/
theorem stagePt {n m mF : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmF : 1 ≤ mF) (c : Fin n → ℝ) (τ : ℝ)
    (θ : HidParam n m)
    {au alo ahi Δmax δmax ε₁ ε₂ su r₁ r₂ η : ℝ} (halo : alo ≤ au) (hahi : au ≤ ahi)
    (hΔmax : 0 ≤ Δmax) (hδmax : 0 ≤ δmax) (hA1 : Δmax < alo) (hA2 : ahi + Δmax < 1)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hsu : 0 < su)
    (hsle : su ≤ 1 - ε₁ - (ahi + ε₂) ^ 2 / (alo - Δmax))
    (hr₁ : 0 < r₁) (hr₁' : 1 ≤ r₁ ^ 2 * (alo - Δmax))
    (hr₂ : 0 < r₂) (hr₂' : 1 ≤ r₂ ^ 2 * (1 - ahi - Δmax)) (hη : 0 < η)
    {Δ δ : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ Δmax) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δmax)
    (hK : errKc ((m : ℝ) / n * au) c τ θ ≤ ((m : ℝ) / n * Δ) ^ 2)
    (hD : errDc c τ θ ≤ ((m : ℝ) / n * δ) ^ 2) :
    ∫⁻ p, ENNReal.ofReal ((gT (stdGauss (Fin n)) (hA c τ θ) p -
        gO (bbar c τ θ) (tauOut c τ θ) p) ^ 2)
        ∂((gaussMat n m (2 / (m : ℝ))).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal (2 / (n : ℝ) * ((1 + η) * (2 * (Δ / su + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) *
          (1 - alo + δmax + Δmax)) +
        (1 + 1 / η) * (2 * (r₁ ^ 2 * Δ ^ 2 + (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (m : ℝ) / n := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hV0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hN0 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have hvd : 2 / (m : ℝ) * d = 2 / (n : ℝ) := by rw [hd]; field_simp
  have h1 : 0 < au - Δ := by linarith
  have h2 : 0 < 1 - au - Δ := by linarith
  have h3 : 0 < alo - Δmax := by linarith
  have hr1'' : 1 ≤ r₁ ^ 2 * (au - Δ) :=
    hr₁'.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))
  have hr2'' : 1 ≤ r₂ ^ 2 * (1 - au - Δ) :=
    hr₂'.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))
  have hh := bm_hA hn c τ θ
  have hKr : ∫ p, (∑ k, hA c τ θ p.1 k * hA c τ θ p.2 k - d * au) ^ 2
      ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) ≤ (d * Δ) ^ 2 := by
    rw [hd]; exact hK
  have hDr : ∫ γ, (normSq (hA c τ θ γ) - d) ^ 2 ∂stdGauss (Fin n) ≤ (d * δ) ^ 2 := by
    rw [hd]; exact hD
  have hΔa : d * Δ < d * au := mul_lt_mul_of_pos_left (by linarith) hd0
  have hda : d * au + d * Δ < d := by
    have := mul_pos hd0 h2
    linarith
  -- the raw form of `hsle`
  have hsr : d * su ≤ d - d * ε₁ - (d * au + d * ε₂) ^ 2 / (d * au - d * Δ) := by
    have e : (d * au + d * ε₂) ^ 2 / (d * au - d * Δ) = d * ((au + ε₂) ^ 2 / (au - Δ)) := by
      rw [show d * au - d * Δ = d * (au - Δ) by ring,
        show d * au + d * ε₂ = d * (au + ε₂) by ring]
      field_simp
    have k : (au + ε₂) ^ 2 / (au - Δ) ≤ (ahi + ε₂) ^ 2 / (alo - Δmax) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2) h3
        (by linarith)
    have k2 : su ≤ 1 - ε₁ - (au + ε₂) ^ 2 / (au - Δ) := by linarith
    rw [e]
    have := mul_le_mul_of_nonneg_left k2 hd0.le
    linarith
  have fr := frameA (stdGauss (Fin n)) hh (a := d * au) (Δ := d * Δ) (d := d) (δ := d * δ)
    (ε₁ := d * ε₁) (ε₂ := d * ε₂) (s := d * su) (by positivity) (by positivity) (by positivity)
    hΔa hKr hDr (by positivity) hsr
  have sc := scalarsA (stdGauss (Fin n)) hh (a := d * au) (Δ := d * Δ) (d := d) (δ := d * δ)
    (by positivity) (by positivity) hΔa hda hKr hDr
  rw [show hbar (stdGauss (Fin n)) (hA c τ θ) = bbar c τ θ from rfl] at fr sc
  obtain ⟨hb, hLr⟩ := fr
  obtain ⟨hY, hYl, hR, hSS⟩ := sc
  have eL : d * Δ / (d * su) + (d * Δ) ^ 2 / (d * ε₂) ^ 2 + (d * δ) ^ 2 / (d * ε₁) ^ 2 =
      Δ / su + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2 := by
    simp only [mul_pow]
    rw [mul_div_mul_left _ _ hd0.ne', mul_div_mul_left _ _ (pow_ne_zero 2 hd0.ne'),
      mul_div_mul_left _ _ (pow_ne_zero 2 hd0.ne')]
  rw [eL] at hLr
  have hYge : d * au - d * Δ ≤ normSq (bbar c τ θ) := by linarith [(abs_le.mp hY).1]
  have hYle : normSq (bbar c τ θ) ≤ d * au + d * Δ := by linarith [(abs_le.mp hY).2]
  have hYd : 0 < d - normSq (bbar c τ θ) := by linarith
  -- the constant scalar
  have htau : tauOut c τ θ = √(2 / (m : ℝ)) * √(d - normSq (bbar c τ θ)) := by
    have e : 2 / (n : ℝ) - 2 / (m : ℝ) * normSq (bbar c τ θ) =
        2 / (m : ℝ) * (d - normSq (bbar c τ θ)) := by rw [← hvd]; ring
    rw [tauOut, e, max_eq_right (mul_nonneg hV0 hYd.le), Real.sqrt_mul hV0]
  have hS : ∫ u, (sig (2 / (m : ℝ)) (bbar c τ θ) (hA c τ θ u) - tauOut c τ θ) ^ 2
      ∂stdGauss (Fin n) ≤ 2 / (m : ℝ) *
        (d * Δ / √(d * au - d * Δ) + (d * δ + 2 * (d * Δ)) / √(d - d * au - d * Δ)) ^ 2 := by
    have e : (fun u => (sig (2 / (m : ℝ)) (bbar c τ θ) (hA c τ θ u) - tauOut c τ θ) ^ 2) =
        fun u => 2 / (m : ℝ) * (√(normSq (res (bbar c τ θ) (hA c τ θ u))) -
          √(d - normSq (bbar c τ θ))) ^ 2 := by
      funext u
      rw [htau, sig, ← mul_sub, mul_pow, Real.sq_sqrt hV0]
    rw [e, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hSS hV0
  obtain ⟨H, hH⟩ := hA_bound hn c τ θ
  have hL0 : 0 ≤ Δ / su + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2 := by positivity
  have key := stageA (stdGauss (Fin n)) (mF := mF) hV0 hb (measurable_hA c τ θ) hH hn hmF hL0 hLr
    hR (tauOut c τ θ) hYl hS hη
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the three monotone bounds
  have c1 : 2 / (m : ℝ) * (d + d * δ - normSq (bbar c τ θ)) ≤
      2 / (n : ℝ) * (1 - alo + δmax + Δmax) := by
    have a1 : 2 / (m : ℝ) * (d + d * δ - normSq (bbar c τ θ)) ≤
        2 / (m : ℝ) * (d * (1 + δ - au + Δ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hV0
    have a2 : 2 / (n : ℝ) * (1 + δ - au + Δ) ≤ 2 / (n : ℝ) * (1 - alo + δmax + Δmax) :=
      mul_le_mul_of_nonneg_left (by linarith) hN0
    calc _ ≤ 2 / (m : ℝ) * (d * (1 + δ - au + Δ)) := a1
      _ = 2 / (n : ℝ) * (1 + δ - au + Δ) := by rw [← hvd]; ring
      _ ≤ _ := a2
  have c2 : 2 / (m : ℝ) * ((d * Δ) ^ 2 / (d * au - d * Δ)) ≤ 2 / (n : ℝ) * (r₁ ^ 2 * Δ ^ 2) := by
    have e2 : (d * Δ) ^ 2 / (d * au - d * Δ) = d * (Δ ^ 2 / (au - Δ)) := by
      rw [show d * au - d * Δ = d * (au - Δ) by ring]
      field_simp
    have k : Δ ^ 2 / (au - Δ) ≤ r₁ ^ 2 * Δ ^ 2 := by
      rw [div_le_iff₀ h1]
      calc Δ ^ 2 = Δ ^ 2 * 1 := by ring
        _ ≤ Δ ^ 2 * (r₁ ^ 2 * (au - Δ)) := mul_le_mul_of_nonneg_left hr1'' (sq_nonneg Δ)
        _ = _ := by ring
    calc _ = 2 / (n : ℝ) * (Δ ^ 2 / (au - Δ)) := by rw [e2, ← hvd]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left k hN0
  have c3 : 2 / (m : ℝ) *
      (d * Δ / √(d * au - d * Δ) + (d * δ + 2 * (d * Δ)) / √(d - d * au - d * Δ)) ^ 2 ≤
      2 / (n : ℝ) * (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2 := by
    have e1 : d * Δ / √(d * au - d * Δ) = √d * (Δ / √(au - Δ)) := by
      rw [show d * au - d * Δ = d * (au - Δ) by ring]
      exact div_sqrt_scale hd0 h1
    have e2 : (d * δ + 2 * (d * Δ)) / √(d - d * au - d * Δ) =
        √d * ((δ + 2 * Δ) / √(1 - au - Δ)) := by
      rw [show d - d * au - d * Δ = d * (1 - au - Δ) by ring,
        show d * δ + 2 * (d * Δ) = d * (δ + 2 * Δ) by ring]
      exact div_sqrt_scale hd0 h2
    have k1 : Δ / √(au - Δ) ≤ r₁ * Δ := div_sqrt_le hr₁ h1 hr1'' hΔ0
    have k2 : (δ + 2 * Δ) / √(1 - au - Δ) ≤ r₂ * (δ + 2 * Δ) :=
      div_sqrt_le hr₂ h2 hr2'' (by positivity)
    have k0 : 0 ≤ Δ / √(au - Δ) + (δ + 2 * Δ) / √(1 - au - Δ) := by positivity
    have k : (Δ / √(au - Δ) + (δ + 2 * Δ) / √(1 - au - Δ)) ^ 2 ≤
        (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2 := pow_le_pow_left₀ k0 (add_le_add k1 k2) 2
    have hsd := Real.sq_sqrt hd0.le
    calc _ = 2 / (n : ℝ) * (Δ / √(au - Δ) + (δ + 2 * Δ) / √(1 - au - Δ)) ^ 2 := by
          rw [e1, e2, ← hvd, ← mul_add, mul_pow, hsd]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left k hN0
  have p1 : 0 ≤ 1 + η := by positivity
  have p2 : 0 ≤ 1 + 1 / η := by positivity
  have t1 : (Δ / su + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) *
      (2 * (2 / (m : ℝ)) * (d + d * δ - normSq (bbar c τ θ))) ≤
      2 / (n : ℝ) * (2 * (Δ / su + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) *
        (1 - alo + δmax + Δmax)) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 hL0) zero_le_two
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_)) <;> ring
  have t2 : 2 * (2 / (m : ℝ) * ((d * Δ) ^ 2 / (d * au - d * Δ)) + 2 / (m : ℝ) *
      (d * Δ / √(d * au - d * Δ) + (d * δ + 2 * (d * Δ)) / √(d - d * au - d * Δ)) ^ 2) ≤
      2 / (n : ℝ) * (2 * (r₁ ^ 2 * Δ ^ 2 + (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2)) := by
    linarith
  refine (add_le_add (mul_le_mul_of_nonneg_left t1 p1) (mul_le_mul_of_nonneg_left t2 p2)).trans
    (le_of_eq ?_)
  ring

end BstLean.Part149

open BstLean.Part149 in
#print axioms stagePt
