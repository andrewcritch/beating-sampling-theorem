import BstLean.Part149Pt
import BstLean.Part149Stage2
import BstLean.Part149Frame2

/-!
# Part 149: the stage of the Agent network, pointwise in the hidden weights (second route)

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md` (the `A`-stage error for FIXED hidden weights
`θ = (A₁, A₂)`, by the route of the unit residual directions). The hidden map is `h = hA c τ θ` on
`(ℝⁿ, stdGauss)`; `v = 2/m`; `d = m/n`; `b = bbar c τ θ`; `σ₀ = √(d − |b|²)`. The hypotheses are
in units of `d`: `errKc (d·au) c τ θ ≤ (d·Δ)²`, `errDc c τ θ ≤ (d·δ)²`, and
`‖⟨h, b⟩ − |b|²‖₂ ≤ d·ΔX`.

* `stagePt2`: `scalarsB`, `dirB`, `dirB2` (Part149Frame2) with the raw values `d·au`, `d·Δ`, `d`,
  `d·δ`, `d·ΔX`, `s = d·w²`, then `stageA2` (Part149Stage2) with `σ₀ = √(d − |b|²)`, for which
  `tauOut c τ θ = √v·σ₀`; the right side is bounded with constants that are monotone in
  `Δ ≤ Δmax`, `alo ≤ au ≤ ahi`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)

/-- `d·x/√(d·y) = √d·(x/√y)`. -/
private lemma div_sqrt_scale2 {d x y : ℝ} (hd : 0 < d) (hy : 0 < y) :
    d * x / √(d * y) = √d * (x / √y) := by
  have hsd : 0 < √d := Real.sqrt_pos.2 hd
  have hsy : 0 < √y := Real.sqrt_pos.2 hy
  rw [Real.sqrt_mul hd.le, div_eq_iff (by positivity)]
  have h1 := Real.mul_self_sqrt hd.le
  have h2 : x / √y * √y = x := div_mul_cancel₀ _ hsy.ne'
  linear_combination (-d) * h2 - (x / √y * √y) * h1

/-- If `1 ≤ r²·x` then `t/√x ≤ r·t` for `t ≥ 0`. -/
private lemma div_sqrt_le2 {r x t : ℝ} (hr : 0 < r) (hx : 0 < x) (h : 1 ≤ r ^ 2 * x)
    (ht : 0 ≤ t) : t / √x ≤ r * t := by
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have h1 : (1 : ℝ) ^ 2 ≤ (r * √x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx.le]; simpa using h
  have h2 : 1 ≤ r * √x := (le_abs_self 1).trans (abs_le_of_sq_le_sq h1 (by positivity))
  rw [div_le_iff₀ hsx]
  have := mul_le_mul_of_nonneg_left h2 ht
  linarith

/-- The arithmetic of the three direction quantities: from the raw bounds of `dirB` and `dirB2`
(divided by `d`) to the constant `Lt`. -/
private lemma lt_arith {x Δ ΔX K E Sb r₁ r₂ w g q E1 E2 p μB : ℝ}
    (hr₂' : 1 ≤ r₂ ^ 2 * x) (hw : 0 < w) (hg : 0 < g) (hq : g + w ≤ q)
    (hΔ0 : 0 ≤ Δ) (hK0 : 0 ≤ K) (hK : K ≤ r₁ ^ 2 * ΔX ^ 2) (hES : E ^ 2 ≤ Sb)
    (hE1 : 0 ≤ E1) (hP1 : x * E1 ≤ E ^ 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hP3 : p ≤ μB) (hμ0 : 0 ≤ μB)
    (hP4 : (q - w) ^ 2 * μB ≤ E ^ 2)
    (hE2 : E2 ≤ (Δ + K) ^ 2 / w ^ 4 + 2 * μB) :
    E1 + E2 + p ^ 2 ≤ r₂ ^ 2 * Sb + (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 + 3 * Sb / g ^ 2 := by
  have a1 : E1 ≤ r₂ ^ 2 * Sb := by
    have h1 : E1 ≤ r₂ ^ 2 * x * E1 := by
      have := mul_le_mul_of_nonneg_right hr₂' hE1
      linarith
    have h2 : r₂ ^ 2 * (x * E1) ≤ r₂ ^ 2 * Sb :=
      mul_le_mul_of_nonneg_left (hP1.trans hES) (sq_nonneg _)
    linarith
  have a2 : μB ≤ Sb / g ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : g ^ 2 ≤ (q - w) ^ 2 := pow_le_pow_left₀ hg.le (by linarith) 2
    have := mul_le_mul_of_nonneg_right h1 hμ0
    linarith
  have a3 : p ^ 2 ≤ μB := by
    have : p ^ 2 ≤ p := by nlinarith
    linarith
  have a4 : (Δ + K) ^ 2 / w ^ 4 ≤ (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by positivity)
  have e : 3 * Sb / g ^ 2 = 3 * (Sb / g ^ 2) := by ring
  rw [e]
  linarith

/-- **The stage of the Agent network at the stand-in inputs, for fixed hidden weights, by the
route of the unit residual directions.** -/
theorem stagePt2 {n m mF : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmF : 1 ≤ mF) (c : Fin n → ℝ) (τ : ℝ)
    (θ : HidParam n m)
    {au alo ahi Δmax r₁ r₂ w g η : ℝ} (halo : alo ≤ au) (hahi : au ≤ ahi)
    (hΔmax : 0 ≤ Δmax) (hA1 : Δmax < alo) (hA2 : ahi + Δmax < 1)
    (hr₁ : 0 < r₁) (hr₁' : 1 ≤ r₁ ^ 2 * (alo - Δmax))
    (hr₂ : 0 < r₂) (hr₂' : 1 ≤ r₂ ^ 2 * (1 - ahi - Δmax))
    (hw : 0 < w) (hg : 0 < g) (hgw : (g + w) ^ 2 ≤ 1 - ahi - Δmax) (hη : 0 < η)
    {Δ ΔX δ : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ Δmax) (hΔX0 : 0 ≤ ΔX) (hδ0 : 0 ≤ δ)
    (hK : errKc ((m : ℝ) / n * au) c τ θ ≤ ((m : ℝ) / n * Δ) ^ 2)
    (hD : errDc c τ θ ≤ ((m : ℝ) / n * δ) ^ 2)
    (hX : ∫ γ, (∑ j, hA c τ θ γ j * bbar c τ θ j - normSq (bbar c τ θ)) ^ 2
      ∂stdGauss (Fin n) ≤ ((m : ℝ) / n * ΔX) ^ 2) :
    ∫⁻ p, ENNReal.ofReal ((gT (stdGauss (Fin n)) (hA c τ θ) p -
        gO (bbar c τ θ) (tauOut c τ θ) p) ^ 2)
        ∂((gaussMat n m (2 / (m : ℝ))).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal (2 / (n : ℝ) * ((1 + η) * (2 * (r₁ ^ 2 * ΔX ^ 2 +
          (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2)) +
        (1 + 1 / η) * (2 * (1 - alo + Δmax) *
          (r₂ ^ 2 * (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 +
            (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 +
            3 * (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 / g ^ 2)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (m : ℝ) / n := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hV0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hN0 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have hvd : 2 / (m : ℝ) * d = 2 / (n : ℝ) := by rw [hd]; field_simp
  have h1 : 0 < au - Δ := by linarith
  have h2 : 0 < 1 - au - Δ := by linarith
  have hr1'' : 1 ≤ r₁ ^ 2 * (au - Δ) :=
    hr₁'.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))
  have hr2'' : 1 ≤ r₂ ^ 2 * (1 - au - Δ) :=
    hr₂'.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))
  have hgw' : (g + w) ^ 2 ≤ 1 - au - Δ := by linarith
  have hw2 : w ^ 2 < 1 - au - Δ := by nlinarith
  have hh := bm_hA hn c τ θ
  have hKr : ∫ p, (∑ k, hA c τ θ p.1 k * hA c τ θ p.2 k - d * au) ^ 2
      ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) ≤ (d * Δ) ^ 2 := by
    rw [hd]; exact hK
  have hDr : ∫ γ, (normSq (hA c τ θ γ) - d) ^ 2 ∂stdGauss (Fin n) ≤ (d * δ) ^ 2 := by
    rw [hd]; exact hD
  have hXr : ∫ γ, (∑ j, hA c τ θ γ j * hbar (stdGauss (Fin n)) (hA c τ θ) j -
      normSq (hbar (stdGauss (Fin n)) (hA c τ θ))) ^ 2 ∂stdGauss (Fin n) ≤ (d * ΔX) ^ 2 := by
    rw [hd]; exact hX
  have hΔa : d * Δ < d * au := mul_lt_mul_of_pos_left (by linarith) hd0
  have hda : d * au + d * Δ < d := by
    have := mul_pos hd0 h2
    linarith
  have hs0 : 0 < d * w ^ 2 := by positivity
  have hs' : d * w ^ 2 < d - d * au - d * Δ := by
    have := mul_lt_mul_of_pos_left hw2 hd0
    linarith
  have sc := scalarsB (stdGauss (Fin n)) hh (a := d * au) (Δ := d * Δ) (d := d) (δ := d * δ)
    (ΔX := d * ΔX) (by positivity) (by positivity) (by positivity) hΔa hda hKr hDr hXr
  have dr := dirB (stdGauss (Fin n)) hh (a := d * au) (Δ := d * Δ) (d := d) (δ := d * δ)
    (ΔX := d * ΔX) (by positivity) (by positivity) (by positivity) hΔa hda hKr hDr hXr hs0 hs'
  have d2 := dirB2 (stdGauss (Fin n)) hh (a := d * au) (Δ := d * Δ) (d := d) (δ := d * δ)
    (ΔX := d * ΔX) (by positivity) (by positivity) (by positivity) hΔa hda hKr hDr hXr hs0 hs'
  rw [show hbar (stdGauss (Fin n)) (hA c τ θ) = bbar c τ θ from rfl] at sc dr d2
  obtain ⟨hY, hYl, -, hSS⟩ := sc
  obtain ⟨hP1, hP3, hP4⟩ := dr
  have hYge : d * au - d * Δ ≤ normSq (bbar c τ θ) := by linarith [(abs_le.mp hY).1]
  have hYle : normSq (bbar c τ θ) ≤ d * au + d * Δ := by linarith [(abs_le.mp hY).2]
  have hYd : 0 < d - normSq (bbar c τ θ) := by linarith
  have hYpos : 0 < normSq (bbar c τ θ) := by linarith
  have hb : bbar c τ θ ≠ 0 := by
    intro h0
    rw [h0] at hYpos
    simp [normSq] at hYpos
  -- the constant scalar
  have htau : tauOut c τ θ = √(2 / (m : ℝ)) * √(d - normSq (bbar c τ θ)) := by
    have e : 2 / (n : ℝ) - 2 / (m : ℝ) * normSq (bbar c τ θ) =
        2 / (m : ℝ) * (d - normSq (bbar c τ θ)) := by rw [← hvd]; ring
    rw [tauOut, e, max_eq_right (mul_nonneg hV0 hYd.le), Real.sqrt_mul hV0]
  -- the raw constants in units of `d`
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ΔX ^ 2 / (au - Δ) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = ΔX / √(au - Δ) + (δ + 2 * ΔX) / √(1 - au - Δ) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have eK : (d * ΔX) ^ 2 / (d * au - d * Δ) = d * K := by
    rw [hKdef, show d * au - d * Δ = d * (au - Δ) by ring]
    field_simp
  have hsd := Real.sq_sqrt hd0.le
  have eS : (d * ΔX / √(d * au - d * Δ) + (d * δ + 2 * (d * ΔX)) / √(d - d * au - d * Δ)) ^ 2 =
      d * E ^ 2 := by
    have e1 : d * ΔX / √(d * au - d * Δ) = √d * (ΔX / √(au - Δ)) := by
      rw [show d * au - d * Δ = d * (au - Δ) by ring]
      exact div_sqrt_scale2 hd0 h1
    have e2 : (d * δ + 2 * (d * ΔX)) / √(d - d * au - d * Δ) =
        √d * ((δ + 2 * ΔX) / √(1 - au - Δ)) := by
      rw [show d - d * au - d * Δ = d * (1 - au - Δ) by ring,
        show d * δ + 2 * (d * ΔX) = d * (δ + 2 * ΔX) by ring]
      exact div_sqrt_scale2 hd0 h2
    rw [e1, e2, ← mul_add, mul_pow, hsd, hEdef]
  rw [eK] at hYl d2
  rw [eS] at hSS
  have hKle : K ≤ r₁ ^ 2 * ΔX ^ 2 := by
    rw [hKdef, div_le_iff₀ h1]
    calc ΔX ^ 2 = ΔX ^ 2 * 1 := by ring
      _ ≤ ΔX ^ 2 * (r₁ ^ 2 * (au - Δ)) := mul_le_mul_of_nonneg_left hr1'' (sq_nonneg ΔX)
      _ = _ := by ring
  have hES : E ^ 2 ≤ (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 := by
    have k1 : ΔX / √(au - Δ) ≤ r₁ * ΔX := div_sqrt_le2 hr₁ h1 hr1'' hΔX0
    have k2 : (δ + 2 * ΔX) / √(1 - au - Δ) ≤ r₂ * (δ + 2 * ΔX) :=
      div_sqrt_le2 hr₂ h2 hr2'' (by positivity)
    rw [hEdef] at hE0 ⊢
    exact pow_le_pow_left₀ hE0 (add_le_add k1 k2) 2
  -- the three direction quantities
  obtain ⟨E1, hE1def⟩ : ∃ E1 : ℝ, E1 =
      ∑ j, (∫ u, eDir (bbar c τ θ) (hA c τ θ u) j ∂stdGauss (Fin n)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨μB, hμBdef⟩ : ∃ μB : ℝ, μB = (stdGauss (Fin n)).real
      {u | normSq (res (bbar c τ θ) (hA c τ θ u)) < d * w ^ 2} := ⟨_, rfl⟩
  rw [← hE1def] at hP1
  rw [← hμBdef] at hP3 hP4 d2
  have hE10 : 0 ≤ E1 := by rw [hE1def]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hμ0 : 0 ≤ μB := by rw [hμBdef]; exact measureReal_nonneg
  have hq : g + w ≤ √(1 - au - Δ) := Real.le_sqrt_of_sq_le hgw'
  have hP1' : (1 - au - Δ) * E1 ≤ E ^ 2 := by
    have a1 : d * (1 - au - Δ) * E1 ≤ (d - normSq (bbar c τ θ)) * E1 :=
      mul_le_mul_of_nonneg_right (by linarith) hE10
    have a2 : d * ((1 - au - Δ) * E1) ≤ d * E ^ 2 := by linarith
    exact le_of_mul_le_mul_left a2 hd0
  have hP4' : (√(1 - au - Δ) - w) ^ 2 * μB ≤ E ^ 2 := by
    have e1 : √(d - d * au - d * Δ) = √d * √(1 - au - Δ) := by
      rw [show d - d * au - d * Δ = d * (1 - au - Δ) by ring, Real.sqrt_mul hd0.le]
    have e2 : √(d * w ^ 2) = √d * w := by
      rw [Real.sqrt_mul hd0.le, Real.sqrt_sq hw.le]
    rw [e1, e2, ← mul_sub, mul_pow, hsd] at hP4
    have a2 : d * ((√(1 - au - Δ) - w) ^ 2 * μB) ≤ d * E ^ 2 := by linarith
    exact le_of_mul_le_mul_left a2 hd0
  have hE2 : ∫ p, (∑ j, eDir (bbar c τ θ) (hA c τ θ p.1) j * eDir (bbar c τ θ) (hA c τ θ p.2) j) ^ 2
      ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) ≤ (Δ + K) ^ 2 / w ^ 4 + 2 * μB := by
    have e : (d * Δ + d * K) ^ 2 / (d * w ^ 2) ^ 2 = (Δ + K) ^ 2 / w ^ 4 := by
      rw [show (d * Δ + d * K) ^ 2 = d ^ 2 * (Δ + K) ^ 2 by ring,
        show (d * w ^ 2) ^ 2 = d ^ 2 * w ^ 4 by ring,
        mul_div_mul_left _ _ (pow_ne_zero 2 hd0.ne')]
    rw [e] at d2
    exact d2
  have hLt := lt_arith (r₁ := r₁) hr2'' hw hg hq hΔ0 hK0 hKle hES hE10 hP1'
    measureReal_nonneg measureReal_le_one hP3 hμ0 hP4' hE2
  rw [hE1def] at hLt
  have hLt0 : 0 ≤ r₂ ^ 2 * (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 +
      (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 + 3 * (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 / g ^ 2 := by
    positivity
  obtain ⟨H, hH⟩ := hA_bound hn c τ θ
  have key := stageA2 (stdGauss (Fin n)) (n := n) (mF := mF) hV0 hb (measurable_hA c τ θ) hH hn
    hmF (√(d - normSq (bbar c τ θ))) hYl hSS hLt0 hLt hη
  rw [← htau] at key
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have p1 : 0 ≤ 1 + η := by positivity
  have p2 : 0 ≤ 1 + 1 / η := by positivity
  have t1 : 2 * (2 / (m : ℝ)) * (d * K + d * E ^ 2) ≤
      2 / (n : ℝ) * (2 * (r₁ ^ 2 * ΔX ^ 2 + (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2)) := by
    have e : 2 * (2 / (m : ℝ)) * (d * K + d * E ^ 2) = 2 / (n : ℝ) * (2 * (K + E ^ 2)) := by
      rw [← hvd]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hN0
  have c1 : (tauOut c τ θ) ^ 2 ≤ 2 / (n : ℝ) * (1 - alo + Δmax) := by
    rw [htau, mul_pow, Real.sq_sqrt hV0, Real.sq_sqrt hYd.le]
    have a1 : 2 / (m : ℝ) * (d - normSq (bbar c τ θ)) ≤ 2 / (m : ℝ) * (d * (1 - au + Δ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hV0
    have a2 : 2 / (n : ℝ) * (1 - au + Δ) ≤ 2 / (n : ℝ) * (1 - alo + Δmax) :=
      mul_le_mul_of_nonneg_left (by linarith) hN0
    calc _ ≤ 2 / (m : ℝ) * (d * (1 - au + Δ)) := a1
      _ = 2 / (n : ℝ) * (1 - au + Δ) := by rw [← hvd]; ring
      _ ≤ _ := a2
  have t2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 zero_le_two) hLt0
  refine (add_le_add (mul_le_mul_of_nonneg_left t1 p1) (mul_le_mul_of_nonneg_left t2 p2)).trans
    (le_of_eq ?_)
  ring

end BstLean.Part149

open BstLean.Part149 in
#print axioms stagePt2
