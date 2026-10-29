import BstLean.Part182SchurI
import BstLean.Part182Geo
import BstLean.Part182EvW
import BstLean.Part182Ew
import BstLean.Part182Poin

/-!
# Part 182 (file `Cov`): the covariance bound `N_cov ≈ 0.30` on the event `SCovT ∩ SXM22`

No proof is left open; no `native_decide` or `axiom` is used.

The single-level weighted Schur test (file `SchurI`, `Dq_le_kern` with `Ω₁ = Ω₀ = Ω(5, 14)`, the
kernel `n·0.582` on the good pairs `G = Γ(5, 14, 8) \ (bad ∪ bad∘swap)`), with:
* `E w ≤ 1.0182 θ/n` (file `Ew`);
* the exceptional pair mass `μ²(Gᶜ ∩ Ω²) ≤ 2e^{−32} + 2·10⁻¹⁴` (file `Geo`: `gamma_row_le`; the event
  `SCovT`: `badMass ≤ 10⁻¹⁴`);
* the outside mass `μ(Ωᶜ) ≤ 2e^{−12.5} + 2e^{−14}` (file `Geo`: `omega_compl_le`);
* `Ξ₄ ≤ 1.1·1.0182·θ_hi·γ_A/n` on `SXM22` (Part 181 `Xi4_SXM22`).

**`Dq_TI`**: `Dq v ≤ (0.582·1.0182·θ_hi + 1.1·1.0182·θ_hi·0.003486)·(γ_A/n)·|v|²`, and
**`cov_TI`**: `COV_at D c N` for every `N` above that constant. No hypothesis `TI_hyp` is used
here: the event `SCovT` is assumed; its charge needs `TI_hyp` (file `EvW`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nrm jacT Xi4 nuA)

variable {n : ℕ}

/-! ## Numbers -/

lemma exp_neg_one_le' : exp (-1) ≤ (3678794412 / 10 ^ 10 : ℝ) := by
  have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith

lemma exp_neg_nat_le (k : ℕ) : exp (-(k : ℝ)) ≤ (3678794412 / 10 ^ 10 : ℝ) ^ k := by
  have e : exp (-(k : ℝ)) = exp (-1) ^ k := by rw [← Real.exp_nat_mul]; ring_nf
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le exp_neg_one_le' k

lemma exp_neg_half_le : exp (-(1 / 2) : ℝ) ≤ (606531 / 10 ^ 6 : ℝ) := by
  refine BstLean.Part156.exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma two_exp_neg32 : 2 * exp (-(8 : ℝ) ^ 2 / 2) ≤ (26 / 10 ^ 15 : ℝ) := by
  have e : -(8 : ℝ) ^ 2 / 2 = -((32 : ℕ) : ℝ) := by norm_num
  rw [e]
  have h := exp_neg_nat_le 32
  have : (2 : ℝ) * (3678794412 / 10 ^ 10) ^ 32 ≤ 26 / 10 ^ 15 := by norm_num
  linarith

lemma Po_le : 2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ)) ≤ (9126 / 10 ^ 9 : ℝ) := by
  have e1 : -(5 : ℝ) ^ 2 / 2 = -((12 : ℕ) : ℝ) + -(1 / 2) := by norm_num
  have e2 : -(14 : ℝ) = -((14 : ℕ) : ℝ) := by norm_num
  rw [e1, e2, Real.exp_add]
  have h12 := exp_neg_nat_le 12
  have h14 := exp_neg_nat_le 14
  have hh := exp_neg_half_le
  have h0 : 0 ≤ exp (-((12 : ℕ) : ℝ)) := (exp_pos _).le
  have hm : exp (-((12 : ℕ) : ℝ)) * exp (-(1 / 2)) ≤
      (3678794412 / 10 ^ 10 : ℝ) ^ 12 * (606531 / 10 ^ 6) :=
    mul_le_mul h12 hh (exp_pos _).le (by positivity)
  have : (2 : ℝ) * ((3678794412 / 10 ^ 10) ^ 12 * (606531 / 10 ^ 6)) +
      2 * (3678794412 / 10 ^ 10) ^ 14 ≤ 9126 / 10 ^ 9 := by norm_num
  linarith

lemma sqrt_sqrt_le_of {H q : ℝ} (hq : 0 ≤ q) (hH : H ≤ q ^ 4) : √(√H) ≤ q := by
  have e : q ^ 4 = (q ^ 2) ^ 2 := by ring
  rw [e] at hH
  have h1 : √H ≤ q ^ 2 :=
    (Real.sqrt_le_sqrt hH).trans (le_of_eq (Real.sqrt_sq (by positivity)))
  exact (Real.sqrt_le_sqrt h1).trans (le_of_eq (Real.sqrt_sq hq))

/-! ## Helpers -/

lemma sqrt_le_of_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : √a ≤ b :=
  (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hb))

lemma ne_zero_of_thetaC_lt (hn : 0 < n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (h : thetaC c τ < 1) : c ≠ 0 := by
  intro hc
  apply (lt_irrefl (1 : ℝ))
  have e : thetaC c τ = 1 := by
    unfold thetaC rhoC
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < (n : ℝ) * τ ^ 2 := by positivity
    have hc0 : normSq c = 0 := by rw [hc]; simp [normSq]
    rw [hc0, zero_add, Real.sq_sqrt hp.le, div_self hp.ne']
  linarith

/-- `r₋ < 1` (indeed `≤ 0.061`) on the window, for the wide parameters `(t₀, z₀) = (5, 14)`. -/
lemma rminus_lt (hn : 22000 ≤ n) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 528 / 1000) :
    2 * 5 * √(θ * (1 - θ) / n) + 2 * θ * √(14 / n) < 1 := by
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : √(θ * (1 - θ) / n) ≤ 1 / 296 := by
    refine sqrt_le_of_sq' (by norm_num) ?_
    rw [div_le_iff₀ hn0]
    have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
    nlinarith
  have h2 : √((14 : ℝ) / n) ≤ 253 / 10000 := by
    refine sqrt_le_of_sq' (by norm_num) ?_
    rw [div_le_iff₀ hn0]
    nlinarith
  have h3 : 0 ≤ √((14 : ℝ) / n) := Real.sqrt_nonneg _
  nlinarith

/-- The symmetry of `Γ`. -/
lemma gammaS_swap {c : Fin n → ℝ} {t0 z0 t1 : ℝ} {a b : Fin n → ℝ}
    (h : (a, b) ∈ GammaS c t0 z0 t1) : (b, a) ∈ GammaS c t0 z0 t1 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, h1, ?_⟩
  simpa only [dotProduct_comm] using h3

/-- The mass of the pairs of `Ω²` outside `Γ`: at most `2e^{−t₁²/2}`. -/
lemma pairs_out_gamma (hn : 0 < n) (c : Fin n → ℝ) {t0 z0 t1 : ℝ} (hz0 : 0 ≤ z0) (ht1 : 0 ≤ t1) :
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
      ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) ≤ 2 * exp (-t1 ^ 2 / 2) := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hΩ := measurableSet_OmegaS c t0 z0
  have hm : MeasurableSet ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) :=
    (hΩ.prod hΩ).diff (measurableSet_GammaS c t0 z0 t1)
  have hB : 0 ≤ 2 * exp (-t1 ^ 2 / 2) := by positivity
  rw [Measure.real, Measure.prod_apply hm]
  have hle : ∫⁻ ξ, (stdGauss (Fin n)) (Prod.mk ξ ⁻¹'
      ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1)) ∂stdGauss (Fin n) ≤
      ∫⁻ _ξ, ENNReal.ofReal (2 * exp (-t1 ^ 2 / 2)) ∂stdGauss (Fin n) := by
    refine lintegral_mono fun ξ => ?_
    by_cases hξ : ξ ∈ OmegaS c t0 z0
    · have e : Prod.mk ξ ⁻¹' ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) =
          {ξ' | ξ' ∈ OmegaS c t0 z0 ∧ (ξ, ξ') ∉ GammaS c t0 z0 t1} := by
        ext ξ'
        simp only [Set.mem_preimage, Set.mem_diff, Set.mem_prod, Set.mem_setOf_eq]
        tauto
      rw [e]
      have h := gamma_row_le hn c hz0 ht1 (t0 := t0) hξ
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h
    · have e : Prod.mk ξ ⁻¹' ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1) = ∅ := by
        ext ξ'
        simp only [Set.mem_preimage, Set.mem_diff, Set.mem_prod, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1
        exact absurd h1.1 hξ
      rw [e, measure_empty]
      exact bot_le
  rw [lintegral_const, measure_univ, mul_one] at hle
  calc (∫⁻ ξ, (stdGauss (Fin n)) (Prod.mk ξ ⁻¹'
        ((OmegaS c t0 z0 ×ˢ OmegaS c t0 z0) \ GammaS c t0 z0 t1)) ∂stdGauss (Fin n)).toReal
      ≤ (ENNReal.ofReal (2 * exp (-t1 ^ 2 / 2))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = 2 * exp (-t1 ^ 2 / 2) := ENNReal.toReal_ofReal hB

/-! ## The covariance bound -/

/-- **The quadratic form of `D` on `SXM22 ∩ SCovT`** (single-level weighted Schur test):
`Dq v ≤ (0.582·1.0182·θ_hi + 1.1·1.0182·θ_hi·0.003486)·(γ_A/n)·|v|²` for `n ≥ 22 000` and
`0.46 ≤ θ ≤ θ_hi ≤ 0.528`. -/
theorem Dq_TI (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hX : ((c, τ), (A₁, A₂)) ∈ BstLean.Part181.SXM22 n) (hC : ((c, τ), (A₁, A₂)) ∈ SCovT n)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ (582 / 1000 * (10182 / 10000) * θh +
      11 / 10 * (10182 / 10000) * θh * (3486 / 10 ^ 6)) * (2 / (n : ℝ)) / n * normSq v := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn0 : 0 < n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < n := by linarith
  have hθlt : thetaC c τ < 1 := by linarith
  have hc : c ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθlt
  set μ := stdGauss (Fin n) with hμ
  set Ω := OmegaS c 5 14 with hΩd
  set Γ := GammaS c 5 14 8 with hΓd
  set key : AgFam n := ((c, τ), (A₁, A₂)) with hkey
  set Bx : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | (key, p) ∈ badSet n 5 14 8 (582 / 1000)} with hBxd
  have hBxm : MeasurableSet Bx := measurable_prodMk_left (measurableSet_badSet 5 14 8 (582 / 1000))
  have hΩm : MeasurableSet Ω := measurableSet_OmegaS c 5 14
  have hΓm : MeasurableSet Γ := measurableSet_GammaS c 5 14 8
  set G := Γ \ (Bx ∪ Prod.swap ⁻¹' Bx) with hGd
  have hGm : MeasurableSet G := hΓm.diff (hBxm.union (measurable_swap hBxm))
  have hGs : ∀ a b, (a, b) ∈ G → (b, a) ∈ G := by
    intro a b h
    obtain ⟨h1, h2⟩ := h
    refine ⟨gammaS_swap h1, ?_⟩
    rintro (h3 | h3)
    · exact h2 (Or.inr h3)
    · exact h2 (Or.inl h3)
  have hpair : ∀ a b, (a, b) ∈ G → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      (n : ℝ) * (582 / 1000) := by
    intro a b h
    obtain ⟨h1, h2⟩ := h
    have hnb : ¬ pairBad A₁ A₂ (582 / 1000) (sphPt (c + τ • a)) (sphPt (c + τ • b)) := by
      intro hb
      exact h2 (Or.inl ⟨h1, hb⟩)
    unfold pairBad at hnb
    exact not_lt.mp hnb
  have hpair₁ : ∀ a b, (a, b) ∈ G → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      kern Set.univ ((n : ℝ) * (582 / 1000)) ((n : ℝ) * (582 / 1000)) a b := by
    intro a b h
    rw [kern_of_mem (Set.mem_univ _)]
    exact hpair a b h
  -- the weight bounds
  have hr := rminus_lt hn (by linarith) (hθ1.trans hθh)
  set rm := 2 * 5 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(14 / n) with hrm
  have hWb : ∀ ξ ∈ Ω, wN c τ ξ ≤ thetaC c τ / n / (1 - rm) := by
    intro ξ hξ
    have h := omega_weight hn0 hc hτ (t0 := 5) (z0 := 14) (by norm_num) (by norm_num) hξ
      (by simpa only [hrm, mul_assoc] using hr)
    simpa only [wN, hrm, mul_assoc] using h
  have hWb0 : 0 ≤ thetaC c τ / n / (1 - rm) := by
    have : 0 < 1 - rm := by linarith
    have : 0 ≤ thetaC c τ := by linarith
    positivity
  have hEw : ∫ ξ, wN c τ ξ ∂μ ≤ 10182 / 10000 * (thetaC c τ / n) := by
    have h := Ew_le_22 hn c hτ hθ0 (hθ1.trans hθh)
    simpa only [wN, integral_const_mul] using h
  have hPp : ∀ ξ, μ.real {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ (Set.univ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} ≤
      0 := by
    intro ξ
    have e : {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ (Set.univ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} = ∅ := by
      ext ξ'; simp
    rw [e, measureReal_empty]
  have hPs : μ.real (Ω \ Ω) ≤ 0 := by rw [Set.diff_self, measureReal_empty]
  have hmain := Dq_le_kern A₁ A₂ c (by omega) hτ (subset_refl Ω) hΩm hΩm
    (lam₁ := 582 / 1000) (lam₀ := 582 / 1000) (by norm_num) (by norm_num)
    Set.univ MeasurableSet.univ (fun _ _ _ => Set.mem_univ _) G hGm hGs hpair₁ G hGm hGs hpair
    hEw hWb0 hWb hPp hPs v
  -- the exceptional masses
  have hH0 : ((μ.prod μ).real (Gᶜ ∩ (Ω \ Ω) ×ˢ (Ω \ Ω))) = 0 := by
    rw [Set.diff_self, Set.empty_prod, Set.inter_empty, measureReal_empty]
  have hwin : winT c τ := ⟨hθ0, hθ1.trans hθh⟩
  have hbad : badMass n 5 14 8 (582 / 1000) key ≤ 1 / 10 ^ 14 := by
    rcases hC with h | h
    · exact absurd hwin h
    · exact h
  have hBxr : (μ.prod μ).real Bx ≤ 1 / 10 ^ 14 := hbad
  have hBxs : (μ.prod μ).real (Prod.swap ⁻¹' Bx) = (μ.prod μ).real Bx := by
    rw [Measure.real, Measure.real,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage hBxm.nullMeasurableSet]
  have hout := pairs_out_gamma hn0 c (t0 := 5) (z0 := 14) (t1 := 8) (by norm_num) (by norm_num)
  have hH1 : (μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω) ≤ 26 / 10 ^ 15 + 2 / 10 ^ 14 := by
    have hsub : Gᶜ ∩ Ω ×ˢ Ω ⊆ ((Ω ×ˢ Ω) \ Γ) ∪ Bx ∪ Prod.swap ⁻¹' Bx := by
      rintro p ⟨hp1, hp2⟩
      by_cases hpΓ : p ∈ Γ
      · have : p ∈ Bx ∪ Prod.swap ⁻¹' Bx := by
          by_contra hn'
          exact hp1 ⟨hpΓ, hn'⟩
        rcases this with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl ⟨hp2, hpΓ⟩)
    calc (μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω)
        ≤ (μ.prod μ).real (((Ω ×ˢ Ω) \ Γ) ∪ Bx ∪ Prod.swap ⁻¹' Bx) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (μ.prod μ).real (((Ω ×ˢ Ω) \ Γ) ∪ Bx) + (μ.prod μ).real (Prod.swap ⁻¹' Bx) :=
          measureReal_union_le _ _
      _ ≤ (μ.prod μ).real ((Ω ×ˢ Ω) \ Γ) + (μ.prod μ).real Bx +
            (μ.prod μ).real (Prod.swap ⁻¹' Bx) :=
          add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ 26 / 10 ^ 15 + 2 / 10 ^ 14 := by
          rw [hBxs]
          have := two_exp_neg32
          linarith
  have hq1 : √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) ≤ 465 / 10 ^ 6 :=
    sqrt_sqrt_le_of (by norm_num) (hH1.trans (by norm_num))
  have hPo : μ.real Ωᶜ ≤ 9126 / 10 ^ 9 := by
    have h := omega_compl_le hn0 c (t0 := 5) (z0 := 14) (by norm_num) (by norm_num)
    exact h.trans Po_le
  have hq2 : √(μ.real Ωᶜ) ≤ 3021 / 10 ^ 6 :=
    sqrt_le_of_sq' (by norm_num) (hPo.trans (by norm_num))
  have hX4 := BstLean.Part181.Xi4_SXM22 hn hτ hθ0 hθ1 hθh hX
  have hX40 : 0 ≤ Xi4 A₁ A₂ c τ := by
    unfold Xi4; positivity
  rw [hH0, Real.sqrt_zero, Real.sqrt_zero, add_zero] at hmain
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hS0 : 0 ≤ normSq v := normSq_nonneg v
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hS0)
  -- the scalar inequality
  have hf : √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ) ≤ 3486 / 10 ^ 6 := by linarith
  have hf0 : 0 ≤ √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ) := by positivity
  have hXf : Xi4 A₁ A₂ c τ * (√(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ)) ≤
      11 / 10 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n * (3486 / 10 ^ 6) :=
    mul_le_mul hX4 hf hf0 (by
      have : 0 ≤ θh := by linarith
      positivity)
  have hE : 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * (582 / 1000) * (10182 / 10000 * (thetaC c τ / n)) +
      (n : ℝ) * (582 / 1000) * (thetaC c τ / n / (1 - rm)) * 0 +
      (n : ℝ) * (582 / 1000) * (thetaC c τ / n / (1 - rm)) * 0) ≤
      582 / 1000 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n := by
    rw [hmR]; simp only [mul_zero, add_zero]
    have e : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (582 / 1000) * (10182 / 10000 * (thetaC c τ / n))) =
        582 / 1000 * (10182 / 10000) * thetaC c τ * (2 / (n : ℝ)) / n := by
      field_simp
    rw [e]
    have : 0 < (2 / (n : ℝ)) / n := by positivity
    have h2 : 582 / 1000 * (10182 / 10000) * thetaC c τ ≤ 582 / 1000 * (10182 / 10000) * θh := by
      nlinarith
    calc 582 / 1000 * (10182 / 10000) * thetaC c τ * (2 / (n : ℝ)) / n
        = 582 / 1000 * (10182 / 10000) * thetaC c τ * ((2 / (n : ℝ)) / n) := by ring
      _ ≤ 582 / 1000 * (10182 / 10000) * θh * ((2 / (n : ℝ)) / n) :=
          mul_le_mul_of_nonneg_right h2 this.le
      _ = 582 / 1000 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n := by ring
  calc 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * (582 / 1000) * (10182 / 10000 * (thetaC c τ / n)) +
        (n : ℝ) * (582 / 1000) * (thetaC c τ / n / (1 - rm)) * 0 +
        (n : ℝ) * (582 / 1000) * (thetaC c τ / n / (1 - rm)) * 0) +
        Xi4 A₁ A₂ c τ * (√(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ))
      ≤ 582 / 1000 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n +
        11 / 10 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n * (3486 / 10 ^ 6) := add_le_add hE hXf
    _ = (582 / 1000 * (10182 / 10000) * θh +
        11 / 10 * (10182 / 10000) * θh * (3486 / 10 ^ 6)) * (2 / (n : ℝ)) / n := by ring

/-- **The covariance hypothesis `COV_at D c N` on `SXM22 ∩ SCovT`**, for every `N` at least
`0.582·1.0182·θ_hi + 1.1·1.0182·θ_hi·0.003486`. -/
theorem cov_TI (hn : 22000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c) {θh N : ℝ}
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ θh)
    (hθh : θh ≤ 528 / 1000)
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ BstLean.Part181.SXM22 n)
    (hC : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovT n)
    (hN : 582 / 1000 * (10182 / 10000) * θh + 11 / 10 * (10182 / 10000) * θh * (3486 / 10 ^ 6) ≤ N) :
    COV_at D c N := by
  refine cov_at_of_Dq (by omega) D c hτ fun w => ?_
  refine (Dq_TI hn hτ hθ0 hθ1 hθh hX hC w).trans ?_
  have hnR : (0 : ℝ) < n := by
    have : (22000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h0 : 0 ≤ (2 / (n : ℝ)) / n * normSq w := by
    have := normSq_nonneg w
    positivity
  calc (582 / 1000 * (10182 / 10000) * θh + 11 / 10 * (10182 / 10000) * θh * (3486 / 10 ^ 6)) *
        (2 / (n : ℝ)) / n * normSq w
      = (582 / 1000 * (10182 / 10000) * θh + 11 / 10 * (10182 / 10000) * θh * (3486 / 10 ^ 6)) *
        ((2 / (n : ℝ)) / n * normSq w) := by ring
    _ ≤ N * ((2 / (n : ℝ)) / n * normSq w) := mul_le_mul_of_nonneg_right hN h0
    _ = N * (2 / (n : ℝ)) / n * normSq w := by ring

end BstLean.Part182

open BstLean.Part182 in
#print axioms Dq_TI
open BstLean.Part182 in
#print axioms cov_TI
