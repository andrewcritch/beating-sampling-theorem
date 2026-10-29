import BstLean.Part182Cov21

/-!
# Part 182 (file `Cov21M`): the covariance bound at `n ≥ 21 000` for the TI-lite constant `λ = 0.72`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the event and covariance parts of `Cov21` with `λ = 0.72` (the value a Lean proof of
Lemma TI without the Davidson–Szarek lower bound is expected to give), `δ = 10⁻¹⁸`, `ε = 10⁻⁵`, the
bad-pair threshold `10⁻¹³`, and `f = 0.000690 + 0.003021 = 0.003711`. The geometry
(`GeoT21`, `geoT21_holds`), `Ew_le_21` and `rminus_lt21` are reused from `Cov21`.

* `SCovT21M n`, **`SCovT21M_ret_charge`** (charge `10⁻⁵` given `TI_hyp n 0.383 0.641 0.72 10⁻¹⁸`).
* **`Dq_TI21M`**, **`cov_TI21M`**: `N_cov = 0.72·1.0186·θ_hi + 1.102·1.0186·θ_hi·0.003711`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nrm jacT Xi4 nuA)

variable {n : ℕ}

/-- **The covariance event of the window**: outside the window, or the pair mass of the bad pairs
(wide sets `(5, 14, 8)`, `λ = 0.72`) is at most `10⁻¹³`. -/
def SCovT21M (n : ℕ) : Set (AgFam n) :=
  {k | ¬ winT k.1.1 k.1.2} ∪ SCov n 5 14 8 (72 / 100) (1 / 10 ^ 13)

theorem measurableSet_SCovT21M (n : ℕ) : MeasurableSet (SCovT21M n) := by
  have hw : MeasurableSet {k : AgFam n | winT k.1.1 k.1.2} :=
    (measurableSet_le measurable_const measurable_thetaC_key21).inter
      (measurableSet_le measurable_thetaC_key21 measurable_const)
  exact hw.compl.union (measurableSet_SCov _ _ _ _ _)

/-- **The charge of `SCovT21M` at one `(c, τ)`**, given the two-input hypothesis. -/
theorem SCovT21M_charge (hn : 1 ≤ n) (hgeo : GeoT21 n)
    (hTI : TI_hyp n (383 / 1000) (641 / 1000) (72 / 100) (1 / 10 ^ 18))
    (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SCovT21M n} ≤ 1 / 10 ^ 5 := by
  by_cases hw : winT c τ
  · have h := SCov_charge (t0 := 5) (z0 := 14) (t1 := 8) (lam := 72 / 100) hn c τ
      (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 18) (by norm_num : (0 : ℝ) < 1 / 10 ^ 5)
      (hgeo c τ hτ hw) hTI
    have e : (1 / 10 ^ 18 : ℝ) / (1 / 10 ^ 5) = 1 / 10 ^ 13 := by norm_num
    rw [e] at h
    refine le_trans (measureReal_mono (fun θ hθ => ?_) (measure_ne_top _ _)) h
    intro hS
    exact hθ (Or.inr hS)
  · have e : {θ | ((c, τ), θ) ∉ SCovT21M n} = ∅ := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl hw
    rw [e, measureReal_empty]
    norm_num

/-- **The charge of `SCovT21M` for the retained data** of the paper's design. -/
theorem SCovT21M_ret_charge (hn : 21000 ≤ n) (hgeo : GeoT21 n)
    (hTI : TI_hyp n (383 / 1000) (641 / 1000) (72 / 100) (1 / 10 ^ 18))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SCovT21M n))ᶜ ≤
      1 / 10 ^ 5 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SCovT21M n) (by norm_num)
    (fun c τ hτ => SCovT21M_charge (by omega) hgeo hTI c τ hτ)

/-- **The quadratic form of `D` on `SXM22 ∩ SCovT21M`** (single-level weighted Schur test):
`Dq v ≤ (0.585·1.0186·θ_hi + 1.102·1.0186·θ_hi·0.003711)·(γ_A/n)·|v|²` for `n ≥ 22 000` and
`0.46 ≤ θ ≤ θ_hi ≤ 0.528`. -/
theorem Dq_TI21M (hn : 21000 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hX : ((c, τ), (A₁, A₂)) ∈ SXM21 n) (hC : ((c, τ), (A₁, A₂)) ∈ SCovT21M n)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ (72 / 100 * (10186 / 10000) * θh +
      1102 / 1000 * (10186 / 10000) * θh * (3711 / 10 ^ 6)) * (2 / (n : ℝ)) / n * normSq v := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn0 : 0 < n := by omega
  have hnR : (21000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < n := by linarith
  have hθlt : thetaC c τ < 1 := by linarith
  have hc : c ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθlt
  set μ := stdGauss (Fin n) with hμ
  set Ω := OmegaS c 5 14 with hΩd
  set Γ := GammaS c 5 14 8 with hΓd
  set key : AgFam n := ((c, τ), (A₁, A₂)) with hkey
  set Bx : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | (key, p) ∈ badSet n 5 14 8 (72 / 100)} with hBxd
  have hBxm : MeasurableSet Bx := measurable_prodMk_left (measurableSet_badSet 5 14 8 (72 / 100))
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
      (n : ℝ) * (72 / 100) := by
    intro a b h
    obtain ⟨h1, h2⟩ := h
    have hnb : ¬ pairBad A₁ A₂ (72 / 100) (sphPt (c + τ • a)) (sphPt (c + τ • b)) := by
      intro hb
      exact h2 (Or.inl ⟨h1, hb⟩)
    unfold pairBad at hnb
    exact not_lt.mp hnb
  have hpair₁ : ∀ a b, (a, b) ∈ G → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      kern Set.univ ((n : ℝ) * (72 / 100)) ((n : ℝ) * (72 / 100)) a b := by
    intro a b h
    rw [kern_of_mem (Set.mem_univ _)]
    exact hpair a b h
  -- the weight bounds
  have hr := rminus_lt21 hn (by linarith) (hθ1.trans hθh)
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
  have hEw : ∫ ξ, wN c τ ξ ∂μ ≤ 10186 / 10000 * (thetaC c τ / n) := by
    have h := Ew_le_21 hn c hτ hθ0 (hθ1.trans hθh)
    simpa only [wN, integral_const_mul] using h
  have hPp : ∀ ξ, μ.real {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ (Set.univ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} ≤
      0 := by
    intro ξ
    have e : {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ (Set.univ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} = ∅ := by
      ext ξ'; simp
    rw [e, measureReal_empty]
  have hPs : μ.real (Ω \ Ω) ≤ 0 := by rw [Set.diff_self, measureReal_empty]
  have hmain := Dq_le_kern A₁ A₂ c (by omega) hτ (subset_refl Ω) hΩm hΩm
    (lam₁ := 72 / 100) (lam₀ := 72 / 100) (by norm_num) (by norm_num)
    Set.univ MeasurableSet.univ (fun _ _ _ => Set.mem_univ _) G hGm hGs hpair₁ G hGm hGs hpair
    hEw hWb0 hWb hPp hPs v
  -- the exceptional masses
  have hH0 : ((μ.prod μ).real (Gᶜ ∩ (Ω \ Ω) ×ˢ (Ω \ Ω))) = 0 := by
    rw [Set.diff_self, Set.empty_prod, Set.inter_empty, measureReal_empty]
  have hwin : winT c τ := ⟨hθ0, hθ1.trans hθh⟩
  have hbad : badMass n 5 14 8 (72 / 100) key ≤ 1 / 10 ^ 13 := by
    rcases hC with h | h
    · exact absurd hwin h
    · exact h
  have hBxr : (μ.prod μ).real Bx ≤ 1 / 10 ^ 13 := hbad
  have hBxs : (μ.prod μ).real (Prod.swap ⁻¹' Bx) = (μ.prod μ).real Bx := by
    rw [Measure.real, Measure.real,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage hBxm.nullMeasurableSet]
  have hout := pairs_out_gamma hn0 c (t0 := 5) (z0 := 14) (t1 := 8) (by norm_num) (by norm_num)
  have hH1 : (μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω) ≤ 26 / 10 ^ 15 + 2 / 10 ^ 13 := by
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
      _ ≤ 26 / 10 ^ 15 + 2 / 10 ^ 13 := by
          rw [hBxs]
          have := two_exp_neg32
          linarith
  have hq1 : √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) ≤ 690 / 10 ^ 6 :=
    sqrt_sqrt_le_of (by norm_num) (hH1.trans (by norm_num))
  have hPo : μ.real Ωᶜ ≤ 9126 / 10 ^ 9 := by
    have h := omega_compl_le hn0 c (t0 := 5) (z0 := 14) (by norm_num) (by norm_num)
    exact h.trans Po_le
  have hq2 : √(μ.real Ωᶜ) ≤ 3021 / 10 ^ 6 :=
    sqrt_le_of_sq' (by norm_num) (hPo.trans (by norm_num))
  have hX4 := Xi4_SXM21 hn hτ hθ0 hθ1 hθh hX
  have hX40 : 0 ≤ Xi4 A₁ A₂ c τ := by
    unfold Xi4; positivity
  rw [hH0, Real.sqrt_zero, Real.sqrt_zero, add_zero] at hmain
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hS0 : 0 ≤ normSq v := normSq_nonneg v
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hS0)
  -- the scalar inequality
  have hf : √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ) ≤ 3711 / 10 ^ 6 := by linarith
  have hf0 : 0 ≤ √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ) := by positivity
  have hXf : Xi4 A₁ A₂ c τ * (√(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ)) ≤
      1102 / 1000 * (10186 / 10000) * θh * (2 / (n : ℝ)) / n * (3711 / 10 ^ 6) :=
    mul_le_mul hX4 hf hf0 (by
      have : 0 ≤ θh := by linarith
      positivity)
  have hE : 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * (72 / 100) * (10186 / 10000 * (thetaC c τ / n)) +
      (n : ℝ) * (72 / 100) * (thetaC c τ / n / (1 - rm)) * 0 +
      (n : ℝ) * (72 / 100) * (thetaC c τ / n / (1 - rm)) * 0) ≤
      72 / 100 * (10186 / 10000) * θh * (2 / (n : ℝ)) / n := by
    rw [hmR]; simp only [mul_zero, add_zero]
    have e : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (72 / 100) * (10186 / 10000 * (thetaC c τ / n))) =
        72 / 100 * (10186 / 10000) * thetaC c τ * (2 / (n : ℝ)) / n := by
      field_simp
    rw [e]
    have : 0 < (2 / (n : ℝ)) / n := by positivity
    have h2 : 72 / 100 * (10186 / 10000) * thetaC c τ ≤ 72 / 100 * (10186 / 10000) * θh := by
      nlinarith
    calc 72 / 100 * (10186 / 10000) * thetaC c τ * (2 / (n : ℝ)) / n
        = 72 / 100 * (10186 / 10000) * thetaC c τ * ((2 / (n : ℝ)) / n) := by ring
      _ ≤ 72 / 100 * (10186 / 10000) * θh * ((2 / (n : ℝ)) / n) :=
          mul_le_mul_of_nonneg_right h2 this.le
      _ = 72 / 100 * (10186 / 10000) * θh * (2 / (n : ℝ)) / n := by ring
  calc 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * (72 / 100) * (10186 / 10000 * (thetaC c τ / n)) +
        (n : ℝ) * (72 / 100) * (thetaC c τ / n / (1 - rm)) * 0 +
        (n : ℝ) * (72 / 100) * (thetaC c τ / n / (1 - rm)) * 0) +
        Xi4 A₁ A₂ c τ * (√(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ))
      ≤ 72 / 100 * (10186 / 10000) * θh * (2 / (n : ℝ)) / n +
        1102 / 1000 * (10186 / 10000) * θh * (2 / (n : ℝ)) / n * (3711 / 10 ^ 6) := add_le_add hE hXf
    _ = (72 / 100 * (10186 / 10000) * θh +
        1102 / 1000 * (10186 / 10000) * θh * (3711 / 10 ^ 6)) * (2 / (n : ℝ)) / n := by ring

/-- **The covariance hypothesis `COV_at D c N` on `SXM22 ∩ SCovT21M`**, for every `N` at least
`0.585·1.0186·θ_hi + 1.102·1.0186·θ_hi·0.003711`. -/
theorem cov_TI21M (hn : 21000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c) {θh N : ℝ}
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ θh)
    (hθh : θh ≤ 528 / 1000)
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM21 n)
    (hC : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovT21M n)
    (hN : 72 / 100 * (10186 / 10000) * θh + 1102 / 1000 * (10186 / 10000) * θh * (3711 / 10 ^ 6) ≤ N) :
    COV_at D c N := by
  refine cov_at_of_Dq (by omega) D c hτ fun w => ?_
  refine (Dq_TI21M hn hτ hθ0 hθ1 hθh hX hC w).trans ?_
  have hnR : (0 : ℝ) < n := by
    have : (21000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h0 : 0 ≤ (2 / (n : ℝ)) / n * normSq w := by
    have := normSq_nonneg w
    positivity
  calc (72 / 100 * (10186 / 10000) * θh + 1102 / 1000 * (10186 / 10000) * θh * (3711 / 10 ^ 6)) *
        (2 / (n : ℝ)) / n * normSq w
      = (72 / 100 * (10186 / 10000) * θh + 1102 / 1000 * (10186 / 10000) * θh * (3711 / 10 ^ 6)) *
        ((2 / (n : ℝ)) / n * normSq w) := by ring
    _ ≤ N * ((2 / (n : ℝ)) / n * normSq w) := mul_le_mul_of_nonneg_right hN h0
    _ = N * (2 / (n : ℝ)) / n * normSq w := by ring

end BstLean.Part182

open BstLean.Part182 in
#print axioms cov_TI21M
open BstLean.Part182 in
#print axioms SCovT21M_ret_charge
