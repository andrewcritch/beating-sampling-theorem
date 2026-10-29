import BstLean.Part185All

/-!
# Part 186 (file `Core`): the two-level Schur bound with a core pair set

No proof is left open; no `native_decide` or `axiom` is used.

Paper: Part 04, Proposition `t7:p04:certificate` (two levels of input sets). Part 182 used one
level (`Ω(5, 14)`, `Γ(5, 14, 8)`, one constant `λ`). Here the inner level is the core set
`Ω₁ = Ω(t₀, z₀) ⊆ Ω(5, 14)` with the core pairs `Γ_c = Γ(t₀, z₀, t₁)`: core pairs have a narrower
window of `x·x'`, so a smaller pair constant `λ₁`; the other pairs keep `λ₀`.

* **`Dq_core`**: on the two bad-pair mass bounds (`badMass` of the core pairs at `λ₁` and of the wide
  pairs at `λ₀`), with `E w ≤ K_e θ/n`:
  `Dq v ≤ (2/m)(nλ₁K_eθ/n·n/n … )` — see the statement: the main term `λ₁K_eθ`, the off-core
  rows `λ₀ W_b (2e^{−t₁²/2})`, the off-core inputs `λ₀ W_b (2e^{−t₀²/2} + 2e^{−z₀})`, and `Ξ₄`
  times the exceptional masses.
-/

namespace BstLean.Part186

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nrm jacT Xi4 nuA)
open BstLean.Part182

variable {n : ℕ}

lemma omegaS_mono {c : Fin n → ℝ} {t0 z0 t0' z0' : ℝ} (ht : t0 ≤ t0') (_hz0 : 0 ≤ z0) (hz : z0 ≤ z0') :
    OmegaS c t0 z0 ⊆ OmegaS c t0' z0' := by
  intro ξ ⟨h1, h2, h3⟩
  have hs : √((n : ℝ) * z0) ≤ √((n : ℝ) * z0') :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _))
  refine ⟨h1.trans ht, ?_, ?_⟩
  · linarith
  · linarith

lemma gPlus_mono {z0 z0' : ℝ} (_hz0 : 0 ≤ z0) (hz : z0 ≤ z0') : gPlus n z0 ≤ gPlus n z0' := by
  unfold gPlus
  have hs : √((n : ℝ) * z0) ≤ √((n : ℝ) * z0') :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _))
  exact Real.sqrt_le_sqrt (by linarith)

lemma gammaS_mono {c : Fin n → ℝ} {t0 z0 t1 t0' z0' t1' : ℝ} (ht : t0 ≤ t0') (hz0 : 0 ≤ z0)
    (hz : z0 ≤ z0') (ht1 : 0 ≤ t1) (ht1' : t1 ≤ t1') :
    GammaS c t0 z0 t1 ⊆ GammaS c t0' z0' t1' := by
  rintro ⟨a, b⟩ ⟨h1, h2, h3⟩
  refine ⟨omegaS_mono ht hz0 hz h1, omegaS_mono ht hz0 hz h2, h3.trans ?_⟩
  have hg0 : 0 ≤ gPlus n z0 := Real.sqrt_nonneg _
  exact mul_le_mul ht1' (gPlus_mono hz0 hz) hg0 (ht1.trans ht1')

/-- **The two-level Schur bound with a core pair set.** -/
theorem Dq_core (hn : 6 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ) (hc : c ≠ 0)
    {t0 z0 t1 lam1 lam0 Ke M1 M0 : ℝ} (ht0 : 0 ≤ t0) (ht05 : t0 ≤ 5) (hz0 : 0 ≤ z0)
    (hz014 : z0 ≤ 14) (ht1 : 0 ≤ t1) (ht18 : t1 ≤ 8) (hl1 : 0 ≤ lam1) (hl0 : 0 ≤ lam0)
    (hr : 2 * 5 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(14 / n) < 1)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hEw : ∫ ξ, BstLean.Part182.wN c τ ξ ∂stdGauss (Fin n) ≤ Ke * (thetaC c τ / n))
    (hb1 : badMass n t0 z0 t1 lam1 ((c, τ), (A₁, A₂)) ≤ M1)
    (hb0 : badMass n 5 14 8 lam0 ((c, τ), (A₁, A₂)) ≤ M0)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ (2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * lam1 * (Ke * (thetaC c τ / n)) +
        (n : ℝ) * lam0 * (thetaC c τ / n /
          (1 - (2 * 5 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(14 / n)))) *
          (2 * exp (-t1 ^ 2 / 2)) +
        (n : ℝ) * lam0 * (thetaC c τ / n /
          (1 - (2 * 5 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(14 / n)))) *
          (2 * exp (-t0 ^ 2 / 2) + 2 * exp (-z0))) +
      Xi4 A₁ A₂ c τ * (√(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M1 + 2 * M0)) +
        √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M0)) +
        √(2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ))))) * normSq v := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn0 : 0 < n := by omega
  set μ := stdGauss (Fin n) with hμ
  set Ω₀ := OmegaS c 5 14 with hΩ₀d
  set Ω₁ := OmegaS c t0 z0 with hΩ₁d
  set Γw := GammaS c 5 14 8 with hΓwd
  set Γc := GammaS c t0 z0 t1 with hΓcd
  set key : AgFam n := ((c, τ), (A₁, A₂)) with hkey
  set Bw : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {p | (key, p) ∈ badSet n 5 14 8 lam0} with hBwd
  set Bc : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {p | (key, p) ∈ badSet n t0 z0 t1 lam1} with hBcd
  have hBwm : MeasurableSet Bw := measurable_prodMk_left (measurableSet_badSet 5 14 8 lam0)
  have hBcm : MeasurableSet Bc := measurable_prodMk_left (measurableSet_badSet t0 z0 t1 lam1)
  have hΩ₀m : MeasurableSet Ω₀ := measurableSet_OmegaS c 5 14
  have hΩ₁m : MeasurableSet Ω₁ := measurableSet_OmegaS c t0 z0
  have hΓwm : MeasurableSet Γw := measurableSet_GammaS c 5 14 8
  have hΓcm : MeasurableSet Γc := measurableSet_GammaS c t0 z0 t1
  have h01 : Ω₁ ⊆ Ω₀ := omegaS_mono ht05 hz0 hz014
  have hcw : Γc ⊆ Γw := gammaS_mono ht05 hz0 hz014 ht1 ht18
  -- the core-pair indicator set
  set C₁ : Set ((Fin n → ℝ) × (Fin n → ℝ)) := Γc ∪ (Ω₁ ×ˢ Ω₁)ᶜ with hC₁d
  have hC₁m : MeasurableSet C₁ := hΓcm.union (hΩ₁m.prod hΩ₁m).compl
  have hC₁s : ∀ a b, (a, b) ∈ C₁ → (b, a) ∈ C₁ := by
    rintro a b (h | h)
    · exact Or.inl (gammaS_swap h)
    · right
      intro hh
      exact h ⟨hh.2, hh.1⟩
  -- level-1 good pairs
  set G₁ := (Γw ∩ Ω₁ ×ˢ Ω₁) \ (Bw ∪ Prod.swap ⁻¹' Bw ∪ (Bc ∪ Prod.swap ⁻¹' Bc)) with hG₁d
  have hG₁m : MeasurableSet G₁ :=
    (hΓwm.inter (hΩ₁m.prod hΩ₁m)).diff ((hBwm.union (measurable_swap hBwm)).union
      (hBcm.union (measurable_swap hBcm)))
  have hG₁s : ∀ a b, (a, b) ∈ G₁ → (b, a) ∈ G₁ := by
    rintro a b ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨gammaS_swap h1, ⟨h2.2, h2.1⟩⟩, ?_⟩
    rintro (((h | h) | (h | h)))
    · exact h3 (Or.inl (Or.inr h))
    · exact h3 (Or.inl (Or.inl h))
    · exact h3 (Or.inr (Or.inr h))
    · exact h3 (Or.inr (Or.inl h))
  have hpair₁ : ∀ a b, (a, b) ∈ G₁ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      kern C₁ ((n : ℝ) * lam1) ((n : ℝ) * lam0) a b := by
    rintro a b ⟨⟨h1, h2⟩, h3⟩
    by_cases hc1 : (a, b) ∈ Γc
    · rw [kern_of_mem (Or.inl hc1)]
      have hnb : ¬ pairBad A₁ A₂ lam1 (sphPt (c + τ • a)) (sphPt (c + τ • b)) := by
        intro hb
        exact h3 (Or.inr (Or.inl ⟨hc1, hb⟩))
      unfold pairBad at hnb
      exact not_lt.mp hnb
    · have hnC : (a, b) ∉ C₁ := by
        rintro (h | h)
        · exact hc1 h
        · exact h h2
      rw [kern_of_notMem hnC]
      have hnb : ¬ pairBad A₁ A₂ lam0 (sphPt (c + τ • a)) (sphPt (c + τ • b)) := by
        intro hb
        exact h3 (Or.inl (Or.inl ⟨h1, hb⟩))
      unfold pairBad at hnb
      exact not_lt.mp hnb
  -- level-0 good pairs
  set G₀ := Γw \ (Bw ∪ Prod.swap ⁻¹' Bw) with hG₀d
  have hG₀m : MeasurableSet G₀ := hΓwm.diff (hBwm.union (measurable_swap hBwm))
  have hG₀s : ∀ a b, (a, b) ∈ G₀ → (b, a) ∈ G₀ := by
    intro a b h
    obtain ⟨h1, h2⟩ := h
    refine ⟨gammaS_swap h1, ?_⟩
    rintro (h3 | h3)
    · exact h2 (Or.inr h3)
    · exact h2 (Or.inl h3)
  have hpair₀ : ∀ a b, (a, b) ∈ G₀ → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      (n : ℝ) * lam0 := by
    intro a b h
    obtain ⟨h1, h2⟩ := h
    have hnb : ¬ pairBad A₁ A₂ lam0 (sphPt (c + τ • a)) (sphPt (c + τ • b)) := by
      intro hb
      exact h2 (Or.inl ⟨h1, hb⟩)
    unfold pairBad at hnb
    exact not_lt.mp hnb
  -- weights
  set rm := 2 * 5 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(14 / n) with hrm
  have hWb : ∀ ξ ∈ Ω₀, BstLean.Part182.wN c τ ξ ≤ thetaC c τ / n / (1 - rm) := by
    intro ξ hξ
    have h := omega_weight hn0 hc hτ (t0 := 5) (z0 := 14) (by norm_num) (by norm_num) hξ
      (by simpa only [hrm, mul_assoc] using hr)
    simpa only [BstLean.Part182.wN, hrm, mul_assoc] using h
  have hθ0 : 0 ≤ thetaC c τ := by
    unfold thetaC
    positivity
  have hWb0 : 0 ≤ thetaC c τ / n / (1 - rm) := by
    have : 0 < 1 - rm := by linarith
    positivity
  have hPp : ∀ ξ, μ.real {ξ' | ξ' ∈ Ω₁ ∧ (ξ, ξ') ∉ C₁} ≤ 2 * exp (-t1 ^ 2 / 2) := by
    intro ξ
    by_cases hξ : ξ ∈ Ω₁
    · refine le_trans (measureReal_mono (fun ξ' hξ' => ?_) (measure_ne_top _ _))
        (gamma_row_le hn0 c hz0 ht1 hξ)
      obtain ⟨h1, h2⟩ := hξ'
      exact ⟨h1, fun h => h2 (Or.inl h)⟩
    · have e : {ξ' | ξ' ∈ Ω₁ ∧ (ξ, ξ') ∉ C₁} = ∅ := by
        ext ξ'
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
        intro _
        right
        intro hh
        exact hξ hh.1
      rw [e, measureReal_empty]
      positivity
  have hPs : μ.real (Ω₀ \ Ω₁) ≤ 2 * exp (-t0 ^ 2 / 2) + 2 * exp (-z0) := by
    refine le_trans (measureReal_mono (fun ξ hξ => hξ.2) (measure_ne_top _ _)) ?_
    exact omega_compl_le hn0 c ht0 hz0
  have hmain := Dq_le_kern A₁ A₂ c (by omega) hτ h01 hΩ₀m hΩ₁m hl1 hl0 C₁ hC₁m hC₁s G₁ hG₁m hG₁s
    hpair₁ G₀ hG₀m hG₀s hpair₀ hEw hWb0 hWb hPp hPs v
  -- the exceptional masses
  have hBw : (μ.prod μ).real Bw ≤ M0 := hb0
  have hBc : (μ.prod μ).real Bc ≤ M1 := hb1
  have hsw : ∀ B : Set ((Fin n → ℝ) × (Fin n → ℝ)), MeasurableSet B →
      (μ.prod μ).real (Prod.swap ⁻¹' B) = (μ.prod μ).real B := by
    intro B hB
    rw [Measure.real, Measure.real,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage hB.nullMeasurableSet]
  have hout := pairs_out_gamma hn0 c (t0 := 5) (z0 := 14) (t1 := 8) (by norm_num) (by norm_num)
  have hH1 : (μ.prod μ).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁) ≤
      2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M1 + 2 * M0 := by
    have hsub : G₁ᶜ ∩ Ω₁ ×ˢ Ω₁ ⊆ ((Ω₀ ×ˢ Ω₀) \ Γw) ∪ (Bw ∪ Prod.swap ⁻¹' Bw) ∪
        (Bc ∪ Prod.swap ⁻¹' Bc) := by
      rintro p ⟨hp1, hp2⟩
      by_cases hpΓ : p ∈ Γw
      · by_contra hn'
        apply hp1
        refine ⟨⟨hpΓ, hp2⟩, ?_⟩
        rintro (h | h)
        · exact hn' (Or.inl (Or.inr h))
        · exact hn' (Or.inr h)
      · exact Or.inl (Or.inl ⟨⟨h01 hp2.1, h01 hp2.2⟩, hpΓ⟩)
    calc (μ.prod μ).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁)
        ≤ (μ.prod μ).real (((Ω₀ ×ˢ Ω₀) \ Γw) ∪ (Bw ∪ Prod.swap ⁻¹' Bw) ∪
            (Bc ∪ Prod.swap ⁻¹' Bc)) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (μ.prod μ).real ((Ω₀ ×ˢ Ω₀) \ Γw) + ((μ.prod μ).real Bw +
            (μ.prod μ).real (Prod.swap ⁻¹' Bw)) +
            ((μ.prod μ).real Bc + (μ.prod μ).real (Prod.swap ⁻¹' Bc)) := by
          refine (measureReal_union_le _ _).trans (add_le_add ?_ (measureReal_union_le _ _))
          exact (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
      _ ≤ 2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M1 + 2 * M0 := by
          rw [hsw Bw hBwm, hsw Bc hBcm]
          linarith
  have hH0 : (μ.prod μ).real (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)) ≤ 2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M0 := by
    have hsub : G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁) ⊆ ((Ω₀ ×ˢ Ω₀) \ Γw) ∪ (Bw ∪ Prod.swap ⁻¹' Bw) := by
      rintro p ⟨hp1, hp2⟩
      by_cases hpΓ : p ∈ Γw
      · by_contra hn'
        apply hp1
        refine ⟨hpΓ, ?_⟩
        intro h
        exact hn' (Or.inr h)
      · exact Or.inl ⟨⟨hp2.1.1, hp2.2.1⟩, hpΓ⟩
    calc (μ.prod μ).real (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁))
        ≤ (μ.prod μ).real (((Ω₀ ×ˢ Ω₀) \ Γw) ∪ (Bw ∪ Prod.swap ⁻¹' Bw)) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (μ.prod μ).real ((Ω₀ ×ˢ Ω₀) \ Γw) + ((μ.prod μ).real Bw +
            (μ.prod μ).real (Prod.swap ⁻¹' Bw)) :=
          (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
      _ ≤ 2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M0 := by
          rw [hsw Bw hBwm]
          linarith
  have hPo : μ.real Ω₀ᶜ ≤ 2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ)) :=
    omega_compl_le hn0 c (t0 := 5) (z0 := 14) (by norm_num) (by norm_num)
  have hX40 : 0 ≤ Xi4 A₁ A₂ c τ := by
    unfold Xi4; positivity
  have hq : √(√((μ.prod μ).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁))) +
      √(√((μ.prod μ).real (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)))) + √(μ.real Ω₀ᶜ) ≤
      √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M1 + 2 * M0)) +
        √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * M0)) +
        √(2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ))) := by
    gcongr
  have hS0 : 0 ≤ normSq v := normSq_nonneg v
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hS0)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hq hX40)

end BstLean.Part186
