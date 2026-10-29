import BstLean.Part105Thm1

/-!
# Part 105: Theorem 1 of round oaW1 — the cases of the north star, the probability form, and the
form with all coefficients random

* `thm1_general`: `W : ℝ^{rn} → ℝⁿ` of degree `r·d_A ≥ 2`, (a) and (b).
* `thm1_r2_dA3`: `r = 2`, `d_A = 3` with the explicit bound `λ_0 ≤ (1/(10n))(1 + 2/n)`.
* `thm1_prob`: the Chebyshev form: `|E_{μ_W} φ − E_{ν_W} φ|² ≤ (λ_0/δ) Var_{ν_W} φ` except with
  probability `δ` over the terms of degree `2` to `d`.
* `thm1_var_full`: the bound (b) in the mean over all coefficients of a Gaussian `W`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part105

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)

variable {N n d : ℕ} {φ : (Fin n → ℝ) → ℝ}

/-- **Theorem 1 (a), (b)** for `W : ℝ^{rn} → ℝⁿ` of degree `r·d_A ≥ 2`. -/
theorem thm1_general (r n dA : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (hd : 2 ≤ r * dA) (σ : ℝ)
    (b0 : CoefIdx (r * n) n (r * dA) → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    (∫ c, (∫ x, φ x ∂muW (mixW b0 c)) ∂bwGauss (r * n) n (r * dA) σ =
        ∫ x, φ x ∂nuW b0 (tauOf (r * dA) σ)) ∧
    ∫ c, (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf (r * dA) σ)) ^ 2
        ∂bwGauss (r * n) n (r * dA) σ ≤
      lam0 (r * n) (r * dA) * Var[φ; nuW b0 (tauOf (r * dA) σ)] := by
  have hN : 1 ≤ r * n := Nat.mul_pos hr hn
  exact ⟨thm1_mean hN hd σ b0 hφ, thm1_var hN hd σ b0 hφ⟩

lemma tauOf_six (σ : ℝ) : tauOf 6 σ = Real.sqrt 5 * σ := by
  unfold tauOf
  norm_num

/-- **Theorem 1 at `r = 2`, `d_A = 3`** (`W : ℝ^{2n} → ℝⁿ` of degree `6`, `τ = √5·σ`), with the
explicit bound of `λ_0`. -/
theorem thm1_r2_dA3 (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (b0 : CoefIdx (2 * n) n 6 → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    (∫ c, (∫ x, φ x ∂muW (mixW b0 c)) ∂bwGauss (2 * n) n 6 σ =
        ∫ x, φ x ∂nuW b0 (Real.sqrt 5 * σ)) ∧
    ∫ c, (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (Real.sqrt 5 * σ)) ^ 2
        ∂bwGauss (2 * n) n 6 σ ≤
      1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) * Var[φ; nuW b0 (Real.sqrt 5 * σ)] := by
  have hN : 1 ≤ 2 * n := by omega
  rw [← tauOf_six]
  refine ⟨thm1_mean hN (by norm_num) σ b0 hφ, (thm1_var hN (by norm_num) σ b0 hφ).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (lam0_bound n hn) (variance_nonneg _ _)

/-! ## Measurability in the coefficients -/

section meas

variable (hN : 1 ≤ N)

include hN in
lemma bm_muInt (hφ : BM φ) : BM (fun W : CoefIdx N n d → ℝ => ∫ x, φ x ∂muW W) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hH : BM (fun p : (Fin N → ℝ) × (CoefIdx N n d → ℝ) => φ (sphProj (bwEval p.2 p.1))) :=
    hφ.comp (measurable_sphProj.comp (measurable_bwEval_comp measurable_snd measurable_fst))
  have h := hH.integral_left (uniformSphere N)
  have e : (fun W : CoefIdx N n d → ℝ => ∫ x, φ x ∂muW W) =
      fun W => ∫ u, φ (sphProj (bwEval W u)) ∂uniformSphere N := by
    funext W
    unfold muW
    rw [integral_map (measurable_muMap W).aemeasurable hφ.meas.aestronglyMeasurable]
  rw [e]
  exact h

lemma measurable_nuMap2 (τ : ℝ) :
    Measurable (fun p : ((Fin N → ℝ) × (Fin n → ℝ)) × (CoefIdx N n d → ℝ) =>
      sphProj (bwEval (mixW p.2 0) p.1.1 + τ • p.1.2)) := by
  have h1 : Measurable (fun p : ((Fin N → ℝ) × (Fin n → ℝ)) × (CoefIdx N n d → ℝ) =>
      bwEval (mixW p.2 0) p.1.1) :=
    measurable_bwEval_comp ((measurable_mixW_left 0).comp measurable_snd)
      (measurable_fst.comp measurable_fst)
  have h2 : Measurable (fun p : ((Fin N → ℝ) × (Fin n → ℝ)) × (CoefIdx N n d → ℝ) =>
      τ • p.1.2) := (measurable_snd.comp measurable_fst).const_smul τ
  exact measurable_sphProj.comp (h1.add h2)

lemma nuW_integral_eq (b0 : CoefIdx N n d → ℝ) (τ : ℝ) {ψ : (Fin n → ℝ) → ℝ} (hψ : Measurable ψ) :
    ∫ x, ψ x ∂nuW b0 τ = ∫ p, ψ (sphProj (bwEval (mixW b0 0) p.1 + τ • p.2))
      ∂((uniformSphere N).prod (stdGauss (Fin n))) := by
  unfold nuW
  rw [integral_map (measurable_nuMap b0 τ).aemeasurable hψ.aestronglyMeasurable]

include hN in
lemma bm_nuInt (hφ : BM φ) (τ : ℝ) :
    BM (fun b0 : CoefIdx N n d → ℝ => ∫ x, φ x ∂nuW b0 τ) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hH := (hφ.comp (measurable_nuMap2 (N := N) (n := n) (d := d) τ)).integral_left
    ((uniformSphere N).prod (stdGauss (Fin n)))
  have e : (fun b0 : CoefIdx N n d → ℝ => ∫ x, φ x ∂nuW b0 τ) = fun b0 =>
      ∫ p, φ (sphProj (bwEval (mixW b0 0) p.1 + τ • p.2))
        ∂((uniformSphere N).prod (stdGauss (Fin n))) := by
    funext b0; exact nuW_integral_eq b0 τ hφ.meas
  rw [e]
  exact hH

include hN in
lemma bm_nuVar (hφ : BM φ) (τ : ℝ) :
    BM (fun b0 : CoefIdx N n d → ℝ => Var[φ; nuW b0 τ]) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hH : BM (fun p : ((Fin N → ℝ) × (Fin n → ℝ)) × (CoefIdx N n d → ℝ) =>
      (φ (sphProj (bwEval (mixW p.2 0) p.1.1 + τ • p.1.2)) - ∫ x, φ x ∂nuW p.2 τ) ^ 2) :=
    ((hφ.comp (measurable_nuMap2 τ)).sub ((bm_nuInt hN hφ τ).comp measurable_snd)).sq
  have h := hH.integral_left ((uniformSphere N).prod (stdGauss (Fin n)))
  have e : (fun b0 : CoefIdx N n d → ℝ => Var[φ; nuW b0 τ]) = fun b0 =>
      ∫ p, (φ (sphProj (bwEval (mixW b0 0) p.1 + τ • p.2)) - ∫ x, φ x ∂nuW b0 τ) ^ 2
        ∂((uniformSphere N).prod (stdGauss (Fin n))) := by
    funext b0
    have := nuW_prob hN b0 τ
    rw [variance_eq_integral hφ.meas.aemeasurable]
    exact nuW_integral_eq b0 τ ((hφ.sub (BM.const _)).sq.meas)
  rw [e]
  exact h

end meas

/-! ## The probability form -/

/-- **Theorem 1, Chebyshev form** (item 4 of the paper statement): for `δ > 0`, the event
`λ_0 · Var_{ν_W} φ < δ · (E_{μ_W} φ − E_{ν_W} φ)²` has probability at most `δ` over the terms of
degree `2` to `d`. -/
theorem thm1_prob (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (b0 : CoefIdx N n d → ℝ) (hφ : BM φ)
    {δ : ℝ} (hδ : 0 < δ) :
    (bwGauss N n d σ).real {c | lam0 N d * Var[φ; nuW b0 (tauOf d σ)] <
      δ * (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2} ≤ δ := by
  set A := lam0 N d * Var[φ; nuW b0 (tauOf d σ)] with hA
  set Y : (CoefIdx N n d → ℝ) → ℝ := fun c =>
    (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2 with hY
  have bY : BM Y := (((bm_muInt hN hφ).comp (measurable_mixW_right b0)).sub (BM.const _)).sq
  have hI : ∫ c, Y c ∂bwGauss N n d σ ≤ A := thm1_var hN hd σ b0 hφ
  have hY0 : ∀ c, 0 ≤ Y c := fun c => sq_nonneg _
  have hI0 : 0 ≤ ∫ c, Y c ∂bwGauss N n d σ := integral_nonneg hY0
  rcases (hI0.trans hI).eq_or_lt with h0 | hpos
  · -- `A = 0`: `Y = 0` almost surely
    have hz : ∫ c, Y c ∂bwGauss N n d σ = 0 := le_antisymm (h0 ▸ hI) hI0
    have hae := (integral_eq_zero_iff_of_nonneg hY0 (bY.integrable _)).mp hz
    have hnull : (bwGauss N n d σ) {c | A < δ * Y c} = 0 := by
      refine measure_mono_null ?_ hae
      intro c hc
      simp only [Set.mem_setOf_eq] at hc
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Pi.zero_apply]
      intro hc0
      rw [hc0, mul_zero, ← h0] at hc
      exact lt_irrefl _ hc
    rw [measureReal_def, hnull]
    simpa using hδ.le
  · have hm := mul_meas_ge_le_integral_of_nonneg (μ := bwGauss N n d σ)
      (Filter.Eventually.of_forall hY0) (bY.integrable _) (A / δ)
    have hsub : {c | A < δ * Y c} ⊆ {c | A / δ ≤ Y c} := by
      intro c hc
      simp only [Set.mem_setOf_eq] at hc ⊢
      rw [div_le_iff₀ hδ]
      linarith
    have hle : (bwGauss N n d σ).real {c | A < δ * Y c} ≤
        (bwGauss N n d σ).real {c | A / δ ≤ Y c} := measureReal_mono hsub
    have h2 : A / δ * (bwGauss N n d σ).real {c | A / δ ≤ Y c} ≤ A := hm.trans hI
    have h3 : (bwGauss N n d σ).real {c | A / δ ≤ Y c} ≤ δ := by
      have hAδ : 0 < A / δ := div_pos hpos hδ
      have := (le_div_iff₀' hAδ).mpr h2
      rwa [div_div_cancel₀ hpos.ne'] at this
    exact hle.trans h3

/-! ## All coefficients random -/

lemma measurable_mixW2 {k q d : ℕ} :
    Measurable (fun p : (CoefIdx k q d → ℝ) × (CoefIdx k q d → ℝ) => mixW p.1 p.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold mixW
  split_ifs
  · exact (measurable_pi_apply i).comp measurable_snd
  · exact (measurable_pi_apply i).comp measurable_fst

lemma nuW_mix (b0 c : CoefIdx N n d → ℝ) (τ : ℝ) : nuW (mixW b0 c) τ = nuW b0 τ := by
  have : mixW (mixW b0 c) 0 = mixW b0 0 := by
    funext i
    unfold mixW
    split_ifs <;> rfl
  unfold nuW
  rw [this]

/-- **Theorem 1 (b) with all coefficients random**: for `W` with the Gaussian version of the
Bombieri–Weyl distribution, `E_W (E_{μ_W} φ − E_{ν_W} φ)² ≤ λ_0 · E_W Var_{ν_W} φ`
(`ν_W` reads only the terms of degree `0` and `1` of `W`). -/
theorem thm1_var_full (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (hφ : BM φ) :
    ∫ W, (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d σ)) ^ 2 ∂bwGauss N n d σ ≤
      lam0 N d * ∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ := by
  set G := bwGauss N n d σ with hG
  set Φ : (CoefIdx N n d → ℝ) → ℝ := fun W =>
    (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d σ)) ^ 2 with hΦ
  have bΦ : BM Φ := ((bm_muInt hN hφ).sub (bm_nuInt hN hφ _)).sq
  have bΦ2 : BM (fun p : (CoefIdx N n d → ℝ) × (CoefIdx N n d → ℝ) => Φ (mixW p.1 p.2)) :=
    bΦ.comp measurable_mixW2
  have e1 : ∫ W, Φ W ∂G = ∫ b0, ∫ c, Φ (mixW b0 c) ∂G ∂G := by
    have h1 : ∫ W, Φ W ∂G = ∫ W, Φ W ∂((G.prod G).map (fun p => mixW p.1 p.2)) := by
      rw [hG, bwGauss_mix σ]
    rw [h1, integral_map measurable_mixW2.aemeasurable bΦ.meas.aestronglyMeasurable,
      integral_prod _ (bΦ2.integrable _)]
  rw [e1, ← integral_const_mul]
  refine integral_mono ((bΦ2.integral_right G).integrable _)
    (((BM.const _).mul (bm_nuVar hN hφ _)).integrable _) ?_
  intro b0
  have h := thm1_var hN hd σ b0 hφ
  simp only [hΦ, nuW_mix]
  exact h

end BstLean.Part105
