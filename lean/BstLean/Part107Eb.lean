import BstLean.Part107Ea

/-!
# Part 107 (item 5), second file: Lemma E for a fixed bounded measurable `φ`

* `sample_sq` (a): the mean square over the samples.
* `stepB` (b), `stepC` (c), `lemmaE_fixed`: Lemma E for a fixed `φ`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

variable {N n d : ℕ} {φ : (Fin n → ℝ) → ℝ}

lemma measurable_standIn (W : CoefIdx N n d → ℝ) (τ : ℝ) : Measurable (standIn W τ) :=
  measurable_nuMap W τ

lemma muW_prob (hN : 1 ≤ N) (W : CoefIdx N n d → ℝ) : IsProbabilityMeasure (muW W) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  unfold muW
  exact (Measure.isProbabilityMeasure_map_iff (measurable_muMap W).aemeasurable).2 inferInstance

lemma bm_memLp {α : Type*} [MeasurableSpace α] {F : α → ℝ} (hF : BM F) (μ : Measure α)
    [IsFiniteMeasure μ] : MemLp F 2 μ :=
  (memLp_two_iff_integrable_sq hF.meas.aestronglyMeasurable).2 (hF.sq.integrable μ)

lemma bm_var {α : Type*} [MeasurableSpace α] {F : α → ℝ} (hF : BM F) (μ : Measure α)
    [IsProbabilityMeasure μ] : Var[F; μ] = ∫ x, F x ^ 2 ∂μ - (∫ x, F x ∂μ) ^ 2 := by
  rw [variance_eq_sub (bm_memLp hF μ)]
  rfl

/-- (a) The mean square of `g − c` over the `k` samples of the stand-in. -/
theorem sample_sq (hN : 1 ≤ N) (hφ : BM φ) (W : CoefIdx N n d → ℝ) (τ : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ) :
    ∫ s : Fin k → Prim N n, ((1 / (k : ℝ)) * ∑ i, φ (standIn W τ (s i)) - c) ^ 2
        ∂(Measure.pi fun _ : Fin k => primM N n) =
      Var[φ; nuW W τ] / (k : ℝ) + (∫ x, φ x ∂nuW W τ - c) ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have h := iid_mean_sq (primM N n) (hφ.comp (measurable_standIn W τ)) k hk c
  have e1 : nuW W τ = (primM N n).map (standIn W τ) := rfl
  rw [e1, variance_map hφ.meas.aemeasurable (measurable_standIn W τ).aemeasurable,
    integral_map (measurable_standIn W τ).aemeasurable hφ.meas.aestronglyMeasurable]
  exact h

lemma bm_muVar (hN : 1 ≤ N) (hφ : BM φ) :
    BM (fun W : CoefIdx N n d → ℝ => Var[φ; muW W]) := by
  have e : (fun W : CoefIdx N n d → ℝ => Var[φ; muW W]) =
      fun W => ∫ x, φ x ^ 2 ∂muW W - (∫ x, φ x ∂muW W) ^ 2 := by
    funext W
    have := muW_prob hN W
    exact bm_var hφ _
  rw [e]
  exact (bm_muInt hN hφ.sq).sub (bm_muInt hN hφ).sq

lemma mix_integral (σ : ℝ) {Φ : (CoefIdx N n d → ℝ) → ℝ} (bΦ : BM Φ) :
    ∫ W, Φ W ∂bwGauss N n d σ =
      ∫ b0, ∫ c, Φ (mixW b0 c) ∂bwGauss N n d σ ∂bwGauss N n d σ := by
  have h1 : ∫ W, Φ W ∂bwGauss N n d σ =
      ∫ W, Φ W ∂(((bwGauss N n d σ).prod (bwGauss N n d σ)).map (fun p => mixW p.1 p.2)) := by
    rw [bwGauss_mix σ]
  rw [h1, integral_map measurable_mixW2.aemeasurable bΦ.meas.aestronglyMeasurable,
    integral_prod _ ((bΦ.comp measurable_mixW2).integrable _)]

/-- (b) `E_W [V_ν/k + (B_ν − B_μ)²] ≤ (λ_0 + 1/k) E_W V_ν`. -/
theorem stepB (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (hφ : BM φ) (k : ℕ) :
    ∫ W, (Var[φ; nuW W (tauOf d σ)] / (k : ℝ) +
        (∫ x, φ x ∂nuW W (tauOf d σ) - ∫ x, φ x ∂muW W) ^ 2) ∂bwGauss N n d σ ≤
      (lam0 N d + 1 / (k : ℝ)) * ∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ := by
  have h := thm1_var_full hN hd σ hφ
  have bV := bm_nuVar (d := d) hN hφ (tauOf d σ)
  have bD : BM (fun W : CoefIdx N n d → ℝ =>
      (∫ x, φ x ∂nuW W (tauOf d σ) - ∫ x, φ x ∂muW W) ^ 2) :=
    ((bm_nuInt hN hφ _).sub (bm_muInt hN hφ)).sq
  rw [integral_add ((bV.integrable _).div_const _) (bD.integrable _), integral_div]
  have e : ∫ W, (∫ x, φ x ∂nuW W (tauOf d σ) - ∫ x, φ x ∂muW W) ^ 2 ∂bwGauss N n d σ =
      ∫ W, (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d σ)) ^ 2 ∂bwGauss N n d σ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    ring
  rw [e]
  have : (lam0 N d + 1 / (k : ℝ)) * ∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ =
      (∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ) / (k : ℝ) +
        lam0 N d * ∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ := by ring
  rw [this]
  linarith

/-- (c) `(1 − λ_0) E_W V_ν ≤ E_W V_μ`. -/
theorem stepC (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (hφ : BM φ) :
    (1 - lam0 N d) * ∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ ≤
      ∫ W, Var[φ; muW W] ∂bwGauss N n d σ := by
  set G := bwGauss N n d σ with hG
  set τ := tauOf d σ with hτ
  have bVμ := bm_muVar (d := d) hN hφ
  have bVν := bm_nuVar (d := d) hN hφ τ
  rw [mix_integral σ bVμ, ← integral_const_mul]
  refine integral_mono (((BM.const _).mul bVν).integrable _)
    (((bVμ.comp measurable_mixW2).integral_right G).integrable _) ?_
  intro b0
  have := nuW_prob hN b0 τ
  have hm1 := thm1_mean hN hd σ b0 hφ
  have hm2 := thm1_mean hN hd σ b0 hφ.sq
  have hv := thm1_var hN hd σ b0 hφ
  have bB : BM (fun c : CoefIdx N n d → ℝ => ∫ x, φ x ∂muW (mixW b0 c)) :=
    (bm_muInt hN hφ).comp (measurable_mixW_right b0)
  have bM : BM (fun c : CoefIdx N n d → ℝ => ∫ x, φ x ^ 2 ∂muW (mixW b0 c)) :=
    (bm_muInt hN hφ.sq).comp (measurable_mixW_right b0)
  set Bν := ∫ x, φ x ∂nuW b0 τ with hBν
  have e1 : ∫ c, Var[φ; muW (mixW b0 c)] ∂G =
      ∫ x, φ x ^ 2 ∂nuW b0 τ - ∫ c, (∫ x, φ x ∂muW (mixW b0 c)) ^ 2 ∂G := by
    have : ∀ c : CoefIdx N n d → ℝ, Var[φ; muW (mixW b0 c)] =
        ∫ x, φ x ^ 2 ∂muW (mixW b0 c) - (∫ x, φ x ∂muW (mixW b0 c)) ^ 2 := by
      intro c
      have := muW_prob hN (mixW b0 c)
      exact bm_var hφ _
    simp_rw [this]
    rw [integral_sub (bM.integrable _) (bB.sq.integrable _), hm2]
  have e2 : ∫ c, (∫ x, φ x ∂muW (mixW b0 c) - Bν) ^ 2 ∂G =
      ∫ c, (∫ x, φ x ∂muW (mixW b0 c)) ^ 2 ∂G - Bν ^ 2 := by
    have : ∀ c : CoefIdx N n d → ℝ, (∫ x, φ x ∂muW (mixW b0 c) - Bν) ^ 2 =
        (∫ x, φ x ∂muW (mixW b0 c)) ^ 2 - (2 * Bν) * (∫ x, φ x ∂muW (mixW b0 c)) + Bν ^ 2 := by
      intro c; ring
    simp_rw [this]
    have I1 : Integrable (fun c : CoefIdx N n d → ℝ =>
        (2 * Bν) * (∫ x, φ x ∂muW (mixW b0 c))) G := (bB.integrable _).const_mul _
    have I2 : Integrable (fun c : CoefIdx N n d → ℝ => (∫ x, φ x ∂muW (mixW b0 c)) ^ 2 -
        (2 * Bν) * (∫ x, φ x ∂muW (mixW b0 c))) G := (bB.sq.integrable _).sub I1
    rw [integral_add I2 (integrable_const _), integral_sub (bB.sq.integrable _) I1,
      integral_const_mul, hm1]
    simp
    ring
  have e3 : Var[φ; nuW b0 τ] = ∫ x, φ x ^ 2 ∂nuW b0 τ - Bν ^ 2 := bm_var hφ _
  show (1 - lam0 N d) * Var[φ; nuW b0 τ] ≤ ∫ c, Var[φ; muW (mixW b0 c)] ∂G
  change _ ≤ lam0 N d * Var[φ; nuW b0 τ] at hv
  rw [e1]
  rw [e2] at hv
  nlinarith

/-- **Lemma E for a fixed bounded measurable `φ`**:
`(1 − λ_0) E_W E_s (g − B_μ)² ≤ (λ_0 + 1/k) E_W Var_{μ_W} φ`. -/
theorem lemmaE_fixed (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (hφ : BM φ) (k : ℕ) (hk : 1 ≤ k) :
    (1 - lam0 N d) * ∫ W, ∫ s : Fin k → Prim N n,
        ((1 / (k : ℝ)) * ∑ i, φ (standIn W (tauOf d σ) (s i)) - ∫ x, φ x ∂muW W) ^ 2
        ∂(Measure.pi fun _ : Fin k => primM N n) ∂bwGauss N n d σ ≤
      (lam0 N d + 1 / (k : ℝ)) * ∫ W, Var[φ; muW W] ∂bwGauss N n d σ := by
  simp_rw [sample_sq hN hφ _ _ k hk]
  have hb := stepB hN hd σ hφ k
  have hc := stepC hN hd σ hφ
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hl : 0 ≤ lam0 N d + 1 / (k : ℝ) := add_nonneg (lam0_nonneg hN hd) (by positivity)
  have hV0 : 0 ≤ ∫ W, Var[φ; muW W] ∂bwGauss N n d σ :=
    integral_nonneg fun W => variance_nonneg _ _
  have hL0 : 0 ≤ ∫ W, (Var[φ; nuW W (tauOf d σ)] / (k : ℝ) +
      (∫ x, φ x ∂nuW W (tauOf d σ) - ∫ x, φ x ∂muW W) ^ 2) ∂bwGauss N n d σ :=
    integral_nonneg fun W => add_nonneg (div_nonneg (variance_nonneg _ _) hk'.le) (sq_nonneg _)
  rcases le_or_gt 0 (1 - lam0 N d) with h1 | h1
  · calc _ ≤ (1 - lam0 N d) * ((lam0 N d + 1 / (k : ℝ)) *
          ∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ) := mul_le_mul_of_nonneg_left hb h1
      _ = (lam0 N d + 1 / (k : ℝ)) * ((1 - lam0 N d) *
          ∫ W, Var[φ; nuW W (tauOf d σ)] ∂bwGauss N n d σ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hl
  · exact (mul_nonpos_of_nonpos_of_nonneg h1.le hL0).trans (mul_nonneg hl hV0)

end BstLean.Part107
