import BstLean.Part106Sphere

/-!
# Part 106: what the spread of the stand-in is

Paper source: `delegations/answers/oaW2-opus-prover.md`, Section 2, "What `sd_ν` is".

Gaussian version of `W` with fixed coefficients `b0` of degree `0` and `1`; `R` the coefficients
of degree `2` to `d`. For bounded measurable `φ`:

`sd_ν² = E_R sd_μ² + E_R (E_μ φ − E_ν φ)²` (`sdNu_decomp`), and so
`(1 − λ_0)·sd_ν² ≤ E_R sd_μ² ≤ sd_ν²` (`sdNu_bounds`).

So `sd_ν²` is the mean of the realized variance `sd_μ² = Var_{μ_W} φ` over the coefficients of `W`
that the program does not read, up to the factor `1 − λ_0`. This is a statement about the mean
over `R`; it is NOT a lower bound of the realized spread for most `W`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

variable {N n d : ℕ}

lemma muW_prob (hN : 1 ≤ N) (W : CoefIdx N n d → ℝ) : IsProbabilityMeasure (muW W) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  unfold muW
  exact (Measure.isProbabilityMeasure_map_iff (measurable_muMap W).aemeasurable).mpr inferInstance

/-- **The spread of the stand-in is the root mean square of the realized spread, plus the mean
squared error of the stand-in mean**:
`Var_ν φ = E_R Var_{μ_W} φ + E_R (E_{μ_W} φ − E_ν φ)²`. -/
theorem sdNu_decomp (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (b0 : CoefIdx N n d → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ c, Var[φ; muW (mixW b0 c)] ∂bwGauss N n d σ +
        ∫ c, (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2 ∂bwGauss N n d σ =
      Var[φ; nuW b0 (tauOf d σ)] := by
  have := nuW_prob hN b0 (tauOf d σ)
  set Bν := ∫ x, φ x ∂nuW b0 (tauOf d σ) with hB
  have hψ : BM (fun x => (φ x - Bν) ^ 2) := (hφ.sub (BM.const Bν)).sq
  have h1 := thm1_mean hN hd σ b0 hψ
  rw [← variance_eq_integral hφ.meas.aemeasurable] at h1
  have h2 : ∀ c, ∫ x, (φ x - Bν) ^ 2 ∂muW (mixW b0 c) =
      Var[φ; muW (mixW b0 c)] + (∫ x, φ x ∂muW (mixW b0 c) - Bν) ^ 2 := by
    intro c
    have := muW_prob hN (mixW b0 c)
    exact int_sq_shift (muW (mixW b0 c)) hφ Bν
  have bA : BM (fun c : CoefIdx N n d → ℝ => ∫ x, (φ x - Bν) ^ 2 ∂muW (mixW b0 c)) :=
    (bm_muInt hN hψ).comp (measurable_mixW_right b0)
  have bS : BM (fun c : CoefIdx N n d → ℝ => (∫ x, φ x ∂muW (mixW b0 c) - Bν) ^ 2) :=
    (((bm_muInt hN hφ).comp (measurable_mixW_right b0)).sub (BM.const Bν)).sq
  have bV : BM (fun c : CoefIdx N n d → ℝ => Var[φ; muW (mixW b0 c)]) := by
    have e : (fun c : CoefIdx N n d → ℝ => Var[φ; muW (mixW b0 c)]) = fun c =>
        ∫ x, (φ x - Bν) ^ 2 ∂muW (mixW b0 c) - (∫ x, φ x ∂muW (mixW b0 c) - Bν) ^ 2 := by
      funext c
      rw [h2 c]
      ring
    rw [e]
    exact bA.sub bS
  rw [← integral_add (bV.integrable _) (bS.integrable _), ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  exact (h2 c).symm

/-- **`(1 − λ_0)·sd_ν² ≤ E_R sd_μ² ≤ sd_ν²`.** -/
theorem sdNu_bounds (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (b0 : CoefIdx N n d → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    (1 - lam0 N d) * Var[φ; nuW b0 (tauOf d σ)] ≤
        ∫ c, Var[φ; muW (mixW b0 c)] ∂bwGauss N n d σ ∧
      ∫ c, Var[φ; muW (mixW b0 c)] ∂bwGauss N n d σ ≤ Var[φ; nuW b0 (tauOf d σ)] := by
  have h := sdNu_decomp hN hd σ b0 hφ
  have h1 := thm1_var hN hd σ b0 hφ
  have h0 : 0 ≤ ∫ c, (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2
      ∂bwGauss N n d σ := integral_nonneg fun c => sq_nonneg _
  constructor <;> linarith

lemma muVar_phiT {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (W : CoefIdx N n d → ℝ) :
    Var[phiAF A F; muW W] = Var[phiT A F; muW W] := by
  unfold muW
  rw [variance_map (continuous_phiAF A F).measurable.aemeasurable
      (measurable_muMap W).aemeasurable,
    variance_map (bm_phiT A F).meas.aemeasurable (measurable_muMap W).aemeasurable]
  congr 1
  funext p
  simp only [Function.comp, phiT_sphProj]

/-- **What `sd_μ²` is**: the variance of `F(A(W(u)/|W(u)|))` over `u` uniform on the unit sphere
of `ℝ^N`. Its square root is the spread `sd` of `MM.md` (the Focus, "Accuracy `ε`"). No theorem
of Part 106 has this spread on the right side of the accuracy inequality. -/
theorem sdMu_eq {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (W : CoefIdx N n d → ℝ) :
    Var[phiAF A F; muW W] =
      Var[fun u : Fin N → ℝ => bwEval F (bwEval A (sphProj (bwEval W u))) 0; uniformSphere N] := by
  unfold muW
  rw [variance_map (continuous_phiAF A F).measurable.aemeasurable
      (measurable_muMap W).aemeasurable]
  rfl

/-- **The spread of the stand-in at `r = 2`, `d_A = 3`**, for `φ = F ∘ A`: with
`Λ = (1/(10n))(1 + 2/n)`, `(1 − Λ)·sd_ν² ≤ E_R sd_μ² ≤ sd_ν²`, where `sd_μ² = Var_{μ_W}(F ∘ A)` is
the realized variance and the mean is over the coefficients of degree `2` to `6` of `W`. -/
theorem sdNu_bounds_r2_dA3 (n dF : ℕ) (hn : 1 ≤ n) (σ : ℝ) (b0 : CoefIdx (2 * n) n 6 → ℝ)
    (A : CoefIdx n n 3 → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    (1 - 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ))) * Var[phiAF A F; nuW b0 (Real.sqrt 5 * σ)] ≤
        ∫ c, Var[phiAF A F; muW (mixW b0 c)] ∂bwGauss (2 * n) n 6 σ ∧
      ∫ c, Var[phiAF A F; muW (mixW b0 c)] ∂bwGauss (2 * n) n 6 σ ≤
        Var[phiAF A F; nuW b0 (Real.sqrt 5 * σ)] := by
  have h := sdNu_bounds (N := 2 * n) (d := 6) (by omega) (by norm_num) σ b0 (bm_phiT A F)
  rw [tauOf_six] at h
  simp_rw [muVar_phiT, nuVar_phiT]
  have hl := lam0_bound n hn
  have hV : 0 ≤ Var[phiT A F; nuW b0 (Real.sqrt 5 * σ)] := variance_nonneg _ _
  refine ⟨le_trans ?_ h.1, h.2⟩
  nlinarith

end BstLean.Part106

#print axioms BstLean.Part106.sdMu_eq
#print axioms BstLean.Part106.sdNu_decomp
#print axioms BstLean.Part106.sdNu_bounds
#print axioms BstLean.Part106.sdNu_bounds_r2_dA3
