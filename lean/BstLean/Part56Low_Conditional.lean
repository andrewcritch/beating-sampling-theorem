import BstLean.Part56Low_Gaussian
import BstLean.Part56Low_Feature
import BstLean.Part56Low_Heat
import BstLean.Part56Orth_Heat
import BstLean.Part56Low_Split
import BstLean.Part53Laws

namespace BstLean.Part56.LowConditional

open MeasureTheory BstLean.Part29 BstLean.Part36 BstLean.Part41 BstLean.Part53
open LowGaussian LowFeature

variable {n d : ℕ}

private lemma continuous_f (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Continuous (fval k f0 T) := by
  unfold fval contr
  fun_prop

lemma linZ_coeff_smul (s : ℝ) (Z : CoefIdxD n d → ℝ) (ψ : Mono n d → ℝ) :
    linZ (s • Z) ψ = s • linZ Z ψ := by
  classical
  funext a
  simp only [linZ, colM, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

lemma cvar_resampling (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (s : ℝ) (hs : 0 ≤ s) (v : Fin n → ℝ) (hv : UnitV v)
    (x : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) :
    cvarG k f0 T (s * Real.sqrt (tauR d v x)) (mux (s • Z) v x) =
      (∫ W, fval k f0 T (mapMD (s • (projA v Z + (W - projA v W))) x) ^ 2
        ∂stdGauss (CoefIdxD n d)) -
      (fvA k (heatA k (s ^ 2 * tauR d v x) (TF k f0 T)) (mux (s • Z) v x)) ^ 2 := by
  have hroot : Real.sqrt (nsq (s • Orth.residualFeature (d := d) v x)) =
      s * Real.sqrt (tauR d v x) := by
    rw [Orth.residualFeature_scaled_norm s v hv x,
      Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
  have hm := integral_linear_gaussian (s • Orth.residualFeature (d := d) v x)
    (fval k f0 T) (continuous_f k f0 T) (mux (s • Z) v x)
  have hq := integral_linear_gaussian (s • Orth.residualFeature (d := d) v x)
    (fun y => fval k f0 T y ^ 2) ((continuous_f k f0 T).pow 2) (mux (s • Z) v x)
  rw [hroot] at hm hq
  have hh : (∫ W, fval k f0 T
      (mux (s • Z) v x + linZ W (s • Orth.residualFeature v x))
      ∂stdGauss (CoefIdxD n d)) =
      fvA k (heatA k (s ^ 2 * tauR d v x) (TF k f0 T)) (mux (s • Z) v x) := by
    simp_rw [← fvA_TF]
    rw [Orth.linear_heat_mean k (TF k f0 T) (TF_symm k f0 T hT),
      Orth.residualFeature_scaled_norm s v hv x]
  unfold cvarG
  simp_rw [Orth.resampled_map]
  rw [← hm, ← hq, hh]

lemma resampled_square_integrable (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ)
    (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    Integrable (fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
      fval k f0 T (mapMD (s • (projA v p.1 + (p.2 - projA v p.2))) x) ^ 2)
      ((stdGauss (CoefIdxD n d)).prod (stdGauss (CoefIdxD n d))) := by
  have hi := wick_product_integrable53 k s (TF k f0 T) (TF k f0 T)
    (fun p : Mono n d => phiM x p) (fun p : Mono n d => phiM x p)
  have hi' : Integrable (fun Z : CoefIdxD n d → ℝ =>
      fval k f0 T (mapMD (s • Z) x) ^ 2) (stdGauss (CoefIdxD n d)) := by
    simpa only [fvA_TF, Orth.map_linear, linZ_coeff_smul, pow_two] using hi
  exact (Orth.resampling_measurePreserving (LowSplit.propSplit56 d) v hv).integrable_comp_of_integrable hi'

lemma resampled_square_integral (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ)
    (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    (∫ Z, ∫ W, fval k f0 T (mapMD (s • (projA v Z + (W - projA v W))) x) ^ 2
      ∂stdGauss (CoefIdxD n d) ∂stdGauss (CoefIdxD n d)) =
      ∫ Z, fval k f0 T (mapMD (s • Z) x) ^ 2 ∂stdGauss (CoefIdxD n d) := by
  have hi := resampled_square_integrable (d := d) k f0 T s v hv x
  rw [← integral_prod _ hi]
  have hp := Orth.resampling_measurePreserving (LowSplit.propSplit56 d) v hv
  have hm : AEStronglyMeasurable (fun Z : CoefIdxD n d → ℝ =>
      fval k f0 T (mapMD (s • Z) x) ^ 2) (stdGauss (CoefIdxD n d)) := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_f k f0 T).comp (by
      simp only [Orth.map_linear, linZ_coeff_smul]
      unfold linZ colM
      fun_prop)).pow 2
  conv_rhs => rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hm)).symm

lemma cvar_wpair_integral (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (s : ℝ) (hs : 0 ≤ s) (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    (∫ Z, cvarG k f0 T (s * Real.sqrt (tauR d v x)) (mux (s • Z) v x)
      ∂stdGauss (CoefIdxD n d)) =
      wpair k s (TF k f0 T) (TF k f0 T) (fun p : Mono n d => phiM x p)
        (fun p : Mono n d => phiM x p) -
      wpair k s (heatA k (s ^ 2 * tauR d v x) (TF k f0 T))
        (heatA k (s ^ 2 * tauR d v x) (TF k f0 T))
        (anchorFeature (d := d) v x) (anchorFeature (d := d) v x) := by
  classical
  let A := TF k f0 T
  let H := heatA k (s ^ 2 * tauR d v x) A
  let a := anchorFeature (d := d) v x
  have hH : ∀ j, IsSymmT (H j) := error53_heat_symm _ A (TF_symm k f0 T hT)
  have he (Z : CoefIdxD n d → ℝ) :
      mux (s • Z) v x = s • linZ Z a := by
    rw [← anchor_value v x, linZ_coeff_smul]
  have hi1 := (resampled_square_integrable (d := d) k f0 T s v hv x).integral_prod_left
  have hi2 : Integrable (fun Z : CoefIdxD n d → ℝ => fvA k H (mux (s • Z) v x) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
    simpa only [he, pow_two] using wick_product_integrable53 k s H H a a
  simp_rw [cvar_resampling k f0 T hT s hs v hv x]
  change (∫ Z, (∫ W, fval k f0 T
    (mapMD (s • (projA v Z + (W - projA v W))) x) ^ 2 ∂stdGauss (CoefIdxD n d)) -
    fvA k H (mux (s • Z) v x) ^ 2 ∂stdGauss (CoefIdxD n d)) = _
  rw [integral_sub hi1 hi2, resampled_square_integral k f0 T s v hv x]
  have hf := wick_identity53 k s A A (TF_symm k f0 T hT) (TF_symm k f0 T hT)
    (fun p : Mono n d => phiM x p) (fun p : Mono n d => phiM x p)
  have hh := wick_identity53 k s H H hH hH a a
  simp_rw [he]
  simpa only [A, H, a, fvA_TF, Orth.map_linear, linZ_coeff_smul, pow_two] using
    congrArg₂ (fun a b : ℝ => a - b) hf hh

lemma wpair_residual_difference (k : ℕ) (s : ℝ) (A : Tens n)
    (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    wpair k s A A (fun p : Mono n d => phiM x p) (fun p : Mono n d => phiM x p) -
      wpair k s (heatA k (s ^ 2 * tauR d v x) A) (heatA k (s ^ 2 * tauR d v x) A)
        (anchorFeature (d := d) v x) (anchorFeature (d := d) v x) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * s ^ (2 * c) *
        frob (heatA k (s ^ 2 * phiSq d x) A c) *
        (phiSq d x ^ c - nsq (anchorFeature (d := d) v x) ^ c) := by
  classical
  let a := anchorFeature (d := d) v x
  have hcomp (c : ℕ) :
      heatA k (s ^ 2 * nsq a) (heatA k (s ^ 2 * tauR d v x) A) c =
        heatA k (s ^ 2 * phiSq d x) A c := by
    rw [FloorHeat.heatA_add]
    congr 2
    rw [full_norm_split v hv x]
    ring
  have hfull : (∑ p : Mono n d, phiM x p * phiM x p) = phiSq d x := by
    simp only [phiSq, pow_two]
  have hanc : (∑ p : Mono n d, a p * a p) = nsq a := by
    simp only [nsq, pow_two]
  unfold wpair
  change (∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * s ^ (2 * c) *
    tinner (heatA k (s ^ 2 * phiSq d x) A c) (heatA k (s ^ 2 * phiSq d x) A c) *
    (∑ p : Mono n d, phiM x p * phiM x p) ^ c) -
    (∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * s ^ (2 * c) *
    tinner (heatA k (s ^ 2 * nsq a) (heatA k (s ^ 2 * tauR d v x) A) c)
      (heatA k (s ^ 2 * nsq a) (heatA k (s ^ 2 * tauR d v x) A) c) *
      (∑ p : Mono n d, a p * a p) ^ c) = _
  simp_rw [hfull, hanc, hcomp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [tinner, frob, pow_two]
  ring

lemma cvar_energy_integral (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (s : ℝ) (hs : 0 ≤ s) (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    (∫ Z, cvarG k f0 T (s * Real.sqrt (tauR d v x)) (mux (s • Z) v x)
      ∂stdGauss (CoefIdxD n d)) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * s ^ (2 * c) *
        frob (heatA k (s ^ 2 * phiSq d x) (TF k f0 T) c) *
        (phiSq d x ^ c - nsq (anchorFeature (d := d) v x) ^ c) := by
  rw [cvar_wpair_integral k f0 T hT s hs v hv x,
    wpair_residual_difference k s (TF k f0 T) v hv x]

lemma residual_power_difference (c : ℕ) (hc : 1 ≤ c)
    (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    tauR d v x ^ c ≤ phiSq d x ^ c - nsq (anchorFeature (d := d) v x) ^ c := by
  have ht : 0 ≤ tauR d v x := tauR_nonneg56 d v x
  have hb : 0 ≤ nsq (anchorFeature (d := d) v x) :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hp := pow_add_pow_le ht hb (show c ≠ 0 by omega)
  rw [← full_norm_split v hv x] at hp
  linarith


end BstLean.Part56.LowConditional
