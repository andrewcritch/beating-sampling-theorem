import BstLean.Part223Energy
import BstLean.Part223Canonical
import BstLean.Part216NetworkLocation

/-! The complete-row energy bound applies to the installed exact network pass. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part202
open BstLean.Part171 (tA_nonneg)

noncomputable def scaledLatitude {n : ℕ} (c : Ret n) (g : ℕ)
    (v : Fin (n - 1) → ℝ) : Fin (mA n) → ℝ :=
  sqrt (tA n) • aLat c (nodeS c g) v

lemma scaledLatitude_measurable {n : ℕ} (c : Ret n) (g : ℕ) :
    Measurable (scaledLatitude c g) :=
  (measurable_aLat c (nodeS c g)).const_smul (sqrt (tA n))

lemma scaledLatitude_mean {n : ℕ} (c : Ret n) (g : ℕ) :
    vmean (stdGauss (Fin (n - 1))) (scaledLatitude c g) =
      sqrt (tA n) • a1Bar c (nodeS c g) := by
  funext j
  exact integral_const_mul _ _

/-- Multiplying the standard second-layer rows by the He scale gives the actual pass. -/
theorem networkEnergy_eq {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K)
    (M : (Fin (mA n) → Fin (mA n) → ℝ)) :
    exWn (withA2 c (sqrt (tA n) • M)) g =
      matrixEnergyError (stdGauss (Fin (n - 1))) (scaledLatitude c g)
        (G2 (sqrt (vsig2 c (nodeS c g)))) M := by
  erw [exWn_eq hn c g hK]
  unfold matrixEnergyError
  rw [← Finset.sum_sub_distrib, scaledLatitude_mean]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun v => by
      apply congrArg (fun z : ℝ => relu z ^ 2)
      change (∑ k, (sqrt (tA n) * M j k) * aLat c (nodeS c g) v k) =
        ∑ k, M j k * (sqrt (tA n) * aLat c (nodeS c g) v k)
      apply Finset.sum_congr rfl
      intro k _
      ring
  · congr 1
    change (∑ k, (sqrt (tA n) * M j k) * a1Bar c (nodeS c g) k) =
      ∑ k, M j k * (sqrt (tA n) * a1Bar c (nodeS c g) k)
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma scaledLatitude_bound {n : ℕ} (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K) :
    ∀ v, ‖scaledLatitude c g v‖ ≤ sqrt (tA n) * K := by
  intro v
  rw [scaledLatitude, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hK v) (sqrt_nonneg _)

/-- The row trace is the installed first-layer variance table, with its He scale. -/
theorem scaledLatitude_trace {n : ℕ} (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K) :
    covarianceTrace (stdGauss (Fin (n - 1))) (scaledLatitude c g) = vsig2 c (nodeS c g) := by
  have hE : (∫ v, normSq (aLat c (nodeS c g) v) ∂stdGauss (Fin (n - 1))) =
      ∑ i, e1Bar c (nodeS c g) i := by
    have hi : ∀ i, Integrable (fun v => aLat c (nodeS c g) v i ^ 2)
        (stdGauss (Fin (n - 1))) :=
      fun i => int_comp_bdd (measurable_aLat c _) hK ((continuous_apply i).pow 2)
    unfold normSq
    rw [integral_finsetSum _ fun i _ => hi i]
    rfl
  have hT : covarianceTrace (stdGauss (Fin (n - 1))) (scaledLatitude c g) =
      tA n * (∑ i, e1Bar c (nodeS c g) i - normSq (a1Bar c (nodeS c g))) := by
    rw [covarianceTrace_eq_energy (scaledLatitude_measurable c g)
      (scaledLatitude_bound c g hK), scaledLatitude_mean]
    simp_rw [scaledLatitude, normSq_smul, sq_sqrt (tA_nonneg n)]
    rw [integral_const_mul, hE]
    ring
  unfold vsig2
  change _ = max 0 (tA n * _)
  rw [← hT, max_eq_right covarianceTrace_nonneg]

/-- The installed operator bound supplies the covariance premise from dimension three. -/
theorem scaledLatitude_covariance {n : ℕ} (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    (e : Fin (mA n) → ℝ) :
    ∫ v, (e ⬝ᵥ (scaledLatitude c g v -
      vmean (stdGauss (Fin (n - 1))) (scaledLatitude c g))) ^ 2
        ∂stdGauss (Fin (n - 1)) ≤
      (sqrt (tA n * ((1 - nodeS c g ^ 2) * O ^ 2 / ((n : ℝ) - 2)))) ^ 2 * normSq e := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ tA n * ((1 - nodeS c g ^ 2) * O ^ 2 / ((n : ℝ) - 2)) :=
    mul_nonneg (tA_nonneg n) (div_nonneg (mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg _))
      (by linarith))
  rw [sq_sqrt hL, scaledLatitude_mean]
  have he : ∀ v, (e ⬝ᵥ (scaledLatitude c g v - sqrt (tA n) • a1Bar c (nodeS c g))) ^ 2 =
      tA n * (e ⬝ᵥ (aLat c (nodeS c g) v - a1Bar c (nodeS c g))) ^ 2 := by
    intro v
    rw [scaledLatitude, ← smul_sub, dotProduct_smul, smul_eq_mul, mul_pow,
      sq_sqrt (tA_nonneg n)]
  simp_rw [he]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (BstLean.Part173.cov_bound_lat hn c hs hO hOp e)
    (tA_nonneg n)
  simpa only [vmean_aLat, mul_assoc] using h

/-- The reference array contains independent complete rows, with retained plane and fresh
transverse coordinates in each row. The expression is the actual network energy error
minus its conditional mean, with no transverse restriction. -/
theorem networkEnergy_order18 {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (g : ℕ) {K ell : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (scaledLatitude c g v -
      vmean (stdGauss (Fin (n - 1))) (scaledLatitude c g))) ^ 2
        ∂stdGauss (Fin (n - 1)) ≤ ell ^ 2 * normSq e) :
    let S := planeSplit (scaledLatitude_measurable c g) (scaledLatitude_bound c g hK)
      (hB c) ell hCov
    ∫⁻ y, ENNReal.ofReal (|exWn (withA2 c (sqrt (tA n) • assembledMatrix S y)) g -
      (∫ η, exWn (withA2 c (sqrt (tA n) •
          assembledMatrix S (fun j => ((y j).1, η j)))) g
        ∂(Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))))| ^ 18)
      ∂(Measure.pi fun _ : Fin (mA n) =>
        ((stdGauss (Fin 1)).prod (stdGauss (Fin 1))).prod (stdGauss (Fin (mA n)))) ≤
      ENNReal.ofReal ((rowScale (stdGauss (Fin (n - 1))) (scaledLatitude c g) ell *
        (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
          BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))) ^ 18) := by
  dsimp only
  simp_rw [networkEnergy_eq hn c g hK]
  exact matrixEnergyError_order18 _ (scaledLatitude_measurable c g)
    (scaledLatitude_bound c g hK) _ n

/-- The assembled second-layer matrix has the original Gaussian matrix distribution. -/
theorem assembled_secondLayer_distribution {n : ℕ} (c : Ret n) (g : ℕ) {K ell : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (scaledLatitude c g v -
      vmean (stdGauss (Fin (n - 1))) (scaledLatitude c g))) ^ 2
        ∂stdGauss (Fin (n - 1)) ≤ ell ^ 2 * normSq e) :
    let S := planeSplit (scaledLatitude_measurable c g) (scaledLatitude_bound c g hK)
      (hB c) ell hCov
    Measure.map (fun y => sqrt (tA n) • assembledMatrix S y)
      (Measure.pi fun _ : Fin (mA n) =>
        ((stdGauss (Fin 1)).prod (stdGauss (Fin 1))).prod (stdGauss (Fin (mA n)))) =
      gaussMat (mA n) (mA n) (tA n) := by
  dsimp only
  let S := planeSplit (scaledLatitude_measurable c g) (scaledLatitude_bound c g hK)
    (hB c) ell hCov
  have hm : Measurable (assembledMatrix S (N := mA n)) :=
    Measurable.of_eval fun j => S.measurable_assemble.comp (measurable_pi_apply j)
  have hsc : Measure.map (fun M : Fin (mA n) → Fin (mA n) → ℝ => sqrt (tA n) • M)
      (Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))) =
        gaussMat (mA n) (mA n) (tA n) := by
    have he := congrArg (Measure.map (matOf (tA n)))
      (BstLean.Part184.stdGauss_uncurry (mA n))
    have hu : Measurable (Function.uncurry : (Fin (mA n) → Fin (mA n) → ℝ) →
        (Fin (mA n) × Fin (mA n) → ℝ)) :=
      (MeasurableEquiv.curry _ _ ℝ).symm.measurable
    rw [Measure.map_map (measurable_matOf _) hu] at he
    exact he
  have hd := congrArg
    (Measure.map (fun M : Fin (mA n) → Fin (mA n) → ℝ => sqrt (tA n) • M))
    (assembledMatrix_gaussian S (mA n))
  rw [Measure.map_map (measurable_const_smul _) hm] at hd
  exact hd.trans hsc

#print axioms networkEnergy_eq
#print axioms networkEnergy_order18
#print axioms assembled_secondLayer_distribution

noncomputable def originalNetworkEnergyFluct {n : ℕ} (c : Ret n) (g : ℕ)
    (M : (Fin (mA n) → Fin (mA n) → ℝ)) : ℝ :=
  exWn (withA2 c (sqrt (tA n) • M)) g -
    ∫ η, exWn (withA2 c (sqrt (tA n) •
      replaceMatrix (hB c) (vmean (stdGauss (Fin (n - 1))) (scaledLatitude c g)) M η)) g
      ∂(Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n)))

theorem originalNetworkEnergyFluct_eq {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K) :
    originalNetworkEnergyFluct c g = canonicalEnergyFluct (stdGauss (Fin (n - 1)))
      (scaledLatitude c g) (hB c) (G2 (sqrt (vsig2 c (nodeS c g)))) := by
  funext M
  unfold originalNetworkEnergyFluct canonicalEnergyFluct
  simp_rw [networkEnergy_eq hn c g hK]

/-- The actual centred energy supply uses one original standard Gaussian row array.
The first-layer operator premise supplies the covariance; no distribution identity is assumed. -/
theorem originalNetworkEnergyFluct_order18 {n : ℕ} (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O) :
    ∫⁻ M, ENNReal.ofReal (|originalNetworkEnergyFluct c g M| ^ 18)
      ∂(Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))) ≤
      ENNReal.ofReal ((rowScale (stdGauss (Fin (n - 1))) (scaledLatitude c g)
        (sqrt (tA n * ((1 - nodeS c g ^ 2) * O ^ 2 / ((n : ℝ) - 2)))) *
        (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
          BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))) ^ 18) := by
  have hK := aLat_bdd (by omega : 1 ≤ n) c hs hO hOp
  rw [originalNetworkEnergyFluct_eq (by omega) c g hK]
  exact canonicalEnergyFluct_order18 (scaledLatitude_measurable c g)
    (scaledLatitude_bound c g hK) (hB c) _ (scaledLatitude_covariance hn c g hs hO hOp)
    (BstLean.Part171.measurable_G2.comp (measurable_const.prodMk measurable_id)) n

#print axioms originalNetworkEnergyFluct_eq
#print axioms originalNetworkEnergyFluct_order18
end BstLean.Part223
