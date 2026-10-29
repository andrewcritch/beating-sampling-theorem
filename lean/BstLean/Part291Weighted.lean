import BstLean.Part229Network
import BstLean.Part188Frame
import BstLean.Part188Mass

/-! Weighted frame assembly for the actual stand-in network.
The projected and cap-energy integrals remain explicit analytic inputs.
The derivative, extension, integrability and covariance steps use Part229. -/
namespace BstLean.BlueprintLow

open Real Set MeasureTheory Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part153 BstLean.Part157
open BstLean.Part160 BstLean.Part188 BstLean.Part229

noncomputable def residualTest {n : ℕ} (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) (ξ : Fin n → ℝ) : ℝ :=
  ∑ j, res (D.bA c.1 c.2.1.1) (hStand D c ξ) j * v j

noncomputable def coordinateVector {n : ℕ} (D : Design n) (c : Ret n) :
    Fin (mA n) → ℝ :=
  (√(n : ℝ) * nrm (D.bA c.1 c.2.1.1))⁻¹ • D.bA c.1 c.2.1.1

lemma coordinate_as_sphereScalar {n : ℕ} (D : Design n) (c : Ret n) :
    sphereScalar c.1.2 (D.tau0 c)
      (hiddenScalar c.2.1.1.1 c.2.1.1.2 1 (coordinateVector D c)) =
      centreCoordinate D c := by
  funext ξ
  simp only [sphereScalar, hiddenScalar, coordinateVector, centreCoordinate,
    dotProduct, Pi.smul_apply, smul_eq_mul, hStand, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma residual_as_sphereScalar {n : ℕ} (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) :
    sphereScalar c.1.2 (D.tau0 c)
      (hiddenScalar c.2.1.1.1 c.2.1.1.2 1 (res (D.bA c.1 c.2.1.1) v)) =
      residualTest D c v := by
  funext ξ
  simpa only [sphereScalar, one_smul, residualTest, hStand] using
    hiddenScalar_residual c.2.1.1.1 c.2.1.1.2 1 (D.bA c.1 c.2.1.1) v
      (sphPt (c.1.2 + D.tau0 c • ξ))

/-- Actual capped network covariance, with no derivative or regularity hypothesis. -/
theorem weightedCovariance_from_energies {n : ℕ} (hn : 6 ≤ n)
    (D : Design n) (c : Ret n) (v : Fin (mA n) → ℝ)
    {a d N C : ℝ} (hτ : 0 < D.tau0 c) (hd : 0 < d)
    (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hA : ∫ ξ, projectedEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
      ∂stdGauss (Fin n) ≤ N)
    (hB : ∫ ξ, capEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
      ∂stdGauss (Fin n) ≤ C) :
    Integrable (fun ξ => (weight a d (centreCoordinate D c ξ) * residualTest D c v ξ -
      ∫ ξ', weight a d (centreCoordinate D c ξ') * residualTest D c v ξ'
        ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    (∫ ξ, (weight a d (centreCoordinate D c ξ) * residualTest D c v ξ -
      ∫ ξ', weight a d (centreCoordinate D c ξ') * residualTest D c v ξ'
        ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n)) ≤ (√N + √C) ^ 2 := by
  have h := network_capped_covariance hn c.2.1.1.1 c.2.1.1.2
    (s := 1) (by norm_num) (coordinateVector D c) (D.bA c.1 c.2.1.1) v c.1.2
    hτ hd hN hC
    (by simpa only [coordinate_as_sphereScalar, residual_as_sphereScalar] using hA)
    (by simpa only [coordinate_as_sphereScalar, residual_as_sphereScalar] using hB)
  simpa only [coordinate_as_sphereScalar, residual_as_sphereScalar] using h

lemma integrable_of_abs_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable K
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hK x)

lemma bounded_variance_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x, |f x| ≤ K) :
    Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2) μ := by
  apply integrable_of_abs_bound μ ((hf.sub measurable_const).pow_const 2)
    (K := (K + |∫ y, f y ∂μ|) ^ 2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub (f x) (∫ y, f y ∂μ)).trans
    (add_le_add (hb x) le_rfl)) 2

/-- Boundedness of the residual scalar under the normalized Gaussian input. -/
lemma residualTest_bound {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ Measurable (residualTest D c v) ∧
      ∀ ξ, |residualTest D c v ξ| ≤ K := by
  let w := res (D.bA c.1 c.2.1.1) v
  let K := hiddenScalarConstant c.2.1.1.1 c.2.1.1.2 1 w
  have hK : 0 ≤ K := hiddenScalarConstant_nonneg _ _ (by norm_num) _
  refine ⟨K, hK, ?_, ?_⟩
  · rw [← residual_as_sphereScalar]
    exact sphereScalar_measurable _ _ hK (hiddenScalar_lip _ _ (by norm_num) _)
  · intro ξ
    rw [← residual_as_sphereScalar]
    exact hiddenScalar_bound _ _ (by norm_num) _ _
      (by rw [nrm]; rw [normSq_sphPt hn]; norm_num)

/-- The hypotheses here are scalar analytic bounds for each unit test. They are not
numerical certificates or event charges. In particular WS and GB are not assumed
to follow from an unweighted covariance cap. -/
structure WeightedTestBounds {n : ℕ} (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) (a d N C xi Ncov Vpsi W Beta : ℝ) : Prop where
  projected : ∫ ξ, projectedEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
    ∂stdGauss (Fin n) ≤ N
  cap : ∫ ξ, capEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
    ∂stdGauss (Fin n) ≤ C
  weight_mean : ∫ ξ, weight a d (centreCoordinate D c ξ) ∂stdGauss (Fin n) ≤ W
  weight_variance : ∫ ξ, (weight a d (centreCoordinate D c ξ) -
    ∫ ξ', weight a d (centreCoordinate D c ξ') ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ Vpsi
  residual_variance : ∫ ξ, (residualTest D c v ξ -
    ∫ ξ', residualTest D c v ξ' ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ Ncov
  residual_mean : |∫ ξ, residualTest D c v ξ ∂stdGauss (Fin n)| ≤ √xi
  mass : (n : ℝ) * (stdGauss (Fin n)).real
    {ξ | ¬ goodInput a d (inputEnergy D c ξ) (centreCoordinate D c ξ)} ≤ Beta

/-- Weighted frame assembly from the actual projected and cap energies. -/
theorem weighted_unit_test {n : ℕ} (hn : 6 ≤ n) (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1)
    {a d N C xi Ncov Vpsi W Beta : ℝ}
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hd : 0 < d) (hN : 0 ≤ N) (hC : 0 ≤ C) (hNc : 0 ≤ Ncov)
    (hV : 0 ≤ Vpsi) (hW : 0 ≤ W)
    (S : WeightedTestBounds D c v a d N C xi Ncov Vpsi W Beta) :
    (n : ℝ) * ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * v j) ^ 2
      ∂stdGauss (Fin n) ≤
        (√N + √C) ^ 2 + (W * √xi + √(Vpsi * Ncov)) ^ 2 + Beta := by
  have hp : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let μ := stdGauss (Fin n)
  let p := fun ξ => weight a d (centreCoordinate D c ξ)
  let z := residualTest D c v
  have hpm : Measurable p := measurable_weight _ _ (measurable_centreCoordinate D c)
  have hp0 : ∀ ξ, 0 ≤ p ξ := fun _ => Real.sqrt_nonneg _
  have hpB : ∀ ξ, |p ξ| ≤ (√d)⁻¹ := fun ξ => by
    rw [abs_of_nonneg (hp0 ξ)]; exact weight_le hd
  have hPi : Integrable p μ := integrable_of_abs_bound μ hpm hpB
  obtain ⟨K, hK, hzm, hzB⟩ := residualTest_bound (by omega) D c v
  have hZi : Integrable z μ := integrable_of_abs_bound μ hzm hzB
  have hPZi : Integrable (fun ξ => p ξ * z ξ) μ := by
    apply integrable_of_abs_bound μ (hpm.mul hzm) (K := (√d)⁻¹ * K)
    intro ξ
    change |p ξ * z ξ| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hpB ξ) (hzB ξ) (abs_nonneg _) (by positivity)
  have hPZ2i : Integrable (fun ξ => (p ξ * z ξ) ^ 2) μ := by
    apply integrable_of_abs_bound μ ((hpm.mul hzm).pow_const 2) (K := ((√d)⁻¹ * K) ^ 2)
    intro ξ
    change |(p ξ * z ξ) ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_mul]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul (hpB ξ) (hzB ξ) (abs_nonneg _) (by positivity)) 2
  have hP2i := bounded_variance_integrable μ hpm (by positivity) hpB
  have hZ2i := bounded_variance_integrable μ hzm hK hzB
  have hcov := (weightedCovariance_from_energies hn D c v hτ hd hN hC
    S.projected S.cap).2
  have h := WF_of_weighted_covariance μ (hStand D c) (BstLean.Part160.measurable_hStand D c)
    (D.bA c.1 c.2.1.1) v (inputEnergy D c) (centreCoordinate D c)
    (by exact_mod_cast (show 0 < n by omega)) hd hv
    (measurableSet_goodInput (measurable_inputEnergy D c) (measurable_centreCoordinate D c) a d)
    (network_residual_energy (by omega) D c hb.ne') hNc hV
    hPi hZi hPZi hPZ2i hP2i hZ2i S.weight_variance S.residual_variance S.residual_mean
    hcov S.mass
  apply h.trans
  have hmean0 : 0 ≤ ∫ ξ, p ξ ∂μ := integral_nonneg hp0
  have hm : (∫ ξ, p ξ ∂μ) * √xi + √(Vpsi * Ncov) ≤
      W * √xi + √(Vpsi * Ncov) :=
    add_le_add (mul_le_mul_of_nonneg_right S.weight_mean (sqrt_nonneg _)) le_rfl
  exact add_le_add (add_le_add le_rfl
    (pow_le_pow_left₀ (by positivity) hm 2)) le_rfl

end BstLean.BlueprintLow
