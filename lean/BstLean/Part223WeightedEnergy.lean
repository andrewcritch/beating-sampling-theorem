import BstLean.Part223NetworkEnergy

/-! Weighted order18 energy uses one original second-layer matrix for every node. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part202
open BstLean.Part216

noncomputable def energyCoefficient18 (n : ℕ) : ℝ :=
  2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
    BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹)

lemma energyCoefficient18_nonneg (n : ℕ) : 0 ≤ energyCoefficient18 n := by
  have := BstLean.Part202.beta_pos.le
  unfold energyCoefficient18
  positivity

theorem originalNetworkEnergy_weighted18 {n J : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    {σ H Q : ℝ} (hσ : 0 ≤ σ) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hcap : ∀ g, 1 - nodeS c (node g) ^ 2 ≤ Q)
    (htrace : ∀ g, vsig2 c (nodeS c (node g)) ≤
      σ ^ 2 * (1 - nodeS c (node g) ^ 2))
    (h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS c (node g) ^ 2) ^ 12) ∂ν ≤
      ENNReal.ofReal (H ^ 12)) :
    ∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalNetworkEnergyFluct c (node g) M| ^ 18)
      ∂(Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))) ∂ν ≤
      ENNReal.ofReal ((sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) * σ *
        energyCoefficient18 n) ^ 18 * H ^ 12 * Q ^ 6) := by
  let L := sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2)))
  have hL : 0 ≤ L := sqrt_nonneg _
  have hD := energyCoefficient18_nonneg n
  apply weighted_energy18 (fun g => sub_nonneg.mpr (hs g)) hH hQ
    (mul_nonneg (mul_nonneg hL hσ) hD) hcap h12
  intro g
  have hell : |sqrt (tA n * ((1 - nodeS c (node g) ^ 2) * O ^ 2 / ((n : ℝ) - 2)))| ≤
      L * sqrt (1 - nodeS c (node g) ^ 2) := by
    rw [abs_of_nonneg (sqrt_nonneg _)]
    rw [show tA n * ((1 - nodeS c (node g) ^ 2) * O ^ 2 / ((n : ℝ) - 2)) =
      (1 - nodeS c (node g) ^ 2) * (tA n * (O ^ 2 / ((n : ℝ) - 2))) by ring,
      sqrt_mul (sub_nonneg.mpr (hs g))]
    exact le_of_eq (mul_comm _ _)
  have hscale := rowScale_latitude_bound (sub_nonneg.mpr (hs g)) hL hσ hell ((scaledLatitude_trace c (node g)
    (aLat_bdd (by omega) c (hs g) hO hOp)).trans_le (htrace g))
  refine (originalNetworkEnergyFluct_order18 hn c (node g) (hs g) hO hOp).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (mul_nonneg rowScale_nonneg hD)
  calc
    _ ≤ ((L * σ) * (1 - nodeS c (node g) ^ 2)) * energyCoefficient18 n :=
      mul_le_mul_of_nonneg_right hscale hD
    _ = ((L * σ) * energyCoefficient18 n) * (1 - nodeS c (node g) ^ 2) := by ring

#print axioms originalNetworkEnergy_weighted18

theorem originalNetworkEnergy_markov18 {n J : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (ν : Measure (Fin J)) [SFinite ν] (node : Fin J → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    {σ H Q B A : ℝ} (hσ : 0 ≤ σ) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hB : 0 ≤ B) (hA : 0 < A)
    (hcap : ∀ g, 1 - nodeS c (node g) ^ 2 ≤ Q)
    (htrace : ∀ g, vsig2 c (nodeS c (node g)) ≤
      σ ^ 2 * (1 - nodeS c (node g) ^ 2))
    (h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS c (node g) ^ 2) ^ 12) ∂ν ≤
      ENNReal.ofReal (H ^ 12))
    (hprice : (sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) * σ * energyCoefficient18 n) ^ 18 *
      H ^ 12 * Q ^ 6 ≤ B ^ 18) :
    (Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))).real
      {M | ENNReal.ofReal (A ^ 18) <
        ∫⁻ g, ENNReal.ofReal (|originalNetworkEnergyFluct c (node g) M| ^ 18) ∂ν} ≤
      (B / A) ^ 18 := by
  have hm : Measurable (Function.uncurry (fun g => originalNetworkEnergyFluct c (node g))) := by
    apply measurable_from_prod_countable_right
    intro g
    change Measurable (originalNetworkEnergyFluct c (node g))
    rw [originalNetworkEnergyFluct_eq (by omega) c (node g)
      (aLat_bdd (by omega) c (hs g) hO hOp)]
    exact measurable_canonicalEnergyFluct (scaledLatitude_measurable c (node g)) (BstLean.Part170.hB c)
      (BstLean.Part171.measurable_G2.comp (measurable_const.prodMk measurable_id)) _
  apply weighted_moment_charge_real hm (by norm_num : (18 : ℕ) ≠ 0) hB hA
  exact (originalNetworkEnergy_weighted18 hn c ν node hs hO hOp hσ hH hQ hcap htrace h12).trans
    (ENNReal.ofReal_le_ofReal hprice)

#print axioms originalNetworkEnergy_markov18
end BstLean.Part223
