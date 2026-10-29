import BstLean.Part239WeightedRA
import BstLean.Part223OriginalBias

/-! Order-104 weighted conditional biases on the original second Agent matrix.
All nodes use the same matrix and the complete second-layer distribution. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part171
open BstLean.Part220 BstLean.Part223 BstLean.Part239

theorem originalBias_weighted104 {n J : ℕ} (hn : 1 ≤ n) (c : Ret n)
    (ν : Measure (Fin J)) [SFinite ν] (node : Fin J → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (hOp : OpB (A1 c) O) (d : Fin J → RAData)
    (hSm : ∀ g, 0 < (d g).Smin)
    (hStat : ∀ g, NodeStat c (node g) (d g).Smin (d g).Smax
      (d g).D (d g).H (d g).V (d g).P)
    {a b e u v w : ℝ}
    (hfa : MomentBound ν 104 (fun g => (d g).f0 n O) a)
    (hfb : MomentBound ν 104 (fun g => (d g).f1 n O) b)
    (hfc : MomentBound ν 104 (fun g => (d g).f2) e)
    (hwa : MomentBound ν 104 (fun g => (d g).w0 n O) u)
    (hwb : MomentBound ν 104 (fun g => (d g).w1 n O) v)
    (hwc : MomentBound ν 104 (fun g => (d g).w2 n O) w) :
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalLocationBias c (node g) M| ^ 104)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤
      ENNReal.ofReal ((n : ℝ) ^ 52 * (mA n : ℝ) ^ 52 *
        (BstLean.Part213.collectedSecond a b e +
          exactCorrection 52 (mA n) * radiusPolynomialRoot104 a b e ^ 2) ^ 52) ∧
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalEnergyBias c (node g) M| ^ 104)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤
      ENNReal.ofReal ((mA n : ℝ) ^ 104 *
        (u + v * sqrt (π / 2) + 2*w +
          exactCorrection 104 (mA n) * radiusPolynomialRoot104 u v w) ^ 104) := by
  have hnode (g : Fin J) := RAData_coefficients_nonneg c (node g) hO (d g) (hStat g)
  have hF (g : Fin J) :
      (∫⁻ M, ENNReal.ofReal (|originalLocationBias c (node g) M| ^ 104)
        ∂gaussMat (mA n) (mA n) (tA n)) ≤
      ENNReal.ofReal ((n : ℝ) ^ 52 * (mA n : ℝ) ^ 52 *
        (BstLean.Part213.collectedSecond ((d g).f0 n O) ((d g).f1 n O) (d g).f2 +
          exactCorrection 52 (mA n) * radiusPolynomialRoot104 ((d g).f0 n O)
            ((d g).f1 n O) (d g).f2 ^ 2) ^ 52) := by
    rw [originalLocationBias_moment]
    simp only [Even.pow_abs (by decide : Even 104)]
    exact conditional_location_RA104_exact hn c (node g) (hs g) hO hOp (hSm g) (hStat g)
      (hnode g).1 (hnode g).2.1 (hnode g).2.2.1 (radiusPolynomial_source_moment104 _ _ _)
  have hW (g : Fin J) :
      (∫⁻ M, ENNReal.ofReal (|originalEnergyBias c (node g) M| ^ 104)
        ∂gaussMat (mA n) (mA n) (tA n)) ≤
      ENNReal.ofReal ((mA n : ℝ) ^ 104 *
        ((d g).w0 n O + (d g).w1 n O * sqrt (π / 2) + 2*(d g).w2 n O +
          exactCorrection 104 (mA n) * radiusPolynomialRoot104 ((d g).w0 n O)
            ((d g).w1 n O) ((d g).w2 n O)) ^ 104) := by
    rw [originalEnergyBias_moment]
    simp only [Even.pow_abs (by decide : Even 104)]
    exact conditional_energy_RA104_exact hn c (node g) (hs g) hO hOp (hSm g) (hStat g)
      (hnode g).2.2.2.1 (hnode g).2.2.2.2.1 (hnode g).2.2.2.2.2
      (radiusPolynomial_source_moment104 _ _ _)
  exact ⟨(lintegral_mono hF).trans (BstLean.Part239.integrated_location_price hfa hfb hfc
    (exactCorrection_nonneg _ _) (by positivity)),
    (lintegral_mono hW).trans (BstLean.Part239.integrated_energy_price hwa hwb hwc
      (exactCorrection_nonneg _ _) (by positivity))⟩

end BstLean.Part292

/-- info: 'BstLean.Part292.originalBias_weighted104' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.originalBias_weighted104
