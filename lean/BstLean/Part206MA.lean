import BstLean.Part198MF
import BstLean.Part206T2

/-! The MF second moment transfers to the actual second-layer centre error.
Inputs share the same first-layer matrix and the same stand-in distribution. -/
namespace BstLean.Part206
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part154

/-- Row integration gives the actual MA second moment with factor two. -/
theorem MA_second_of_row {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {rowBound : ℝ}
    (hi : Integrable (fun z => DF (stdGauss (Fin n)) (fA A c τ) z ^ 2)
      (stdGauss (Fin m)))
    (hRow : (∫ z, DF (stdGauss (Fin n)) (fA A c τ) z ^ 2 ∂stdGauss (Fin m)) ≤ rowBound) :
    Integrable (fun M => dC A M c τ ^ 2) (gaussMat m m (2 / (m : ℝ))) ∧
    (∫ M, dC A M c τ ^ 2 ∂gaussMat m m (2 / (m : ℝ))) ≤ 2 * rowBound := by
  obtain ⟨hiM, heM⟩ := rows_mean hm hi
  have he : (fun M => dC A M c τ ^ 2) =
      fun M => (2 / (m : ℝ)) * ∑ j,
        DF (stdGauss (Fin n)) (fA A c τ)
          ((√(2 / (m : ℝ)))⁻¹ • fun k => M j k) ^ 2 :=
    funext (fun M => dC_sq hm A M c τ)
  rw [he]
  refine ⟨hiM, ?_⟩
  rw [heM]
  exact mul_le_mul_of_nonneg_left hRow (by norm_num : (0 : ℝ) ≤ 2)

/-- The improved MF formula supplies MA for the actual row function. -/
theorem MA_second_from_MF {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {L pg r rG k k3 : ℝ} (H : MFHyp (stdGauss (Fin n)) (fA A c τ) L pg)
    (hV : ∀ x y, BstLean.Part153.nrm (fA A c τ x - fA A c τ y) ≤
      L * BstLean.Part153.nrm (x - y))
    (hr : 0 < r) (hrG : 0 < rG) (hk : 1 < k) (hk3 : 1 < k3)
    (hRatio : L ^ 2 / sF2 (stdGauss (Fin n)) (fA A c τ) ≤ r)
    (hRatioG : L ^ 2 / GamF (stdGauss (Fin n)) (fA A c τ) ≤ rG)
    (hRad : 0 ≤ 1 - 2 * r) (hRadG : 0 ≤ 1 - rG)
    (hgap : 0 < BstLean.Part194.gap 2 r k)
    (hgapG : 0 < BstLean.Part194.gap 1 rG k3) :
    let μ := stdGauss (Fin n)
    let f := fA A c τ
    (∫ M, dC A M c τ ^ 2 ∂gaussMat m m (2 / (m : ℝ))) ≤ 2 *
      (K0 * √(k * k3) * hsF μ f / (sF μ f * √(GamF μ f)) +
        sF μ f / 4 * (sF μ f * BstLean.Part194.tail 2 r k / √k +
          √(GamF μ f) * BstLean.Part194.tail 1 rG k3 / √k3) +
        L ^ 2 * (1 / π * (2 * (L ^ 2 / sF2 μ f) +
          (6863 / 10000) * (GamBarF μ f / sF2 μ f) * nuR (L ^ 2 / sF2 μ f)) + pg) +
        sF2 μ f * QB (L ^ 2 / sF2 μ f) pg) := by
  exact (MA_second_of_row hm A c τ H.DF_sq_int
    (BstLean.Part198.MF_second_moment H hV hr hrG hk hk3 hRatio hRatioG
      hRad hRadG hgap hgapG)).2

#print axioms MA_second_of_row
#print axioms MA_second_from_MF
end BstLean.Part206
