import BstLean.Part291Weighted
import BstLean.Part229Jacobian
import BstLean.Part182SchurI

/-! Identify the actual projected derivative in WF with the weighted network
quadratic form to which the dependent Schur estimate applies. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part153 BstLean.Part157
open BstLean.Part160 BstLean.Part188 BstLean.Part229 BstLean.Part182

theorem projectedEnergy_network_formula {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) {a d : ℝ} (hτ : 0 < D.tau0 c) (hd : 0 < d) :
    (∫ ξ, projectedEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
      ∂stdGauss (Fin n)) =
      ∫ ξ, (wN c.1.2 (D.tau0 c) ξ * weightSq a d (centreCoordinate D c ξ)) *
        normSq (vecMul (res (D.bA c.1 c.2.1.1) v)
          (BJ c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ξ)) ∂stdGauss (Fin n) := by
  have h := network_projected_energy_formula (a := a) hn c.2.1.1.1 c.2.1.1.2
    1 (coordinateVector D c) (D.bA c.1 c.2.1.1) v c.1.2 hτ hd
  simp only [coordinate_as_sphereScalar, residual_as_sphereScalar, one_mul] at h
  apply integral_congr_ae
  filter_upwards [h] with ξ hξ
  rw [hξ, div_pow, nrm_sq]
  unfold wN BJ
  ring

theorem projectedEnergy_from_schur {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {a d N : ℝ} (hτ : 0 < D.tau0 c) (hd : 0 < d) (hN : 0 ≤ N)
    (hSchur : ∀ w : Fin (mA n) → ℝ,
      (∫ ξ, (wN c.1.2 (D.tau0 c) ξ * weightSq a d (centreCoordinate D c ξ)) *
        normSq (vecMul w (BJ c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ξ))
          ∂stdGauss (Fin n)) ≤ N * normSq w)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1) :
    (∫ ξ, projectedEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
      ∂stdGauss (Fin n)) ≤ N := by
  rw [projectedEnergy_network_formula hn D c v hτ hd]
  have h := hSchur (res (D.bA c.1 c.2.1.1) v)
  have hv' : normSq (res (D.bA c.1 c.2.1.1) v) ≤ 1 := by
    simpa only [hv] using normSq_res_le (D.bA c.1 c.2.1.1) v
  exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv' hN)

end BstLean.BlueprintLow
