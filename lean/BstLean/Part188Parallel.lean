import BstLean.Part188Interfaces
import BstLean.Part188R160Lib

/-! The existing parallel projection bound supplies the actual WF centre interface. -/

namespace BstLean.Part188

open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154
open BstLean.Part157 BstLean.Part160

variable {n : ℕ}

theorem parallelCentre_of_projection (hn : 1 ≤ n) (D : Design n) (c : Ret n) {xi : ℝ}
    (hxi : 0 ≤ xi) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hp : |(∑ j, (muStand D c - D.bA c.1 c.2.1.1) j * D.bA c.1 c.2.1.1 j) /
      nrm (D.bA c.1 c.2.1.1)| ≤ √xi) : ParallelCentre D c xi := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set b := D.bA c.1 c.2.1.1
  have hbN : 0 < nrm b := Real.sqrt_pos.mpr hb
  have hsN : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have he : √(centreEnergy D c) = nrm b / √(n : ℝ) := by
    unfold centreEnergy
    rw [Real.sqrt_div (normSq_nonneg b)]
    rfl
  have hdot : (∑ j, muStand D c j * b j) - normSq b =
      ∑ j, (muStand D c - b) j * b j := by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have e : (∑ j, muStand D c j * b j) / (√(n : ℝ) * nrm b) - nrm b / √(n : ℝ) =
      ((∑ j, (muStand D c - b) j * b j) / nrm b) / √(n : ℝ) := by
    rw [← hdot, ← nrm_sq b]
    field_simp
    <;> ring
  refine ⟨hxi, ?_⟩
  rw [centreCoordinate_mean hn, he]
  change |(∑ j, muStand D c j * b j) / (√(n : ℝ) * nrm b) - nrm b / √(n : ℝ)| ≤ _
  rw [e, abs_div, abs_of_pos hsN, Real.sqrt_div hxi]
  exact div_le_div_of_nonneg_right hp hsN.le

/-- The same event supplies a parallel error smaller than the full centre error. -/
theorem parallelCentre_GoodC16 (hn : 16200 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (c : Ret n) (hτ : 0 < D.tau0 c)
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c)) :
    ParallelCentre D c (282 / 10000) := by
  obtain ⟨_, hp, _, hb, _⟩ := Base160_R.centre16 hn hτ hθ0 hθ1 hG
  have hb' : 0 < normSq (D.bA c.1 c.2.1.1) := by rw [hD c]; exact hb
  refine parallelCentre_of_projection (by omega) D c (by norm_num) hb' ?_
  rw [← hD c] at hp
  have hmA : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < √(2 / (mA n : ℝ)) := by rw [hmA]; positivity
  have he : (282 / 10000 : ℝ) * (2 / (n : ℝ)) / n =
      (2 / (mA n : ℝ)) * (282 / 10000) := by rw [hmA]; field_simp
  rw [he, Real.sqrt_mul (by positivity), abs_mul, abs_of_pos hs] at hp
  exact le_of_mul_le_mul_left hp hs

end BstLean.Part188
