import BstLean.Part204Variable

/-! Part 204: S06 centre distance and scalar bounds from 4096. -/

namespace BstLean.Part204

open Real
open BstLean.Part130 BstLean.Part134 BstLean.Part137 BstLean.Part157 BstLean.Part159
open BstLean.Part141 (aOf)
open BstLean.Part140 (kap1)

/-- The P10f centre package has no unproved program-constant premise. -/
theorem centre_scalar_4096 {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n}
    (hS : θ ∈ goodS n) (hA : θ ∈ goodAo n) :
    2 / (mW n : ℝ) * normSq (bWp θ - bhat θ) ≤
        2 / ((2 * n : ℕ) : ℝ) * (645 / 10 ^ 4 / (mW n : ℝ)) ∧
      0 ≤ qOf n (ccP n) θ ∧ qOf n (ccP n) θ ≤ 1001 / 1000 ∧
      |qOf n (ccP n) θ - 1| ≤
        1002 / 1000 * |SWp θ / 2 - 1| + 407 / 100 * |kapT n - kap1 (2 * n)| := by
  obtain ⟨hq, he⟩ := BstLean.Part204.pap_q hn (BstLean.Part201.constK hn) hS
  exact ⟨BstLean.Part204.bWp_dist hn (BstLean.Part201.constC hn) hS hA,
    Real.sqrt_nonneg _, hq, he⟩

/-- Variable hidden thresholds supply both centre distance and scalar precision. -/
theorem centre_scalar_variable {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n}
    {ε T η : ℝ} (hε : ε ≤ 1 / 1000) (hη : 0 < η)
    (hS : |SWp θ / 2 - 1| ≤ ε)
    (hA : 2 / (mW n : ℝ) * normSq (aOf 1 θ) ≤ T) :
    2 / (mW n : ℝ) * normSq (bWp θ - bhat θ) ≤
        (2 * (1 + η) * (3212 / 100000) * (1001 / 1000) +
          (1 + 1 / η) * (2 * T + 36) / 10 ^ 17) /
            ((n : ℝ) * (mW n : ℝ)) ∧
      0 ≤ qOf n (ccP n) θ ∧ qOf n (ccP n) θ ≤ 1001 / 1000 ∧
      |qOf n (ccP n) θ - 1| ≤
        1002 / 1000 * ε + 407 / 100 * |kapT n - kap1 (2 * n)| := by
  exact ⟨bWp_dist_variable hn (BstLean.Part201.constC hn) hε hη hS hA,
    pap_q_variable hn hε hS⟩

end BstLean.Part204

#print BstLean.Part204.centre_scalar_4096
#print BstLean.Part204.centre_scalar_variable
#print axioms BstLean.Part204.centre_scalar_4096
#print axioms BstLean.Part204.centre_scalar_variable
