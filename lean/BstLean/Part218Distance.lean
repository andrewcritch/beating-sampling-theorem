import BstLean.Part218Sixth

/-! The direct distance charge now uses a covariance bound instead of a sixth-moment premise. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part133 BstLean.Part137 BstLean.Part205 BstLean.Part214

noncomputable def sixthConstant (e : ℝ) : ℝ := (√(1 + 2 * e) + √(2 / π)) ^ 3

noncomputable def worldFrobSq {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, (∫ u, centeredFirst M i u * centeredFirst M j u ∂uniformSphere N) ^ 2

/-- The Frobenius quantity is exactly the covariance entry sum used by S08. -/
theorem worldFrobSq_eq {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) :
    worldFrobSq M = ∑ i, ∑ j,
      BstLean.Part139.covV (uniformSphere N) (fun u => reluV (M.mulVec u)) i j ^ 2 := rfl

/-- This is the sharp paper sixth-moment constant, with a dimensionless covariance bound. -/
theorem rowDiscrepancy_sixth_paper {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin N) ℝ) {e : ℝ} (he : 0 ≤ e)
    (hC : worldFrobSq M ≤ (e * worldSigma M ^ 2) ^ 2) :
    √(∫ ξ, rowDiscrepancy M ξ ^ 6 ∂stdGauss (Fin m)) ≤
      worldSigma M ^ 3 * sixthConstant e := by
  have hs : 0 ≤ worldSigma M := by unfold worldSigma sS; positivity
  have h := rowDiscrepancy_sixth hN hm M (F := e * worldSigma M ^ 2) (by positivity) hC
  have heq : worldSigma M ^ 2 + 2 * (e * worldSigma M ^ 2) =
      worldSigma M ^ 2 * (1 + 2 * e) := by ring
  rw [heq, sqrt_mul (sq_nonneg _), sqrt_sq hs] at h
  convert h using 1 <;> dsimp [sixthConstant] <;> ring

lemma sigma_cube_energy {Q s r : ℝ} (hQ : 0 ≤ Q) (hs : 0 ≤ s)
    (hr : 0 ≤ 1 - r) (he : s ^ 2 = Q * (1 - r)) :
    s ^ 3 = Q * √Q * ((1 - r) * √(1 - r)) := by
  have hsqrt : s = √Q * √(1 - r) := by
    rw [← sqrt_mul hQ, ← he, sqrt_sq hs]
  calc
    s ^ 3 = s ^ 2 * s := by ring
    _ = _ := by rw [he, hsqrt]; ring

/-- The normalized supply has exactly the factor required by Part214. -/
theorem rowDiscrepancy_sixth_energy {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin N) ℝ) {e r : ℝ} (he : 0 ≤ e)
    (hr : 0 ≤ 1 - r) (hQ : 0 ≤ firstQ M)
    (hratio : normSq (h1bar M) = firstQ M * r)
    (hC : worldFrobSq M ≤ (e * worldSigma M ^ 2) ^ 2) :
    √(∫ ξ, rowDiscrepancy M ξ ^ 6 ∂stdGauss (Fin m)) ≤
      firstQ M * √(firstQ M) * ((1 - r) * √(1 - r) * sixthConstant e) := by
  have hs : 0 ≤ worldSigma M := by unfold worldSigma sS; positivity
  have heq : worldSigma M ^ 2 = firstQ M * (1 - r) := by
    rw [worldSigma_sq hN hm, hratio]; ring
  have h := rowDiscrepancy_sixth_paper hN hm M he hC
  rw [sigma_cube_energy hQ hs hr heq] at h
  convert h using 1 <;> ring

/-- The distance theorem has no assumed sixth-moment bound. The charged event,
Taylor bound and covariance bound remain explicit first-layer supplies. -/
theorem direct_distance_from_covariance {n : ℕ} (hn : 4096 ≤ n)
    {E : Set (Matrix (Fin (mW n)) (Fin (2 * n)) ℝ)} (hE : MeasurableSet E)
    {ε e r Δ Xc δ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (he : 0 ≤ e) (hr : 0 ≤ 1 - r) (hΔ : 0 ≤ Δ)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + ε) * Δ < Xc)
    (hbad : (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).real Eᶜ ≤ δ)
    (hω : ∀ M ∈ E, |firstOmega M - 1| ≤ ε)
    (hTaylor : ∀ M ∈ E, meanBound (normSq (h1bar M) / firstQ M)
      (worldT M) (worldNu M) ≤ Δ)
    (hratio : ∀ M ∈ E, normSq (h1bar M) = firstQ M * r)
    (hC : ∀ M ∈ E, worldFrobSq M ≤ (e * worldSigma M ^ 2) ^ 2) :
    (BstLean.Part136.hidGauss (2 * n) (mW n)).real (BstLean.Part140.goodDist n Xc)ᶜ ≤
      δ + ((4 * ((2 * n : ℕ) : ℝ) ^ 2 / (mW n : ℝ)) *
        (1 + ε) ^ 2 * √(Δ / 2) * ((1 - r) * √(1 - r) * sixthConstant e)) /
        (Xc - ((2 * n : ℕ) : ℝ) * (1 + ε) * Δ) ^ 2 := by
  have hm : 1 ≤ mW n := by have := BstLean.Part132.mW_ge hn; omega
  have hN : 1 ≤ 2 * n := by omega
  apply direct_distance_from_sixth hn hE hε0 hε1 hΔ
    (by unfold sixthConstant; positivity) hX hbad hω hTaylor
  intro M hM
  have hQ := (energy_window hN hm M hε1 (hω M hM)).1
  exact rowDiscrepancy_sixth_energy hN hm M he hr hQ.le (hratio M hM) (hC M hM)

end BstLean.Part218
#print axioms BstLean.Part218.rowDiscrepancy_sixth_paper
#print axioms BstLean.Part218.direct_distance_from_covariance
