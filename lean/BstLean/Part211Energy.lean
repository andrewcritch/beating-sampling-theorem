import BstLean.Part211First

/-! First-layer source events and the computed-centre energy junction. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (hO gO bO bT rhoC thetaC epsJ)
open BstLean.Part153 (nrm Pb)
open BstLean.Part206

lemma firstEnergyRoot_nonneg {n : ℕ} (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : 0 ≤ firstEnergyRoot A c τ :=
  div_nonneg (BstLean.Part153.nrm_nonneg _) (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))

def FirstUpper (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | firstEnergyRoot A c τ ≤
    (∫ A, firstEnergyRoot A c τ ∂gaussMat (mA n) n (2 / (n : ℝ))) + 2 * √12 / n}

def FirstLower (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | (∫ A, firstEnergyRoot A c τ ∂gaussMat (mA n) n (2 / (n : ℝ))) - 2 * √12 / n ≤
    firstEnergyRoot A c τ}

theorem first_source_charges {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (FirstUpper n c τ)ᶜ ≤ exp (-12) ∧
    (gaussMat (mA n) n (2 / (n : ℝ))).real (FirstLower n c τ)ᶜ ≤ exp (-12) := by
  simpa only [FirstUpper, FirstLower, compl_setOf, not_le] using firstEnergyRoot_charges hn c hτ

theorem first_upper_on_source {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {q : ℝ} (hq : q ∈ Icc (-1) 1) (hcap : 1 - thetaC c τ ≤ q)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A ∈ FirstUpper n c τ) :
    firstEnergyRoot A c τ ^ 2 ≤ meanRoot n q ^ 2 := by
  have hθ := BstLean.Part150.thetaC_bounds hn c hτ
  have hk := kappa_monotoneOn
    (show 1 - thetaC c τ ∈ Icc (-1) 1 from ⟨by linarith, by linarith⟩) hq hcap
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm := (firstEnergyRoot_moment hn c hτ).2
  have hc := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hθ.2
    (by norm_num : (0 : ℝ) ≤ 5)) hnR.le
  apply first_mean_threshold hn hq (firstEnergyRoot_variance hn c hτ).1
    (firstEnergyRoot_second hn c hτ).1 (by linarith)
    (firstEnergyRoot_nonneg A c τ) hA

theorem first_lower_on_source {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A ∈ FirstLower n c τ)
    (hGuard : 0 ≤ meanLowerRoot n (thetaC c τ)) :
    meanLowerRoot n (thetaC c τ) ^ 2 ≤ firstEnergyRoot A c τ ^ 2 :=
  first_mean_lower_threshold
    (fun A => firstEnergyRoot_nonneg A c τ)
    (firstEnergyRoot_moment hn c hτ).1 (firstEnergyRoot_variance hn c hτ).2 hA hGuard

/-- The first-layer moment premise of TL is discharged on its original source event. -/
theorem TL_from_first_source {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (b : Fin (mA n) → ℝ)
    {gLower gUpper finite q : ℝ} (hg : 0 < gLower) (hu : 0 ≤ gUpper) (hf : 0 ≤ finite)
    (hq : q ∈ Icc (-1) 1) (hcap : 1 - thetaC c τ ≤ q)
    (hLower : (2 / n * rhoC c τ ^ 2) * gLower ≤ gO A c τ)
    (hUpper : gO A c τ ≤ (2 / n * rhoC c τ ^ 2) * gUpper)
    (hDomain : energyRatio n gLower q ≤ 1)
    (hFirst : A ∈ FirstUpper n c τ)
    (hSecond : Pb A c τ M ≤ (∫ M, Pb A c τ M
      ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) +
        √(24 * (2 / (mA n : ℝ)) * gO A c τ))
    (hFinite : √(2 / (mA n : ℝ)) / √(2 / n * rhoC c τ ^ 2) *
      nrm (b - bO A M c τ) ≤ finite / √(n : ℝ)) :
    (2 / (mA n : ℝ)) * normSq b / (2 / n * rhoC c τ ^ 2) ≤
      energyUpper n gLower gUpper finite q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hs : 0 < (2 / n * rhoC c τ ^ 2) := by positivity
  have hm := first_upper_on_source hn c hτ hq hcap hFirst
  rw [firstEnergyRoot_sq hn A c hτ, div_le_iff₀ hs] at hm
  exact TL_on_source_event hn A c τ M b hs hg hu hf hLower hUpper
    (by simpa only [mul_comm] using hm) hDomain hSecond hFinite

noncomputable def energyLower (n : ℕ) (gLower gUpper finite θ : ℝ) : ℝ :=
  (√(gLower * (kappa (meanLowerRoot n θ ^ 2 / gUpper) - 2 / (n : ℝ) ^ 2)) -
    2 * √(12 * gUpper) / n - finite / √(n : ℝ)) ^ 2

/-- The lower energy uses the same first-layer event and the original lower norm event. -/
theorem lower_energy_from_first_source {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (b : Fin (mA n) → ℝ)
    {gLower gUpper finite : ℝ} (hg : 0 < gLower) (hu : 0 < gUpper)
    (hLower : (2 / n * rhoC c τ ^ 2) * gLower ≤ gO A c τ)
    (hUpper : gO A c τ ≤ (2 / n * rhoC c τ ^ 2) * gUpper)
    (hFirst : A ∈ FirstLower n c τ) (hRoot : 0 ≤ meanLowerRoot n (thetaC c τ))
    (hBracket : 0 ≤ kappa (meanLowerRoot n (thetaC c τ) ^ 2 / gUpper) - 2 / (n : ℝ) ^ 2)
    (hSecond : (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      √(24 * (2 / (mA n : ℝ)) * gO A c τ) ≤ Pb A c τ M)
    (hFinite : √(2 / (mA n : ℝ)) / √(2 / n * rhoC c τ ^ 2) *
      nrm (b - bO A M c τ) ≤ finite / √(n : ℝ))
    (hGuard : 0 ≤ √(gLower * (kappa (meanLowerRoot n (thetaC c τ) ^ 2 / gUpper) -
      2 / (n : ℝ) ^ 2)) - 2 * √(12 * gUpper) / n - finite / √(n : ℝ)) :
    energyLower n gLower gUpper finite (thetaC c τ) ≤
      (2 / (mA n : ℝ)) * normSq b / (2 / n * rhoC c τ ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  let scale := 2 / n * rhoC c τ ^ 2
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hG : 0 < gO A c τ := (mul_pos hs hg).trans_le hLower
  have hm := first_lower_on_source hn c hτ hFirst hRoot
  rw [firstEnergyRoot_sq hn A c hτ, le_div_iff₀ hs] at hm
  have hr : meanLowerRoot n (thetaC c τ) ^ 2 / gUpper ≤
      (2 / (mA n : ℝ) * normSq (hO A c τ)) / gO A c τ := by
    rw [div_le_div_iff₀ hu hG]
    have h1 := mul_le_mul_of_nonneg_left hUpper (sq_nonneg (meanLowerRoot n (thetaC c τ)))
    have h2 := mul_le_mul_of_nonneg_right hm hu.le
    nlinarith only [h1, h2]
  have hdev := TL_source_deviation hn (BstLean.Part153.gO_nonneg' A c τ) hs.le hu.le hUpper
  have hEvent : (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      √scale * (2 * √(12 * gUpper) / n) ≤ Pb A c τ M := by linarith
  have hdiv : (√scale * (2 * √(12 * gUpper) / n)) / √scale =
      2 * √(12 * gUpper) / n := by field_simp
  have hmA : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h := lower_energy_actual (one_le_mA hn) A c τ M b hs hG hLower
    (rLower := meanLowerRoot n (thetaC c τ) ^ 2 / gUpper)
    (by have : 0 ≤ meanLowerRoot n (thetaC c τ) ^ 2 / gUpper := by positivity
        linarith) hr (by simpa only [hmA] using hBracket) hEvent hFinite
    (by simpa only [hmA, hdiv] using hGuard)
  simpa only [hmA, hdiv, energyLower] using h

end BstLean.Part211
