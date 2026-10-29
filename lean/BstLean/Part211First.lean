import BstLean.Part211Moment

/-! The sharp moment estimate for the actual normalized first-layer mean. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part137 (psiS measurable_psiS)
open BstLean.Part150 (hO rhoC thetaC)
open BstLean.Part206 (firstEnergyRoot)

noncomputable def rowMean {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (g : Fin n → ℝ) : ℝ :=
  psiS (τ * √(normSq g)) (g ⬝ᵥ c)

lemma measurable_rowMean {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Measurable (rowMean c τ) := by
  have hd : Measurable (fun g : Fin n → ℝ => g ⬝ᵥ c) := by unfold dotProduct; fun_prop
  exact measurable_psiS.comp ((measurable_const.mul continuous_normSq.measurable.sqrt).prodMk
    hd)

lemma rowMean_homogeneous {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) {r : ℝ}
    (hr : 0 ≤ r) (g : Fin n → ℝ) : rowMean c τ (r • g) = r * rowMean c τ g := by
  unfold rowMean
  rw [normSq_smul, sqrt_mul (sq_nonneg r), sqrt_sq hr, smul_dotProduct, smul_eq_mul,
    show τ * (r * √(normSq g)) = r * (τ * √(normSq g)) by ring,
    psiS_homogeneous hr]

lemma first_row_integral {n m : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) :
    (∫ A, hO A c τ i ^ 2 ∂gaussMat m n (2 / (n : ℝ))) =
      (2 / n) * ∫ g, rowMean c τ g ^ 2 ∂stdGauss (Fin n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm := (measurable_rowMean c τ).pow_const 2
  change (∫ A, rowMean c τ (rowOf i A) ^ 2 ∂gaussMat m n (2 / (n : ℝ))) = _
  rw [← integral_map (measurable_rowOf i).aemeasurable hm.aestronglyMeasurable,
    gaussMat_row, integral_map (measurable_const_smul _).aemeasurable hm.aestronglyMeasurable]
  simp_rw [rowMean_homogeneous c τ (sqrt_nonneg _), mul_pow, sq_sqrt (by positivity : 0 ≤ 2 / (n : ℝ))]
  exact integral_const_mul _ _

/-- The matrix mean reduces to one Gaussian row with its original radial dependence. -/
theorem firstEnergyRoot_row {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ A, firstEnergyRoot A c τ ^ 2 ∂gaussMat (mA n) n (2 / (n : ℝ))) =
      (2 * ∫ g, rowMean c τ g ^ 2 ∂stdGauss (Fin n)) / rhoC c τ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hi := fun i : Fin (mA n) => (BstLean.Part160.hO_sq_mean hn c τ i).1
  have he : ∀ A : Matrix (Fin (mA n)) (Fin n) ℝ, firstEnergyRoot A c τ ^ 2 =
      (∑ i, hO A c τ i ^ 2) / ((n : ℝ) * rhoC c τ ^ 2) := by
    intro A
    unfold firstEnergyRoot
    rw [div_pow, BstLean.Part153.nrm_sq, mul_pow, sq_sqrt hnR.le]
    rfl
  simp_rw [he]
  rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [first_row_integral hn c τ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm]
  field_simp

lemma exists_unit_direction {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) :
    ∃ (u : Fin n → ℝ) (a : ℝ), normSq u = 1 ∧ c = a • u := by
  cases n with
  | zero => omega
  | succ m => exact BstLean.Part153.exists_unit c

theorem rowMean_moment {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    let I := 2 * ∫ g, rowMean c τ g ^ 2 ∂stdGauss (Fin n)
    let K := rhoC c τ ^ 2 * kappa (normSq c / rhoC c τ ^ 2)
    K - 7 * τ ^ 2 ≤ I ∧ I ≤ K + 5 * τ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨u, a, hu, hc⟩ := exists_unit_direction hn c
  have hc2 : normSq c = a ^ 2 := by rw [hc, normSq_smul, hu, mul_one]
  have hs : 0 < τ * √(n : ℝ) := mul_pos hτ (sqrt_pos.mpr hnR)
  have he : ∀ g : Fin n → ℝ,
      psiS ((τ * √(n : ℝ)) * radialRoot g) (a * (g ⬝ᵥ u)) = rowMean c τ g := by
    intro g
    have hs' : √(n : ℝ) * radialRoot g = √(normSq g) := by
      unfold radialRoot
      rw [sqrt_div (normSq_nonneg g)]
      field_simp
    unfold rowMean
    rw [hc, dotProduct_smul, smul_eq_mul, mul_assoc, hs']
  have h := gaussian_smoothing_moment hn hu a hs
  dsimp only at h ⊢
  simp_rw [he] at h
  have hs2 : (τ * √(n : ℝ)) ^ 2 = (n : ℝ) * τ ^ 2 := by
    rw [mul_pow, sq_sqrt hnR.le]
    ring
  rw [hs2, ← hc2, ← BstLean.Part150.rhoC_sqP] at h
  convert h using 1 <;> field_simp <;> ring

/-- The paper's two-sided first-layer estimate, with no retained-window restriction. -/
theorem firstEnergyRoot_moment {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    kappa (1 - thetaC c τ) - 8 * thetaC c τ / n ≤
      (∫ A, firstEnergyRoot A c τ ^ 2 ∂gaussMat (mA n) n (2 / (n : ℝ))) ∧
    (∫ A, firstEnergyRoot A c τ ^ 2 ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤
      kappa (1 - thetaC c τ) + 5 * thetaC c τ / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have he : normSq c / rhoC c τ ^ 2 = 1 - thetaC c τ := by
    unfold thetaC
    rw [eq_sub_iff_add_eq, ← add_div, ← BstLean.Part150.rhoC_sqP]
    exact div_self (ne_of_gt (sq_pos_of_pos hρ))
  obtain ⟨hl, hh⟩ := rowMean_moment hn c hτ
  rw [he] at hl hh
  have hl' := div_le_div_of_nonneg_right hl (sq_nonneg (rhoC c τ))
  have hh' := div_le_div_of_nonneg_right hh (sq_nonneg (rhoC c τ))
  rw [firstEnergyRoot_row hn c hτ]
  have hL : (rhoC c τ ^ 2 * kappa (1 - thetaC c τ) - 7 * τ ^ 2) / rhoC c τ ^ 2 =
      kappa (1 - thetaC c τ) - 7 * thetaC c τ / n := by
    unfold thetaC
    field_simp
  have hU : (rhoC c τ ^ 2 * kappa (1 - thetaC c τ) + 5 * τ ^ 2) / rhoC c τ ^ 2 =
      kappa (1 - thetaC c τ) + 5 * thetaC c τ / n := by
    unfold thetaC
    field_simp
  rw [hL] at hl'
  rw [hU] at hh'
  have hθ := (BstLean.Part150.thetaC_bounds hn c hτ).1.le
  refine ⟨?_, hh'⟩
  have := div_nonneg hθ hnR.le
  simp only [mul_div_assoc] at hl' ⊢
  linarith

#print axioms firstEnergyRoot_row
#print axioms firstEnergyRoot_moment
end BstLean.Part211
