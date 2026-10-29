import BstLean.Part206TL
import BstLean.Part160ScMean

/-! First-layer mean-energy concentration at fixed retained World data. -/
namespace BstLean.Part206
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (hO rhoC)
open BstLean.Part153 (nrm)

theorem first_row_mean_lipschitz {n m : ℕ} (hn : 1 ≤ n)
    (A A' : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) :
    (hO A c τ i - hO A' c τ i) ^ 2 ≤
      rhoC c τ ^ 2 * normSq (fun j => A i j - A' i j) := by
  let μ := stdGauss (Fin n)
  let u := fun x : Fin n → ℝ => (A *ᵥ (c + τ • x)) i
  let u' := fun x : Fin n → ℝ => (A' *ᵥ (c + τ • x)) i
  let d := fun j => A i j - A' i j
  have hi := (BstLean.Part150.hO_eq_gauss A c τ i).1
  have hi' := (BstLean.Part150.hO_eq_gauss A' c τ i).1
  have hi2 := (BstLean.Part150.relu_sq_eq_gauss A c τ i).1
  have hi2' := (BstLean.Part150.relu_sq_eq_gauss A' c τ i).1
  have hδ2 : Integrable (fun x => (relu (u x) - relu (u' x)) ^ 2) μ := by
    have hm : Measurable (fun x => (relu (u x) - relu (u' x)) ^ 2) := by
      have hc : Continuous u := by dsimp [u]; fun_prop
      have hc' : Continuous u' := by dsimp [u']; fun_prop
      exact (((continuous_relu.comp hc).sub (continuous_relu.comp hc')).pow 2).measurable
    apply ((hi2.const_mul 2).add (hi2'.const_mul 2)).mono' hm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change (relu (u x) - relu (u' x)) ^ 2 ≤ 2 * relu (u x) ^ 2 + 2 * relu (u' x) ^ 2
    nlinarith [sq_nonneg (relu (u x) + relu (u' x))]
  have he : ∀ x, u x - u' x = d ⬝ᵥ c + τ * (x ⬝ᵥ d) := by
    intro x
    dsimp [u, u', d]
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨hlinI, hlin⟩ := BstLean.Part160.gauss_lin_sq d (d ⬝ᵥ c) τ
  have hj := mean_sq_le_second (hi.sub hi') hδ2
  have hmono := integral_mono hδ2 hlinI (fun x => by
    rw [← he]
    exact BstLean.Part153.relu_sub_sq (u x) (u' x))
  have hmean : (∫ x, relu (u x) - relu (u' x) ∂μ) = hO A c τ i - hO A' c τ i := by
    rw [integral_sub hi hi', ← (BstLean.Part150.hO_eq_gauss A c τ i).2,
      ← (BstLean.Part150.hO_eq_gauss A' c τ i).2]
  change (∫ x, relu (u x) - relu (u' x) ∂μ) ^ 2 ≤
    ∫ x, (relu (u x) - relu (u' x)) ^ 2 ∂μ at hj
  rw [hmean] at hj
  rw [hlin] at hmono
  have hc : (d ⬝ᵥ c) ^ 2 ≤ normSq d * normSq c :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnτ := mul_le_mul_of_nonneg_right hnR (sq_nonneg τ)
  rw [BstLean.Part150.rhoC_sqP]
  have hd := normSq_nonneg d
  have hτ := mul_le_mul_of_nonneg_left hnτ hd
  exact (hj.trans hmono).trans (by dsimp [d] at *; nlinarith)

theorem first_mean_norm_lipschitz {n m : ℕ} (hn : 1 ≤ n)
    (A A' : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    |nrm (hO A c τ) - nrm (hO A' c τ)| ≤
      rhoC c τ * √(∑ i, ∑ j, (A i j - A' i j) ^ 2) := by
  have hs : normSq (hO A c τ - hO A' c τ) ≤
      rhoC c τ ^ 2 * ∑ i, ∑ j, (A i j - A' i j) ^ 2 := by
    unfold normSq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => first_row_mean_lipschitz hn A A' c τ i)
  have hρ : 0 ≤ rhoC c τ := sqrt_nonneg _
  calc _ ≤ nrm (hO A c τ - hO A' c τ) := BstLean.Part153.abs_nrm_sub_le _ _
    _ ≤ √(rhoC c τ ^ 2 * ∑ i, ∑ j, (A i j - A' i j) ^ 2) := sqrt_le_sqrt hs
    _ = _ := by rw [sqrt_mul (sq_nonneg _), sqrt_sq hρ]

noncomputable def firstEnergyRoot {n : ℕ}
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  nrm (hO A c τ) / (√(n : ℝ) * rhoC c τ)

theorem firstEnergyRoot_lipschitz {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A A' : Matrix (Fin (mA n)) (Fin n) ℝ) :
    |firstEnergyRoot A c τ - firstEnergyRoot A' c τ| ≤
      (1 / √(n : ℝ)) * √(∑ i, ∑ j, (A i j - A' i j) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have h := first_mean_norm_lipschitz hn A A' c τ
  unfold firstEnergyRoot
  rw [← sub_div, abs_div, abs_of_pos (mul_pos (sqrt_pos.mpr hnR) hρ),
    div_le_iff₀ (mul_pos (sqrt_pos.mpr hnR) hρ)]
  convert h using 1 <;> field_simp

theorem firstEnergyRoot_deviation {n : ℕ} (hn : 1 ≤ n) :
    √(24 * (2 / (n : ℝ))) * (1 / √(n : ℝ)) = 2 * √12 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : (√(24 * (2 / (n : ℝ))) * (1 / √(n : ℝ))) ^ 2 =
      (2 * √12 / (n : ℝ)) ^ 2 := by
    simp only [mul_pow, div_pow, sq_sqrt (by positivity : 0 ≤ 24 * (2 / (n : ℝ))),
      sq_sqrt hnR.le, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
    ring
  nlinarith [sqrt_nonneg (24 * (2 / (n : ℝ))), sqrt_nonneg (12 : ℝ),
    show 0 ≤ √(24 * (2 / (n : ℝ))) * (1 / √(n : ℝ)) by positivity,
    show 0 ≤ 2 * √12 / (n : ℝ) by positivity]

/-- Each original first-layer mean-threshold event has one conditional payment. -/
theorem firstEnergyRoot_charges {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A | (∫ A, firstEnergyRoot A c τ ∂gaussMat (mA n) n (2 / (n : ℝ))) +
        2 * √12 / (n : ℝ) < firstEnergyRoot A c τ} ≤ exp (-12) ∧
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A | firstEnergyRoot A c τ <
        (∫ A, firstEnergyRoot A c τ ∂gaussMat (mA n) n (2 / (n : ℝ))) -
          2 * √12 / (n : ℝ)} ≤ exp (-12) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hU := BstLean.Part153.conc_upper_strict
    (show 0 ≤ 1 / √(n : ℝ) by positivity) (firstEnergyRoot_lipschitz hn c hτ)
    (show 0 < 2 / (n : ℝ) by positivity) (Lc := 12) (by norm_num)
  have hL := BstLean.Part153.conc_lower_strict
    (show 0 ≤ 1 / √(n : ℝ) by positivity) (firstEnergyRoot_lipschitz hn c hτ)
    (show 0 < 2 / (n : ℝ) by positivity) (Lc := 12) (by norm_num)
  simpa only [show (2 : ℝ) * 12 = 24 by norm_num, firstEnergyRoot_deviation hn] using
    And.intro hU hL

/-- The displayed root is exactly the normalized first-layer mean energy. -/
theorem firstEnergyRoot_sq {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    firstEnergyRoot A c τ ^ 2 =
      (2 / (mA n : ℝ) * normSq (hO A c τ)) / (2 / (n : ℝ) * rhoC c τ ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  unfold firstEnergyRoot
  rw [div_pow, BstLean.Part153.nrm_sq, mul_pow, sq_sqrt hnR.le, hm]
  field_simp

/-- The exact first-layer moment is one normalized two-input kernel integral. -/
theorem firstEnergyRoot_second {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun A => firstEnergyRoot A c τ ^ 2)
      (gaussMat (mA n) n (2 / (n : ℝ))) ∧
    (∫ A, firstEnergyRoot A c τ ^ 2 ∂gaussMat (mA n) n (2 / (n : ℝ))) =
      (∫ z, BstLean.Part160.Kn c τ z ∂((stdGauss (Fin n)).prod (stdGauss (Fin n)))) /
        rhoC c τ ^ 2 := by
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
  refine ⟨(integrable_finsetSum _ (fun i _ => hi i)).div_const _, ?_⟩
  rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [(BstLean.Part160.hO_sq_mean hn c τ _).2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm]
  field_simp

/-- Poincare controls the variance of the actual first-layer root. -/
theorem firstEnergyRoot_variance {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun A => firstEnergyRoot A c τ) (gaussMat (mA n) n (2 / (n : ℝ))) ∧
    (∫ A, firstEnergyRoot A c τ ^ 2 ∂gaussMat (mA n) n (2 / (n : ℝ))) -
      (∫ A, firstEnergyRoot A c τ ∂gaussMat (mA n) n (2 / (n : ℝ))) ^ 2 ≤
        2 / (n : ℝ) ^ 2 := by
  let μ := gaussMat (mA n) n (2 / (n : ℝ))
  let V := fun A => firstEnergyRoot A c τ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hi2 : Integrable (fun A => V A ^ 2) μ := (firstEnergyRoot_second hn c hτ).1
  have hc := BstLean.Part148.matLip_continuous (firstEnergyRoot_lipschitz hn c hτ)
  have hi : Integrable V μ := by
    apply (hi2.add (integrable_const (1 : ℝ))).mono' hc.aestronglyMeasurable
    filter_upwards [] with A
    rw [Real.norm_eq_abs]
    change |V A| ≤ V A ^ 2 + 1
    nlinarith [sq_nonneg (|V A| - 1), sq_abs (V A)]
  obtain ⟨_, hv⟩ := BstLean.Part152.gaussVar_mat_le_sharp
    (show 0 ≤ 1 / √(n : ℝ) by positivity) (firstEnergyRoot_lipschitz hn c hτ)
    (show 0 ≤ 2 / (n : ℝ) by positivity)
  let e := ∫ A, V A ∂μ
  change (∫ A, (V A - e) ^ 2 ∂μ) ≤ (2 / (n : ℝ)) * (1 / √(n : ℝ)) ^ 2 at hv
  have he : (fun A => (V A - e) ^ 2) = fun A => V A ^ 2 - 2 * e * V A + e ^ 2 := by
    funext A
    ring
  rw [he, integral_add (f := fun A => V A ^ 2 - 2 * e * V A) (g := fun _ => e ^ 2)
    (hi2.sub (hi.const_mul _)) (integrable_const _),
    integral_sub (f := fun A => V A ^ 2) (g := fun A => 2 * e * V A)
      hi2 (hi.const_mul _), integral_const_mul, integral_const] at hv
  simp only [probReal_univ, one_smul] at hv
  rw [div_pow, sq_sqrt hnR.le] at hv
  refine ⟨hi, ?_⟩
  change (∫ A, V A ^ 2 ∂μ) - e ^ 2 ≤ _
  change (∫ A, V A ^ 2 ∂μ) - 2 * e * e + e ^ 2 ≤ _ at hv
  convert hv using 1 <;> ring

#print axioms first_row_mean_lipschitz
#print axioms first_mean_norm_lipschitz
#print axioms firstEnergyRoot_lipschitz
#print axioms firstEnergyRoot_deviation
#print axioms firstEnergyRoot_charges
#print axioms firstEnergyRoot_sq
#print axioms firstEnergyRoot_second
#print axioms firstEnergyRoot_variance
end BstLean.Part206
