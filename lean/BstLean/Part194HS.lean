import BstLean.Part154Event

/-! Improved HS formulas and transfer through the original centre event.
The sharpened covariance moment supply remains an explicit hypothesis. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150
open BstLean.Part154

noncomputable def S0 (n : ℕ) : ℝ := n - 1 - 2 * √(12 * ((n : ℝ) - 1))
noncomputable def axialC (θ : ℝ) : ℝ := 2 * (1 - θ) / (π * θ)
noncomputable def J0 (n : ℕ) (θ : ℝ) : ℝ :=
  (1 - exp (-12)) * (1 - 1 / S0 n) / √(1 + 2 * axialC θ * n / S0 n)
noncomputable def qHS (n : ℕ) (θ : ℝ) : ℝ := 1 - J0 n θ / 2
noncomputable def CH (n : ℕ) (θ v : ℝ) : ℝ :=
  (1 + v) * ((qHS n θ) ^ 2 + 1 / n) + (1 + 1 / v) * (3 / (16 * n)) +
    4 * (1 + 2 / n) / n

/-- The chi-square cutoff has a positive reserve throughout the frontier interval. -/
theorem S0_gt_one {n : ℕ} (hn : 64 ≤ n) : 1 < S0 n := by
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : 0 ≤ √(12 * ((n : ℝ) - 1)) := sqrt_nonneg _
  have hs2 : √(12 * ((n : ℝ) - 1)) ^ 2 = 12 * ((n : ℝ) - 1) :=
    sq_sqrt (by linarith)
  have hpoly : 0 < ((n : ℝ) - 2) ^ 2 - 48 * ((n : ℝ) - 1) := by
    nlinarith [sq_nonneg ((n : ℝ) - 64)]
  unfold S0
  nlinarith

/-- The axial lower bound and its complementary coefficient have explicit positive gaps. -/
theorem J0_bounds {n : ℕ} (hn : 64 ≤ n) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < J0 n θ ∧ J0 n θ < 1 ∧ 1 / 2 < qHS n θ ∧ qHS n θ < 1 := by
  have hs := S0_gt_one hn
  have hc : 0 ≤ axialC θ := by
    unfold axialC
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hθ1))
      (mul_nonneg pi_pos.le hθ.le)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hden : 1 ≤ √(1 + 2 * axialC θ * n / S0 n) := by
    have hd : 0 ≤ 2 * axialC θ * n / S0 n := by positivity
    have h := sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 2 * axialC θ * n / S0 n by linarith)
    simpa only [sqrt_one] using h
  have he0 : 0 < exp (-12 : ℝ) := exp_pos _
  have he1 : exp (-12 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
  have hs1 : 0 < 1 / S0 n := one_div_pos.mpr (by linarith)
  have hs2 : 1 / S0 n < 1 := (div_lt_one (by linarith : 0 < S0 n)).mpr hs
  have hNum0 : 0 < (1 - exp (-12 : ℝ)) * (1 - 1 / S0 n) :=
    mul_pos (sub_pos.mpr he1) (sub_pos.mpr hs2)
  have hNum1 : (1 - exp (-12 : ℝ)) * (1 - 1 / S0 n) < 1 := by nlinarith
  have hj0 : 0 < J0 n θ := by unfold J0; exact div_pos hNum0 (by linarith)
  have hj1 : J0 n θ < 1 := by
    unfold J0
    apply (div_lt_one (by linarith : 0 < √(1 + 2 * axialC θ * n / S0 n))).mpr
    exact hNum1.trans_le hden
  refine ⟨hj0, hj1, ?_, ?_⟩ <;> unfold qHS <;> linarith

/-- Sum covariance moments without introducing independent copies of input indices. -/
theorem hs_expectation_of_covariance_moments {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ θ v : ℝ) (hv : 0 < v)
    (hi : ∀ i j : Fin (mA n), Integrable
      (fun A : Matrix (Fin (mA n)) (Fin n) ℝ =>
        covF (BstLean.Part29.stdGauss (Fin n)) (fA A c τ) i j ^ 2)
      (gaussMat (mA n) n (2 / n)))
    (hMom : ∀ i j : Fin (mA n),
      (∫ A : Matrix (Fin (mA n)) (Fin n) ℝ,
        covF (BstLean.Part29.stdGauss (Fin n)) (fA A c τ) i j ^ 2
          ∂gaussMat (mA n) n (2 / n)) ≤
        (2 / ((mA n : ℕ) : ℝ)) ^ 2 *
          (τ ^ 4 / n * ((1 + v) * ((qHS n θ) ^ 2 + 1 / n) +
            (1 + 1 / v) * (3 / (16 * n))) +
            if i = j then τ ^ 4 * (4 * (1 + 2 / n)) else 0)) :
    Integrable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => hsH A c τ)
      (gaussMat (mA n) n (2 / n)) ∧
    (∫ A : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A c τ
      ∂gaussMat (mA n) n (2 / n)) ≤ 4 * τ ^ 4 / n * CH n θ v := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  unfold hsH hsF
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  simp_rw [integral_finsetSum _ fun j _ => hi _ j]
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hMom i j).trans ?_
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [hm]
  unfold CH
  apply le_of_eq
  field_simp
  ring

/-- Any improved HS mean bound transfers on the existing event with charge exp(-12). -/
theorem HS_same_event {n : ℕ} (hn : 8 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {B : ℝ}
    (hMean : (∫ A : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A c τ
      ∂gaussMat (mA n) n (2 / n)) ≤ B)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A ∉ BadH n c τ 12) :
    hsH A c τ ≤ (√(√B) + 2 * √24 * √(normSq c + n * τ ^ 2) /
      ((n : ℝ) * √(n : ℝ))) ^ 4 := by
  have hi := (hsH_mean hn c hτ K0_pos.le PRvecAbs_K0).1
  simpa only [show (2 : ℝ) * 12 = 24 by norm_num] using
    EH_bound (by omega : 1 ≤ n) c τ (by norm_num : (0 : ℝ) ≤ 12)
    hi hMean hA

/-- The improved mean bound uses the HS component of the original centre event. -/
theorem HS_on_GoodC {n J : ℕ} (hn : 8 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {B : ℝ}
    (hMean : (∫ A : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A c τ
      ∂gaussMat (mA n) n (2 / n)) ≤ B)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A2 : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hA : (A, A2) ∈ GoodC n J c τ) :
    hsH A c τ ≤ (√(√B) + 2 * √24 * √(normSq c + n * τ ^ 2) /
      ((n : ℝ) * √(n : ℝ))) ^ 4 :=
  HS_same_event hn c hτ hMean hA.2.1

/-- The HS event retains its original conditional complement charge. -/
theorem HS_charge {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    (gaussMat (mA n) n (2 / n)).real (BadH n c τ 12) ≤ exp (-12) :=
  EH_prob hn c τ (by norm_num)

#print axioms S0_gt_one
#print axioms J0_bounds
#print axioms hs_expectation_of_covariance_moments
#print axioms HS_same_event
#print axioms HS_on_GoodC
#print axioms HS_charge
end BstLean.Part194
