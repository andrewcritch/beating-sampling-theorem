import BstLean.Part198Calib

/-! The sharp HS expectation and its transfer through the original centre event. -/
namespace BstLean.Part198
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part194
open BstLean.Part153 (rowLaw)
open BstLean.Part160.MFB

theorem price_constant_tenth : K0 ≤ (1 : ℝ) / 10 := by
  unfold K0
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * π)).mpr
  linarith [pi_lt_d2]

theorem sharp_pair_covariance {n : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v)
    (hθ : 1 / 4 ≤ thetaC c τ) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rowC c τ q.1 q.2 ^ 2)
      ((rowLaw n).prod (rowLaw n)) ∧
    (∫ q, rowC c τ q.1 q.2 ^ 2 ∂((rowLaw n).prod (rowLaw n))) ≤
      τ ^ 4 / n * ((1 + v) * (qHS n (thetaC c τ) ^ 2 + 1 / n) +
        (1 + 1 / v) * (3 / (16 * n))) := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hS : 0 < S0 n := by linarith [cutoff_half hn]
  obtain ⟨i1, e1⟩ := row_pair_moment (by omega : 1 ≤ n) c hc hτ hS (cutoff_full hn)
  have e1' := e1.trans (mul_le_mul_of_nonneg_left (rowPair_le_paper hn hn1 c hτ hθ)
    (by positivity : (0 : ℝ) ≤ 1 / n))
  obtain ⟨i2, e2⟩ := mean2 (n := n) (by omega)
  have hK : PRvecAbs (1 / 10) := PRvecAbs_of
    (fun a => (Ures_le_K0 a).trans price_constant_tenth)
  have hp := fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
    rowC_sq_le (by norm_num : (0 : ℝ) ≤ 1 / 10) hK c hτ hv q.1 q.2
  have iA := (i1.const_mul (τ ^ 4)).const_mul (1 + v)
  have iB := ((i2.const_mul (τ ^ 4)).const_mul ((1 / 10 : ℝ) ^ 2)).const_mul (1 + 1 / v)
  have iC : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rowC c τ q.1 q.2 ^ 2)
      ((rowLaw n).prod (rowLaw n)) := by
    apply (iA.add iB).mono' (meas_rowC c τ |>.pow_const 2).aestronglyMeasurable
    filter_upwards [] with q
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hp q
  refine ⟨iC, ?_⟩
  have h := integral_mono iC (iA.add iB) hp
  simp only [Pi.add_apply] at h
  rw [integral_add iA iB, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul] at h
  have hsecond : (1 / 10 : ℝ) ^ 2 * (∫ q, Qf q ∂((rowLaw n).prod (rowLaw n))) ≤
      3 / (16 * (n : ℝ) ^ 2) := by
    apply (mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ (1 / 10 : ℝ) ^ 2)).trans
    have hn3 : (0 : ℝ) < n - 3 := by linarith
    calc (1 / 10 : ℝ) ^ 2 * (12 / ((n : ℝ) * ((n : ℝ) - 3))) =
        3 / (25 * ((n : ℝ) * ((n : ℝ) - 3))) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have h1 := mul_le_mul_of_nonneg_left e1'
    (show 0 ≤ (1 + v) * τ ^ 4 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ (1 + 1 / v) * τ ^ 4 by positivity)
  ring_nf at h h1 h2 ⊢
  linarith only [h, h1, h2]

theorem sharp_hs_expectation {n : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v)
    (hθ : 1 / 4 ≤ thetaC c τ) :
    Integrable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => hsH A c τ)
      (gaussMat (mA n) n (2 / n)) ∧
    (∫ A : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A c τ
      ∂gaussMat (mA n) n (2 / n)) ≤ 4 * τ ^ 4 / n * CH n (thetaC c τ) v := by
  obtain ⟨iO, eO⟩ := sharp_pair_covariance hn hn1 c hc hτ hv hθ
  obtain ⟨iD, eD⟩ := diagL (by omega : 1 ≤ n) c hτ.le
  let t : ℝ := 2 / ((mA n : ℕ) : ℝ)
  let P := τ ^ 4 / n * ((1 + v) * (qHS n (thetaC c τ) ^ 2 + 1 / n) +
    (1 + 1 / v) * (3 / (16 * n)))
  let Dg := τ ^ 4 * (4 * (1 + 2 / (n : ℝ)))
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hD0 : 0 ≤ Dg := by dsimp [Dg]; positivity
  have mO : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (t * rowC c τ q.1 q.2) ^ 2) :=
    ((meas_rowC c τ).const_mul t).pow_const 2
  have mD : Measurable (fun a : Fin n → ℝ => (t * rowC c τ a a) ^ 2) :=
    (((meas_rowC c τ).comp (measurable_id.prodMk measurable_id)).const_mul t).pow_const 2
  have iO' : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (t * rowC c τ q.1 q.2) ^ 2)
      ((rowLaw n).prod (rowLaw n)) := by
    simp_rw [mul_pow]; exact iO.const_mul _
  have iD' : Integrable (fun a : Fin n → ℝ => (t * rowC c τ a a) ^ 2) (rowLaw n) := by
    simp_rw [mul_pow]; exact iD.const_mul _
  have key : ∀ i j : Fin (mA n),
      Integrable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ =>
        covF (stdGauss (Fin n)) (fA A c τ) i j ^ 2) (gaussMat (mA n) n (2 / n)) ∧
      (∫ A : Matrix (Fin (mA n)) (Fin n) ℝ,
        covF (stdGauss (Fin n)) (fA A c τ) i j ^ 2 ∂gaussMat (mA n) n (2 / n)) ≤
          t ^ 2 * (P + if i = j then Dg else 0) := by
    intro i j
    simp_rw [covF_eq]
    change Integrable (fun A => (t * rowC c τ (rowOf i A) (rowOf j A)) ^ 2) _ ∧ _
    by_cases hij : i = j
    · subst j
      obtain ⟨hi, he⟩ := int_diag_mat (m := mA n) i mD iD'
      refine ⟨hi, ?_⟩
      rw [he]
      simp only [if_pos rfl]
      simp_rw [mul_pow]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (eD.trans (le_add_of_nonneg_left hP0)) (sq_nonneg t)
    · obtain ⟨hi, he⟩ := int_offd_mat (m := mA n) hij mO iO'
      refine ⟨hi, ?_⟩
      rw [he]
      simp only [hij, if_false, add_zero]
      simp_rw [mul_pow]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left eO (sq_nonneg t)
  exact hs_expectation_of_covariance_moments (by omega) c τ (thetaC c τ) v hv
    (fun i j => (key i j).1) (fun i j => (key i j).2)

/-- The original HS event supplies the sharp expectation bound without a new charge. -/
theorem sharp_HS_same_event {n : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v)
    (hθ : 1 / 4 ≤ thetaC c τ)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A ∉ BadH n c τ 12) :
    hsH A c τ ≤ (√(√(4 * τ ^ 4 / n * CH n (thetaC c τ) v)) +
      2 * √24 * √(normSq c + n * τ ^ 2) / ((n : ℝ) * √(n : ℝ))) ^ 4 :=
  HS_same_event (by omega) c hτ (sharp_hs_expectation hn hn1 c hc hτ hv hθ).2 hA

#print axioms sharp_pair_covariance
#print axioms sharp_hs_expectation
#print axioms sharp_HS_same_event

theorem sharp_HS_on_GoodC {n J : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v)
    (hθ : 1 / 4 ≤ thetaC c τ)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A2 : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hA : (A, A2) ∈ GoodC n J c τ) :
    hsH A c τ ≤ (√(√(4 * τ ^ 4 / n * CH n (thetaC c τ) v)) +
      2 * √24 * √(normSq c + n * τ ^ 2) / ((n : ℝ) * √(n : ℝ))) ^ 4 :=
  sharp_HS_same_event hn hn1 c hc hτ hv hθ hA.2.1

#print axioms sharp_HS_on_GoodC
end BstLean.Part198
