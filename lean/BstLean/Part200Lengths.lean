import BstLean.Part200Pair
import BstLean.Part153Energy
import BstLean.Part153Norms

/-! The fixed-input first-layer length and the two-input low-length event. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153

variable {n : ℕ}

/-- A scaled energy equals the paper length `|a₁(x)|/√n` at width `n²`. -/
noncomputable def layerLength (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ := √((n : ℝ) / 2) * √(GamS A x 0)

lemma layerLength_nonneg (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) (x : Fin n → ℝ) :
    0 ≤ layerLength A x := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)

lemma measurable_layerLength (x : Fin n → ℝ) : Measurable (fun A => layerLength A x) :=
  (measurable_GamS x 0).sqrt.const_mul _

lemma length_scale {n : ℕ} (hn : 1 ≤ n) :
    √((n : ℝ) / 2) * √(2 / (n : ℝ) ^ 2) = (√(n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sqrt_mul (by positivity)]
  have he : (n : ℝ) / 2 * (2 / (n : ℝ) ^ 2) = 1 / n := by
    field_simp [hn0.ne'] <;> ring
  rw [he, sqrt_div zero_le_one, sqrt_one, one_div]

lemma layerLength_eq (hn : 1 ≤ n) (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ)
    (x : Fin n → ℝ) : layerLength A x = nrm (reluV (A *ᵥ x)) / √(n : ℝ) := by
  have he : GamS A x 0 = 2 / (n : ℝ) ^ 2 * normSq (reluV (A *ᵥ x)) := by
    simp [GamS, Nat.cast_pow]
  unfold layerLength
  rw [he, sqrt_mul (by positivity), ← nrm, ← mul_assoc, length_scale hn]
  ring

theorem layerLength_mean (hn : 2 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) :
    Integrable (fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => layerLength A x)
      (gaussMat (n ^ 2) n (2 / n)) ∧
    1 - 2 / (n : ℝ) ^ 2 ≤ (∫ A, layerLength A x ∂gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, layerLength A x ∂gaussMat (n ^ 2) n (2 / n)) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hi, h0, hlo, hhi⟩ := sqrtGam_mean (m := n ^ 2) (by nlinarith) x 0
    (v := 2 / n) (by positivity)
  simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
    mul_one, Nat.cast_pow] at hlo hhi
  let a := ∫ A : Matrix (Fin (n ^ 2)) (Fin n) ℝ,
    √(GamS A x 0) ∂gaussMat (n ^ 2) n (2 / n)
  have hs : √((n : ℝ) / 2) ^ 2 = (n : ℝ) / 2 := sq_sqrt (by positivity)
  have hmean : (∫ A, layerLength A x ∂gaussMat (n ^ 2) n (2 / n)) =
      √((n : ℝ) / 2) * a := integral_const_mul _ _
  have hprod : (n : ℝ) / 2 * (2 / n) = 1 := by field_simp [hn0.ne']
  have hsqlo : 1 - 2 / (n : ℝ) ^ 2 ≤ (√((n : ℝ) / 2) * a) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (n : ℝ) / 2 by positivity)
    simpa only [mul_pow, hs, ← mul_assoc, hprod, one_mul] using h
  have hsqhi : (√((n : ℝ) / 2) * a) ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hhi (show 0 ≤ (n : ℝ) / 2 by positivity)
    simpa only [mul_pow, hs, hprod] using h
  have hm0 : 0 ≤ √((n : ℝ) / 2) * a := mul_nonneg (sqrt_nonneg _) h0
  have hm1 : √((n : ℝ) / 2) * a ≤ 1 := by nlinarith
  refine ⟨hi.const_mul _, ?_, ?_⟩
  · rw [hmean]
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm1)]
  · rw [hmean]; exact hm1

lemma layerLength_lip (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1)
    (A A' : Matrix (Fin (n ^ 2)) (Fin n) ℝ) :
    |layerLength A x - layerLength A' x| ≤
      (√(n : ℝ))⁻¹ * √(∑ i, ∑ j, (A i j - A' i j) ^ 2) := by
  unfold layerLength
  rw [← mul_sub, abs_mul, abs_of_nonneg (sqrt_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (sqrtGam_lip x 0 A A') (sqrt_nonneg ((n : ℝ) / 2))
  simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
    sqrt_one, mul_one, Nat.cast_pow] at h
  simpa only [← mul_assoc, length_scale hn] using h

/-- The fixed-input length tail has the paper exponent. -/
theorem layerLength_tail (hn : 2 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1)
    {η : ℝ} (hη : 2 / (n : ℝ) ^ 2 ≤ η) :
    (gaussMat (n ^ 2) n (2 / n)).real {A | η < |layerLength A x - 1|} ≤
      2 * exp (-(n : ℝ) ^ 2 * (η - 2 / (n : ℝ) ^ 2) ^ 2 / 4) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let μ := gaussMat (n ^ 2) n (2 / n)
  let a := ∫ A, layerLength A x ∂μ
  obtain ⟨_, hlo, hhi⟩ := layerLength_mean hn hx
  have hu := gaussConc_mat_upper_sharp (g := fun A => layerLength A x)
    (inv_nonneg.mpr (sqrt_nonneg _)) (layerLength_lip (by omega) hx)
    (v := 2 / n) (by positivity) (t := η - 2 / (n : ℝ) ^ 2) (sub_nonneg.mpr hη)
  have hl := gaussConc_mat_lower_sharp (g := fun A => layerLength A x)
    (inv_nonneg.mpr (sqrt_nonneg _)) (layerLength_lip (by omega) hx)
    (v := 2 / n) (by positivity) (t := η - 2 / (n : ℝ) ^ 2) (sub_nonneg.mpr hη)
  have he : -(η - 2 / (n : ℝ) ^ 2) ^ 2 / (2 * ((2 / n) * ((√(n : ℝ))⁻¹) ^ 2)) =
      -(n : ℝ) ^ 2 * (η - 2 / (n : ℝ) ^ 2) ^ 2 / 4 := by
    rw [inv_pow, sq_sqrt hn0.le]
    field_simp [hn0.ne']
    <;> ring
  rw [he] at hu hl
  have hsub : {A | η < |layerLength A x - 1|} ⊆
      {A | a + (η - 2 / (n : ℝ) ^ 2) ≤ layerLength A x} ∪
      {A | layerLength A x ≤ a - (η - 2 / (n : ℝ) ^ 2)} := by
    intro A hA
    change η < |layerLength A x - 1| at hA
    rcases lt_abs.mp hA with hA | hA
    · left; dsimp [a, μ]; linarith
    · right; dsimp [a, μ]; linarith
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith))

/-- The two inputs share the first layer. The union bound needs no independence. -/
theorem pair_lowLength_probability (hn : 2 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {η : ℝ} (hη : 2 / (n : ℝ) ^ 2 ≤ η) :
    (gaussMat (n ^ 2) n (2 / n)).real
      {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|} ≤
      4 * exp (-(n : ℝ) ^ 2 * (η - 2 / (n : ℝ) ^ 2) ^ 2 / 4) := by
  have h₁ := layerLength_tail hn hx hη
  have h₂ := layerLength_tail hn hx' hη
  have h := measureReal_union_le (μ := gaussMat (n ^ 2) n (2 / n))
    {A | η < |layerLength A x - 1|} {A | η < |layerLength A x' - 1|}
  change (gaussMat (n ^ 2) n (2 / n)).real
    ({A | η < |layerLength A x - 1|} ∪ {A | η < |layerLength A x' - 1|}) ≤ _
  linarith

end BstLean.Part200
