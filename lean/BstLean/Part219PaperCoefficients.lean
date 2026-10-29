import BstLean.Part219Coefficient
import BstLean.Part219Rotation

/-! The mean-coefficient estimates in the paper's theta normalization. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part150 (thetaC rhoC)
open BstLean.Part29 (stdGauss)

noncomputable def paperAmplitude (n : ℕ) (θ : ℝ) : ℝ :=
  √((1 - θ) / (1 - 4 * θ / n))

noncomputable def paperBias (n : ℕ) (θ : ℝ) : ℝ :=
  (θ + √θ * radiusCoefficient n 4 θ * √(1 + 3 / n)) / n

lemma theta_range {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < thetaC c τ ∧ thetaC c τ ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  unfold thetaC
  constructor
  · positivity
  · apply (div_le_one (sq_pos_of_pos hρ)).mpr
    rw [BstLean.Part150.rhoC_sqP]
    linarith [normSq_nonneg c]

lemma signal_fraction {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1)
    (a : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    1 - thetaC (a • u) τ = (a / rhoC (a • u) τ) ^ 2 := by
  have hρ := BstLean.Part150.rhoC_posP hn (a • u) hτ
  have hs := BstLean.Part150.rhoC_sqP (a • u) τ
  simp only [normSq_smul, hu, mul_one] at hs
  unfold thetaC
  field_simp
  nlinarith

lemma latitudeAllowance_paper {n k : ℕ} (hn : 1 ≤ n) (θ : ℝ) :
    latitudeAllowance n k θ =
      radiusCoefficient n (4 * k) θ * √(1 + (4 * (k : ℝ) - 1) / n) / √(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : ((n : ℝ) + 4 * k - 1) = n * (1 + (4 * (k : ℝ) - 1) / n) := by field_simp; ring
  unfold latitudeAllowance
  rw [hs, sqrt_mul hnR.le]
  have hsq := sq_sqrt hnR.le
  have hnS : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  field_simp
  rw [hsq]

lemma paperAmplitude_identity {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    a * √(1 / (a ^ 2 + ((n : ℝ) - 4) * τ ^ 2)) =
      paperAmplitude n (thetaC (a • u) τ) := by
  have hnR : (4 : ℝ) < n := by exact_mod_cast (show 4 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hρ := BstLean.Part150.rhoC_posP (by omega) (a • u) hτ
  have hs := BstLean.Part150.rhoC_sqP (a • u) τ
  simp only [normSq_smul, hu, mul_one] at hs
  have hD : 0 < a ^ 2 + ((n : ℝ) - 4) * τ ^ 2 := by positivity
  have he : (1 - thetaC (a • u) τ) / (1 - 4 * thetaC (a • u) τ / n) =
      a ^ 2 / (a ^ 2 + ((n : ℝ) - 4) * τ ^ 2) := by
    rw [signal_fraction (by omega) hu a hτ]
    unfold thetaC
    field_simp
    rw [hs]
    congr 1
    ring
  unfold paperAmplitude
  rw [he]
  calc
    _ = √(a ^ 2 * (1 / (a ^ 2 + ((n : ℝ) - 4) * τ ^ 2))) := by
      rw [sqrt_mul (sq_nonneg a), sqrt_sq ha]
    _ = _ := by congr 1; ring

lemma paperBias_identity {n : ℕ} (hn : 11 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    τ ^ 2 / rhoC c τ ^ 2 + τ / rhoC c τ * latitudeAllowance n 1 (thetaC c τ) =
      paperBias n (thetaC c τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hρ := BstLean.Part150.rhoC_posP (by omega) c hτ
  have hnS : 0 < √(n : ℝ) := sqrt_pos.mpr hnR
  have ht : √(thetaC c τ) = √(n : ℝ) * τ / rhoC c τ := by
    unfold thetaC
    rw [sqrt_div (mul_nonneg hnR.le (sq_nonneg _)), sqrt_mul hnR.le,
      sqrt_sq hτ.le, sqrt_sq hρ.le]
  rw [latitudeAllowance_paper (by omega)]
  unfold paperBias
  rw [ht]
  norm_num
  unfold thetaC
  have hs := sq_sqrt hnR.le
  field_simp
  ring_nf
  rw [hs]
  <;> ring

theorem inputMean_paper_amplitude {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    0 ≤ u ⬝ᵥ inputMean (a • u) τ ∧
      u ⬝ᵥ inputMean (a • u) τ ≤ paperAmplitude n (thetaC (a • u) τ) := by
  exact ⟨inputMean_axial_nonneg (by omega) u ha hτ,
    (inputMean_axial_upper_sharp hn hu ha hτ).trans_eq (paperAmplitude_identity hn hu ha hτ)⟩

theorem inputMean_paper_bias {n : ℕ} (hn : 11 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    |u ⬝ᵥ inputMean (a • u) τ - √(1 - thetaC (a • u) τ)| ≤
      paperBias n (thetaC (a • u) τ) := by
  have hz := latitude_centered_norm (k := 1) (by norm_num) (by omega) hu a hτ
  norm_num only [BstLean.Part195.rotationConstant_one, one_mul, Nat.cast_one, mul_one] at hz
  have hm : Measurable (fun x => |u ⬝ᵥ standPoint (a • u) τ x - u ⬝ᵥ inputMean (a • u) τ|) := by
    simpa only [Function.comp_apply, dotLinear_apply] using
      (((dotLinear u).continuous.measurable.comp (measurable_standPoint (a • u) τ)).sub_const
        (u ⬝ᵥ inputMean (a • u) τ)).abs
  have hG := latitudeAllowance_nonneg (k := 1) (by omega) (a • u) hτ
  have hv := (moment_of_norm (p := 2) (by norm_num) hm.aestronglyMeasurable
    (fun _ => abs_nonneg _) hG hz).2
  simp only [sq_abs] at hv
  have hh := inputMean_bias_of_variance (by omega) hu ha hτ hG hv
  rw [paperBias_identity hn (a • u) hτ] at hh
  rw [signal_fraction (by omega) hu a hτ, sqrt_sq (div_nonneg ha
    (BstLean.Part150.rhoC_posP (by omega) (a • u) hτ).le)]
  exact hh

theorem inputMean_paper_square_bias {n : ℕ} (hn : 11 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    |(u ⬝ᵥ inputMean (a • u) τ) ^ 2 - (1 - thetaC (a • u) τ)| ≤
      2 * paperBias n (thetaC (a • u) τ) := by
  let α := u ⬝ᵥ inputMean (a • u) τ
  let q := 1 - thetaC (a • u) τ
  have hθ := theta_range (by omega) (a • u) hτ
  have hq : 0 ≤ q := sub_nonneg.mpr hθ.2
  have hs : √q ≤ 1 := sqrt_le_one.mpr (by dsimp [q]; linarith [hθ.1])
  have hα := inputMean_axial_nonneg (by omega) u ha hτ
  have hα1 := (abs_le.mp (inputMean_coefficient_abs (by omega) hu (a • u) τ)).2
  have he : α ^ 2 - q = (α - √q) * (α + √q) := by rw [mul_add, sub_mul, sub_mul]; nlinarith [sq_sqrt hq]
  change |α ^ 2 - q| ≤ _
  rw [he, abs_mul, abs_of_nonneg (add_nonneg hα (sqrt_nonneg q))]
  have h := mul_le_mul_of_nonneg_left (show α + √q ≤ 2 by linarith) (abs_nonneg (α - √q))
  have hb := mul_le_mul_of_nonneg_right (inputMean_paper_bias hn hu ha hτ) (by norm_num : (0 : ℝ) ≤ 2)
  exact h.trans (by dsimp only [α, q]; linarith [hb])

#print axioms inputMean_paper_amplitude
#print axioms inputMean_paper_bias
#print axioms inputMean_paper_square_bias
end BstLean.Part219
