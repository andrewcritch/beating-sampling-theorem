import BstLean.Part218Mehler
import BstLean.Part154MF

/-! The squared-ReLU covariance has the sharp second-order angular envelope. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part105 BstLean.Part130

lemma gaussian_coordinate_integral {ι : Type} [Fintype ι] (i : ι) {f : ℝ → ℝ}
    (hf : Measurable f) : (∫ x, f (x i) ∂stdGauss ι) = ∫ z, f z ∂gaussianReal 0 1 := by
  have mp : MeasurePreserving (fun x : ι → ℝ => x i) (stdGauss ι) (gaussianReal 0 1) :=
    measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  rw [← integral_map mp.measurable.aemeasurable hf.aestronglyMeasurable, mp.map_eq]

lemma gaussian_relu_cube : (∫ z, relu z ^ 3 ∂gaussianReal 0 1) = √(2 / π) := by
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  have hm : Measurable (fun x : ℝ => relu x ^ 3) := measurable_relu.pow_const 3
  have hi : Integrable (fun x : ℝ => relu (-x) ^ 3) (gaussianReal 0 1) := by
    have h := integrable_map_measure (μ := gaussianReal 0 1) (f := fun x : ℝ => -x)
      hm.aestronglyMeasurable measurable_neg.aemeasurable
    rw [hneg] at h
    exact h.mp (integrable_relu_pow 3)
  have he : (∫ z, relu (-z) ^ 3 ∂gaussianReal 0 1) = ∫ z, relu z ^ 3 ∂gaussianReal 0 1 := by
    rw [← integral_map measurable_neg.aemeasurable hm.aestronglyMeasurable, hneg]
  have h := integral_add (integrable_relu_pow 3) hi
  have hp : ∀ z : ℝ, relu z ^ 3 + relu (-z) ^ 3 = |z| ^ 3 := fun z => relu_pow_add z (by norm_num)
  simp_rw [hp] at h
  rw [he, BstLean.Part154.gauss_abs3] at h
  linarith

noncomputable def reluSquarePair (c : ℝ) : ℝ :=
  ∫ w : (Fin 1 → ℝ) × (Fin 1 → ℝ),
    relu (w.1 0) ^ 2 * relu ((c • w.1 + sC c • w.2) 0) ^ 2
    ∂(stdGauss (Fin 1)).prod (stdGauss (Fin 1))

theorem reluSquarePair_envelope {c : ℝ} (hc : |c| ≤ 1) :
    |reluSquarePair c - 1 / 4 - (2 / π) * c| ≤ (5 / 4 - 2 / π) * c ^ 2 := by
  let f : (Fin 1 → ℝ) → ℝ := fun x => relu (x 0) ^ 2
  have mf : Measurable f := (measurable_relu.comp (measurable_pi_apply 0)).pow_const 2
  have ifr : MemLp (fun x : ℝ => relu x ^ 2) 2 (gaussianReal 0 1) := by
    apply (memLp_two_iff_integrable_sq (measurable_relu.pow_const 2).aestronglyMeasurable).mpr
    simpa only [← pow_mul] using integrable_relu_pow 4
  have iF : MemLp f 2 (stdGauss (Fin 1)) := ifr.comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0)
  have e1 : (∫ x, f x ∂stdGauss (Fin 1)) = 1 / 2 := by
    rw [gaussian_coordinate_integral 0 (measurable_relu.pow_const 2)]
    exact int_relu_sq
  have e2 : (∫ x, f x ^ 2 ∂stdGauss (Fin 1)) = 3 / 2 := by
    change (∫ x : Fin 1 → ℝ, (relu (x 0) ^ 2) ^ 2 ∂stdGauss (Fin 1)) = _
    simp only [← pow_mul]
    rw [gaussian_coordinate_integral 0 (measurable_relu.pow_const 4)]
    exact int_relu_four
  have ex : (∫ x, f x * x 0 ∂stdGauss (Fin 1)) = √(2 / π) := by
    have he : ∀ x : Fin 1 → ℝ, f x * x 0 = relu (x 0) ^ 3 := by
      intro x
      by_cases hx : 0 ≤ x 0
      · dsimp [f]; rw [relu_of_nonneg hx]; ring
      · dsimp [f]; rw [relu_of_nonpos (le_of_not_ge hx)]; ring
    simp_rw [he]
    rw [gaussian_coordinate_integral 0 (measurable_relu.pow_const 3), gaussian_relu_cube]
  have ev : (∫ x, (f x - ∫ y, f y ∂stdGauss (Fin 1)) ^ 2 ∂stdGauss (Fin 1)) = 5 / 4 := by
    rw [(BstLean.Part137.integral_sq_sub_const (iF.integrable one_le_two) iF.integrable_sq _).2,
      e1, e2]
    norm_num
  rw [e1] at ev
  have h := mehler2_L2 hc iF iF
  simp only [Fin.sum_univ_one, e1, ex, ev] at h
  have hs : √(2 / π) ^ 2 = 2 / π := sq_sqrt (by positivity)
  have hv : 0 ≤ (5 : ℝ) / 4 - 2 / π := by
    have hp := pi_gt_three
    have h : 2 / π ≤ (2 : ℝ) / 3 := (div_le_div_iff₀ pi_pos (by norm_num)).mpr (by linarith)
    linarith
  simp only [← pow_two, hs] at h
  have he : c ^ 2 * √(5 / 4 - 2 / π) * √(5 / 4 - 2 / π) = (5 / 4 - 2 / π) * c ^ 2 := by
    rw [mul_assoc, mul_self_sqrt hv]
    ring
  rw [he] at h
  convert h using 1 <;> dsimp [reluSquarePair, f] <;> ring

noncomputable def squaredAngularB (N : ℕ) (c : ℝ) : ℝ :=
  reluSquarePair c / ((N : ℝ) * (N + 2)) - 1 / (4 * (N : ℝ) ^ 2)

/-- This is the paper's pointwise envelope for `b`, including its exact linear coefficient. -/
theorem squaredAngularB_envelope {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : |c| ≤ 1) :
    |squaredAngularB N c| ≤
      ((2 / π) / ((N : ℝ) * (N + 2))) * |c| +
      ((5 / 4 - 2 / π) / ((N : ℝ) * (N + 2))) * c ^ 2 +
      |1 / (4 * (N : ℝ) * (N + 2)) - 1 / (4 * (N : ℝ) ^ 2)| := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  let d : ℝ := (N : ℝ) * (N + 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have he : squaredAngularB N c =
      ((2 / π) / d) * c + (reluSquarePair c - 1 / 4 - (2 / π) * c) / d +
        (1 / (4 * (N : ℝ) * (N + 2)) - 1 / (4 * (N : ℝ) ^ 2)) := by
    dsimp [squaredAngularB, d]
    field_simp
    ring
  rw [he]
  have hb := div_le_div_of_nonneg_right (reluSquarePair_envelope hc) hd.le
  have hsum := (abs_add_le (((2 / π) / d) * c + (reluSquarePair c - 1 / 4 - (2 / π) * c) / d)
    (1 / (4 * (N : ℝ) * (N + 2)) - 1 / (4 * (N : ℝ) ^ 2))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 / π) / d),
    abs_div, abs_of_pos hd] at hsum
  have hb' : |reluSquarePair c - 1 / 4 - (2 / π) * c| / d ≤ ((5 / 4 - 2 / π) / d) * c ^ 2 :=
    hb.trans_eq (by ring)
  exact hsum.trans (add_le_add (add_le_add le_rfl hb') le_rfl)

end BstLean.Part218
#print axioms BstLean.Part218.reluSquarePair_envelope
#print axioms BstLean.Part218.squaredAngularB_envelope
