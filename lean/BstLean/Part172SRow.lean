import BstLean.Part172Sph

/-!
# Part 172 (file `SRow`): the variance of one first-layer coordinate on a latitude

No proof is left open; no `native_decide` or `axiom` is used.

`Y = ⟨p, w⟩`, `w = V/|V|`, `f = ReLU(μ + σY)`.
* **`sg_row_var_lower`**: if `μ ≥ 0`, `σ ≥ 0`, then `Var f ≥ σ²|p|²/(4d)`
  (`Cov(f, Y) ≥ σE Y²/2` by symmetry, then Cauchy–Schwarz).
* **`sg_row_var_upper`**: if `σ ≥ 0`, then `Var f ≤ σ²|p|²/d` (`ReLU` is 1-Lipschitz).
Here `Var f = E f² − (E f)²`.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq relu)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {d : ℕ}

/-- `Y(v) = ⟨p, v/|v|⟩`. -/
noncomputable def sg_Y (p : Fin d → ℝ) (v : Fin d → ℝ) : ℝ := ∑ k, p k * unitF53 v k

lemma sg_meas_Y (p : Fin d → ℝ) : Measurable (sg_Y p) :=
  Finset.measurable_sum _ fun k _ => measurable_const.mul ((measurable_pi_apply k).comp measurable_unitF)

lemma sg_Y_sq_le (p v : Fin d → ℝ) : sg_Y p v ^ 2 ≤ normSq p := by
  have h0 : 0 ≤ normSq p := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc sg_Y p v ^ 2 ≤ normSq p * ∑ k, unitF53 v k ^ 2 := sg_dot_sq_le _ _
    _ ≤ normSq p * 1 := mul_le_mul_of_nonneg_left (sg_unit_sumsq_le v) h0
    _ = normSq p := mul_one _

lemma sg_abs_Y_le (p v : Fin d → ℝ) : |sg_Y p v| ≤ √(normSq p) := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (sg_Y_sq_le p v)

lemma sg_Y_neg (p v : Fin d → ℝ) : sg_Y p (-v) = - sg_Y p v := by
  unfold sg_Y unitF53
  simp only [Pi.neg_apply, neg_sq, Pi.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma sg_int_neg {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) :
    ∫ v, g (-v) ∂stdGauss (Fin d) = ∫ v, g v ∂stdGauss (Fin d) := by
  classical
  have h := integral_map (μ := stdGauss (Fin d)) (φ := fun z : Fin d → ℝ => -z)
    measurable_neg.aemeasurable (f := g) hg.aestronglyMeasurable
  rw [BstLean.Part33.stdGauss_neg_invariant] at h
  exact h.symm

lemma sg_int_Y (p : Fin d → ℝ) : ∫ v, sg_Y p v ∂stdGauss (Fin d) = 0 := by
  have h := sg_int_neg (sg_meas_Y p)
  simp_rw [sg_Y_neg] at h
  rw [integral_neg] at h
  linarith

lemma sg_relu_key {μ σ : ℝ} (hμ : 0 ≤ μ) (hσ : 0 ≤ σ) (y : ℝ) :
    σ * y ^ 2 ≤ (relu (μ + σ * y) - relu (μ + σ * (-y))) * y := by
  unfold relu
  rcases le_total 0 y with hy | hy
  · have h1 : 0 ≤ μ + σ * y := by nlinarith
    rw [max_eq_right h1]
    rcases le_total 0 (μ + σ * -y) with h2 | h2
    · rw [max_eq_right h2]; nlinarith
    · rw [max_eq_left h2]; nlinarith
  · have h1 : 0 ≤ μ + σ * -y := by nlinarith
    rw [max_eq_right h1]
    rcases le_total 0 (μ + σ * y) with h2 | h2
    · rw [max_eq_right h2]; nlinarith
    · rw [max_eq_left h2]; nlinarith

lemma sg_relu_abs (a : ℝ) : |relu a| ≤ |a| := by
  unfold relu
  rcases le_total 0 a with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h]; simp

/-- Common integrability facts. -/
lemma sg_row_int (p : Fin d → ℝ) (μ σ : ℝ) :
    let f := fun v => relu (μ + σ * sg_Y p v)
    Measurable f ∧ (∀ v, |f v| ≤ |μ| + |σ| * √(normSq p)) := by
  intro f
  refine ⟨?_, fun v => ?_⟩
  · exact (BstLean.Part130.continuous_relu.measurable).comp
      (measurable_const.add (measurable_const.mul (sg_meas_Y p)))
  · refine (sg_relu_abs _).trans ((abs_add_le _ _).trans ?_)
    rw [abs_mul]
    gcongr
    exact sg_abs_Y_le p v

lemma sg_var_eq {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) (c : ℝ) :
    ∫ v, (f v - c) ^ 2 ∂stdGauss (Fin d) =
      (∫ v, f v ^ 2 ∂stdGauss (Fin d) - (∫ v, f v ∂stdGauss (Fin d)) ^ 2) +
        (∫ v, f v ∂stdGauss (Fin d) - c) ^ 2 := by
  have i1 : Integrable f (stdGauss (Fin d)) := BstLean.Part171.bdd_int hf hC
  have i2 : Integrable (fun v => f v ^ 2) (stdGauss (Fin d)) :=
    BstLean.Part171.bdd_int (hf.pow_const 2) (C := C ^ 2) fun v => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := hC v
      have h0 : 0 ≤ C := (abs_nonneg _).trans this
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have e : ∀ v, (f v - c) ^ 2 = f v ^ 2 - 2 * c * f v + c ^ 2 := fun v => by ring
  simp_rw [e]
  have j : Integrable (fun v => f v ^ 2 - 2 * c * f v) (stdGauss (Fin d)) := i2.sub (i1.const_mul _)
  rw [integral_add j (integrable_const _), integral_sub i2 (i1.const_mul _),
    integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul]
  ring

/-- **The lower bound of the row variance.** -/
theorem sg_row_var_lower (hd : 1 ≤ d) (p : Fin d → ℝ) {μ σ : ℝ} (hμ : 0 ≤ μ) (hσ : 0 ≤ σ) :
    σ ^ 2 * normSq p / (4 * d) ≤
      ∫ v, relu (μ + σ * sg_Y p v) ^ 2 ∂stdGauss (Fin d) -
        (∫ v, relu (μ + σ * sg_Y p v) ∂stdGauss (Fin d)) ^ 2 := by
  obtain ⟨hfm, hfC⟩ := sg_row_int p μ σ
  set f := fun v => relu (μ + σ * sg_Y p v) with hfd
  set K := |μ| + |σ| * √(normSq p)
  set Y := sg_Y p
  set m := ∫ v, f v ∂stdGauss (Fin d)
  have hYm := sg_meas_Y p
  have hYb : ∀ v, |Y v| ≤ √(normSq p) := sg_abs_Y_le p
  have iY : Integrable Y (stdGauss (Fin d)) := BstLean.Part171.bdd_int hYm hYb
  have iY2 : Integrable (fun v => Y v ^ 2) (stdGauss (Fin d)) :=
    BstLean.Part171.bdd_int (hYm.pow_const 2) (C := normSq p) fun v => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sg_Y_sq_le p v
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hfC 0)
  have iF : Integrable (fun v => (f v - m) * Y v) (stdGauss (Fin d)) :=
    BstLean.Part171.bdd_int ((hfm.sub_const m).mul hYm) (C := (K + |m|) * √(normSq p)) fun v => by
      rw [abs_mul]
      exact mul_le_mul ((abs_sub _ _).trans (by linarith [hfC v])) (hYb v) (abs_nonneg _)
        (by positivity)
  have iA : Integrable (fun v => (f v - m) ^ 2) (stdGauss (Fin d)) :=
    BstLean.Part171.bdd_int ((hfm.sub_const m).pow_const 2) (C := (K + |m|) ^ 2) fun v => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [hfC v])) 2
  set A := ∫ v, (f v - m) ^ 2 ∂stdGauss (Fin d)
  set B := ∫ v, (f v - m) * Y v ∂stdGauss (Fin d)
  set C := ∫ v, Y v ^ 2 ∂stdGauss (Fin d)
  have hC : C = normSq p / d := sg_sph_mom2 hd p
  have hA : A = ∫ v, f v ^ 2 ∂stdGauss (Fin d) - m ^ 2 := by
    have := sg_var_eq hfm hfC m
    have h0 : (∫ v, f v ∂stdGauss (Fin d) - m) ^ 2 = 0 := by simp [m]
    simp only [A]; linarith
  -- B = ∫ f Y
  have iFY : Integrable (fun v => f v * Y v) (stdGauss (Fin d)) :=
    BstLean.Part171.bdd_int (hfm.mul hYm) (C := K * √(normSq p)) fun v => by
      rw [abs_mul]; exact mul_le_mul (hfC v) (hYb v) (abs_nonneg _) hK0
  have hB : B = ∫ v, f v * Y v ∂stdGauss (Fin d) := by
    have e : ∀ v, (f v - m) * Y v = f v * Y v - m * Y v := fun v => by ring
    simp only [B]; simp_rw [e]
    rw [integral_sub iFY (iY.const_mul m), integral_const_mul, sg_int_Y, mul_zero, sub_zero]
  -- symmetry
  have hsym : ∫ v, f v * Y v ∂stdGauss (Fin d) = - ∫ v, f (-v) * Y v ∂stdGauss (Fin d) := by
    have h := sg_int_neg (g := fun v => f v * Y v) (hfm.mul hYm)
    simp only [Y, sg_Y_neg, mul_neg] at h
    rw [integral_neg] at h
    linarith
  have iFY' : Integrable (fun v => f (-v) * Y v) (stdGauss (Fin d)) :=
    BstLean.Part171.bdd_int ((hfm.comp measurable_neg).mul hYm) (C := K * √(normSq p)) fun v => by
      rw [abs_mul]; exact mul_le_mul (hfC (-v)) (hYb v) (abs_nonneg _) hK0
  have h2B : 2 * B = ∫ v, (f v - f (-v)) * Y v ∂stdGauss (Fin d) := by
    have e : ∀ v, (f v - f (-v)) * Y v = f v * Y v - f (-v) * Y v := fun v => by ring
    simp_rw [e]
    rw [integral_sub iFY iFY', hB]
    linarith
  have hBlow : σ * C ≤ 2 * B := by
    rw [h2B, ← integral_const_mul]
    refine integral_mono (iY2.const_mul σ) (BstLean.Part171.bdd_int
      ((hfm.sub (hfm.comp measurable_neg)).mul hYm) (C := 2 * K * √(normSq p)) fun v => by
        rw [abs_mul]
        refine mul_le_mul ((abs_sub _ _).trans (by linarith [hfC v, hfC (-v)])) (hYb v)
          (abs_nonneg _) (by positivity)) fun v => ?_
    have := sg_relu_key hμ hσ (Y v)
    simp only [hfd, Y, sg_Y_neg] at this ⊢
    exact this
  -- the quadratic
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have e : ∀ v, (f v - m - t * Y v) ^ 2 = (f v - m) ^ 2 - 2 * t * ((f v - m) * Y v) +
        t ^ 2 * Y v ^ 2 := fun v => by ring
    have h0 : 0 ≤ ∫ v, (f v - m - t * Y v) ^ 2 ∂stdGauss (Fin d) :=
      integral_nonneg fun v => sq_nonneg _
    simp_rw [e] at h0
    have j1 : Integrable (fun v => (f v - m) ^ 2 - 2 * t * ((f v - m) * Y v)) (stdGauss (Fin d)) :=
      iA.sub (iF.const_mul _)
    have j2 : Integrable (fun v => t ^ 2 * Y v ^ 2) (stdGauss (Fin d)) := iY2.const_mul _
    rwa [integral_add j1 j2, integral_sub iA (iF.const_mul _),
      integral_const_mul, integral_const_mul] at h0
  have hq := hquad (σ / 2)
  have hC0 : 0 ≤ C := integral_nonneg fun v => sq_nonneg _
  have : σ ^ 2 * C / 4 ≤ A := by nlinarith
  rw [← hA, show σ ^ 2 * normSq p / (4 * d) = σ ^ 2 * C / 4 by rw [hC]; ring]
  exact this

/-- **The upper bound of the row variance.** -/
theorem sg_row_var_upper (hd : 1 ≤ d) (p : Fin d → ℝ) (μ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ v, relu (μ + σ * sg_Y p v) ^ 2 ∂stdGauss (Fin d) -
        (∫ v, relu (μ + σ * sg_Y p v) ∂stdGauss (Fin d)) ^ 2 ≤ σ ^ 2 * normSq p / d := by
  obtain ⟨hfm, hfC⟩ := sg_row_int p μ σ
  set f := fun v => relu (μ + σ * sg_Y p v) with hfd
  have h := sg_var_eq hfm hfC (relu μ)
  have hYm := sg_meas_Y p
  have iY2 : Integrable (fun v => sg_Y p v ^ 2) (stdGauss (Fin d)) :=
    BstLean.Part171.bdd_int (hYm.pow_const 2) (C := normSq p) fun v => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sg_Y_sq_le p v
  have hle : ∫ v, (f v - relu μ) ^ 2 ∂stdGauss (Fin d) ≤
      ∫ v, σ ^ 2 * sg_Y p v ^ 2 ∂stdGauss (Fin d) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => sq_nonneg _)
      (iY2.const_mul _) (Filter.Eventually.of_forall fun v => ?_)
    have := BstLean.Part142.abs_relu_sub_le (μ + σ * sg_Y p v) μ
    simp only [hfd]
    rw [← sq_abs, show σ ^ 2 * sg_Y p v ^ 2 = |σ * sg_Y p v| ^ 2 by rw [sq_abs]; ring]
    refine pow_le_pow_left₀ (abs_nonneg _) (this.trans (le_of_eq ?_)) 2
    ring_nf
  have hm : ∫ a, sg_Y p a ^ 2 ∂stdGauss (Fin d) = normSq p / d := sg_sph_mom2 hd p
  rw [integral_const_mul, hm] at hle
  have := sq_nonneg (∫ v, f v ∂stdGauss (Fin d) - relu μ)
  have e : σ ^ 2 * (normSq p / d) = σ ^ 2 * normSq p / d := by ring
  linarith
end BstLean.Part172
