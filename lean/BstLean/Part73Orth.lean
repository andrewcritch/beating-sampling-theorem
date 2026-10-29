import BstLean.Part56PropD_Polar
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Part 73: orthogonal invariance of `stdGauss` and of `uniformSphere`

For every matrix `O` with `Oᵀ O = 1`, the map `x ↦ O x` preserves `stdGauss (Fin n)`
(`stdGauss_orth`) and `uniformSphere n` (`uniformSphere_orth`).
Route: `stdGauss (Fin n)` is Mathlib's `stdGaussian` on `EuclideanSpace ℝ (Fin n)` moved by `ofLp`
(`map_pi_eq_stdGaussian`), and `stdGaussian_map` gives the invariance under a linear isometry
equivalence. For the sphere: `uniformSphere_lintegral_gauss` (Part 56) and `unitF53 (O g) = O unitF53 g`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part73

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- `Oᵀ O = 1`. -/
def IsOrth (O : Matrix (Fin n) (Fin n) ℝ) : Prop := O.transpose * O = 1

lemma IsOrth.mul_t {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) : O * O.transpose = 1 :=
  mul_eq_one_comm.mp hO

lemma IsOrth.t {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) : IsOrth O.transpose := by
  unfold IsOrth; rw [Matrix.transpose_transpose]; exact hO.mul_t

/-- `‖O x‖² = ‖x‖²`. -/
lemma orth_sumsq {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (x : Fin n → ℝ) :
    ∑ i, (O.mulVec x) i ^ 2 = ∑ i, x i ^ 2 := by
  have h : (O.mulVec x) ⬝ᵥ (O.mulVec x) = x ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose,
      show O.transpose * O = 1 from hO]
    simp
  simpa [dotProduct, sq] using h

/-- The linear isometry equivalence of `EuclideanSpace` given by `O`. -/
noncomputable def orthLIE (O : Matrix (Fin n) (Fin n) ℝ) (hO : IsOrth O) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (O.mulVec (WithLp.ofLp x))
  invFun x := WithLp.toLp 2 (O.transpose.mulVec (WithLp.ofLp x))
  map_add' x y := by simp [Matrix.mulVec_add]
  map_smul' c x := by simp [Matrix.mulVec_smul]
  left_inv x := by simp only [Matrix.mulVec_mulVec]; rw [show O.transpose * O = 1 from hO]; simp
  right_inv x := by simp only [Matrix.mulVec_mulVec]; rw [hO.mul_t]; simp
  norm_map' x := by
    have h1 := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (O.mulVec (WithLp.ofLp x)))
    have h2 := EuclideanSpace.real_norm_sq_eq x
    rw [orth_sumsq hO, ← h2] at h1
    have := norm_nonneg x
    have := norm_nonneg (WithLp.toLp 2 (O.mulVec (WithLp.ofLp x)))
    change ‖WithLp.toLp 2 (O.mulVec (WithLp.ofLp x))‖ = ‖x‖
    nlinarith

lemma stdGauss_eq_map :
    stdGauss (Fin n) = (stdGaussian (EuclideanSpace ℝ (Fin n))).map WithLp.ofLp := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  unfold stdGauss
  have : (WithLp.ofLp ∘ WithLp.toLp 2 : (Fin n → ℝ) → Fin n → ℝ) = id := rfl
  rw [this, Measure.map_id]

/-- Deliverable 1: `x ↦ O x` preserves `stdGauss (Fin n)`. -/
theorem stdGauss_orth (O : Matrix (Fin n) (Fin n) ℝ) (hO : IsOrth O) :
    (stdGauss (Fin n)).map (fun x => O.mulVec x) = stdGauss (Fin n) := by
  rw [stdGauss_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  have hc : (fun x => O.mulVec x) ∘ (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) =
      WithLp.ofLp ∘ (orthLIE O hO) := by
    funext x; rfl
  rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  exact stdGaussian_map (orthLIE O hO)

lemma unitF_orth {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (g : Fin n → ℝ) :
    unitF53 (O.mulVec g) = O.mulVec (unitF53 g) := by
  unfold unitF53
  rw [orth_sumsq hO, Matrix.mulVec_smul]

/-- Deliverable 2: `x ↦ O x` preserves `uniformSphere n`. -/
theorem uniformSphere_orth (O : Matrix (Fin n) (Fin n) ℝ) (hO : IsOrth O) :
    (uniformSphere n).map (fun x => O.mulVec x) = uniformSphere n := by
  have hm : Measurable (fun x : Fin n → ℝ => O.mulVec x) := by fun_prop
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have : (fun x : Fin 0 → ℝ => O.mulVec x) = id := by funext x; exact Subsingleton.elim _ _
    rw [this, Measure.map_id]
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hm]
  rw [BstLean.Part56.uniformSphere_lintegral_gauss n hn (fun x => F (O.mulVec x)) (hF.comp hm),
    BstLean.Part56.uniformSphere_lintegral_gauss n hn _ hF]
  have h1 : (fun g => F (O.mulVec (unitF53 g))) = fun g => F (unitF53 (O.mulVec g)) := by
    funext g; rw [unitF_orth hO]
  rw [h1]
  have h2 := lintegral_map (μ := stdGauss (Fin n)) (hF.comp BstLean.Part53.measurable_unitF) hm
  rw [stdGauss_orth O hO] at h2
  exact h2.symm

end BstLean.Part73
