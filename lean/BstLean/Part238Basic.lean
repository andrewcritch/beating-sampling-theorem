import BstLean.Part208CoreGain
import BstLean.Part208PairModes
import BstLean.Part208SchurIntegrated
import BstLean.Part199TI

/-! Part 238: basic facts for the sharp core level.
The three TI mode bounds are stated for the raw Jacobian `jac A₁ A₂ x`.
The tangent Jacobian is `jacT = jac * projT`. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part182 BstLean.Part208
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm projT jacT projT_transpose
  projT_mulVec_sj)
open BstLean.Part151 (jac)

/-- The three paper pair bounds of Lemma `t7:p04:ti` for one ordered pair of unit inputs,
with the overlap cap used by the tangential gain. All constants carry the factor `n`. -/
def ModeBounds {m n : ℕ} (J J' : Matrix (Fin m) (Fin n) ℝ) (kE ko ks cp : ℝ)
    (x x' : Fin n → ℝ) : Prop :=
  (x ⬝ᵥ x') ^ 2 ≤ cp ^ 2 ∧
  opN (PEm x x' * (Jᵀ * J') * PEm x x') ≤ (n : ℝ) * kE ∧
  nrm (PEm x x' *ᵥ ((Jᵀ * J') *ᵥ eTan x' x)) ≤ (n : ℝ) * ko ∧
  nrm (PEm x x' *ᵥ ((J'ᵀ * J) *ᵥ eTan x x')) ≤ (n : ℝ) * ko ∧
  |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ (n : ℝ) * ks

/-- A row vector times the tangent Jacobian is tangent at `x`. -/
lemma dot_vecMul_jacT {m n : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) {x : Fin n → ℝ} (hx : normSq x = 1) (v : Fin m → ℝ) :
    x ⬝ᵥ vecMul v (jacT A₁ A₂ x) = 0 := by
  have h1 : vecMul v (jacT A₁ A₂ x) = projT x *ᵥ vecMul v (jac A₁ A₂ x) := by
    unfold jacT
    rw [← vecMul_vecMul, ← vecMul_transpose, projT_transpose]
  rw [h1, projT_mulVec_sj, dotProduct_sub, dotProduct_smul, ms_dot_self, hx, smul_eq_mul]
  ring

/-- On tangent vectors the tangent Jacobian acts as the raw Jacobian. -/
lemma jacT_mulVec_of_perp {m n : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) {x f : Fin n → ℝ} (hxf : x ⬝ᵥ f = 0) :
    jacT A₁ A₂ x *ᵥ f = jac A₁ A₂ x *ᵥ f := by
  unfold jacT
  rw [← mulVec_mulVec, projT_mulVec_sj, hxf, zero_smul, sub_zero]

lemma nrm_smul_sqrt {n : ℕ} (s : ℝ) (f : Fin n → ℝ) :
    nrm (√s • f) = √s * nrm f := by
  unfold nrm
  rw [normSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]

lemma normSq_smul_sqrt {n : ℕ} {s : ℝ} (hs : 0 ≤ s) (f : Fin n → ℝ) :
    normSq (√s • f) = s * normSq f := by
  rw [normSq_smul, Real.sq_sqrt hs]

/-- Two square-integrable functions have an integrable product. -/
lemma integrable_mul_of_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {a b : α → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hai : Integrable (fun p => a p ^ 2) ν) (hbi : Integrable (fun p => b p ^ 2) ν) :
    Integrable (fun p => a p * b p) ν := by
  refine Integrable.mono' ((hai.add hbi).div_const 2) (ha.mul hb).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  show |a p| * |b p| ≤ (a p ^ 2 + b p ^ 2) / 2
  have h1 := sq_abs (a p)
  have h2 := sq_abs (b p)
  nlinarith [sq_nonneg (|a p| - |b p|)]

/-- The core gain `χ` is nonnegative under the gain premises. -/
lemma chi_nonneg {n d : ℕ} {a τ t0 z0 cp sm : ℝ}
    (hR : 0 < axialRadiusLower n a τ t0 z0) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1) :
    0 ≤ (axialPlaneUpper n a τ t0 z0 * (1 - sm) + 1 / (d : ℝ)) / (1 - cp ^ 2) := by
  apply div_nonneg
  · exact add_nonneg
      (mul_nonneg (div_nonneg (sq_nonneg _) hR.le) (sub_nonneg.mpr hsm1))
      (div_nonneg zero_le_one (Nat.cast_nonneg d))
  · linarith

lemma ta_lam_nonneg {kE ko ks : ℝ} (hkE : 0 ≤ kE) (hks : 0 ≤ ks) : 0 ≤ ta_lam kE ko ks := by
  unfold ta_lam
  positivity

/-- The sharp coefficient of the core level, `kE + 2 ko √χ + ks χ`. -/
noncomputable def sharpK (kE ko ks χ : ℝ) : ℝ := kE + 2 * ko * √χ + ks * χ

lemma sharpK_nonneg {kE ko ks χ : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hχ : 0 ≤ χ) : 0 ≤ sharpK kE ko ks χ := by
  unfold sharpK
  positivity

end BstLean.Part238
