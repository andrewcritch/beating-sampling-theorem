import BstLean.Part48Defs

/-!
# Part 48, wave 1: Gaussian rotation (omQ4 §4) — proved

Specification: `delegations/answers/p48-spec-opus.md`, §3 and §5. `trig_of_poly` is in `Part48Trig`.

* `rotX_rot` (proved): `X_{s′}` of the rotated pair `(X_s, Y_s)` is `X_{s+s′}`.
* `rot_preserving` (proved): `(X, Y) ↦ (X_s, Y_s)` preserves `γ ⊗ γ`. Route used: in `ℂ`, the
  rotation is multiplication by `e^{−is}`, a linear isometry, so it preserves `stdGaussian ℂ`
  (`stdGaussian_map`); `stdGaussian ℂ` is the image of `N(0,1) ⊗ N(0,1)` under `(a, b) ↦ a + bi`
  (`stdGaussian_eq_map_pi_orthonormalBasis` with `Complex.orthonormalBasisOneI`,
  `measurePreserving_finTwoArrow`). Coordinatewise: `measurePreserving_pi` and
  `measurePreserving_arrowProdEquivProdArrow`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part48

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

/-- The rotation composes: `X_{s′}(X_s, Y_s) = X_{s+s′}`. -/
theorem rotX_rot {ι : Type*} (s s' : ℝ) (x y : ι → ℝ) :
    rotX s' (rotX s x y) (rotY s x y) = rotX (s + s') x y := by
  funext i
  simp only [rotX, rotY, Real.cos_add, Real.sin_add]
  ring

private lemma cplx_mp :
    MeasurePreserving Complex.measurableEquivRealProd.symm
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (stdGaussian ℂ) := by
  refine ⟨Complex.measurableEquivRealProd.symm.measurable, ?_⟩
  rw [← (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq,
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable
      MeasurableEquiv.finTwoArrow.measurable,
    stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI]
  congr 1
  funext x
  apply Complex.ext <;>
    simp [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI]

private lemma rot2_mp (s : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ => (Real.cos s * p.1 + Real.sin s * p.2,
        -Real.sin s * p.1 + Real.cos s * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  set R := rotation (Circle.exp (-s))
  have hR : MeasurePreserving R (stdGaussian ℂ) (stdGaussian ℂ) :=
    ⟨R.continuous.measurable, stdGaussian_map R⟩
  have h := (cplx_mp.symm _).comp (hR.comp cplx_mp)
  convert h using 1
  funext p
  simp only [Function.comp_apply, R, rotation_apply, Complex.measurableEquivRealProd_symm_apply,
    Circle.coe_exp]
  rw [MeasurableEquiv.symm_symm, Complex.measurableEquivRealProd_apply]
  have he : Complex.exp (((-s : ℝ) : ℂ) * Complex.I) = ⟨Real.cos s, -Real.sin s⟩ := by
    apply Complex.ext
    · simp [Complex.exp_re]
    · simp [Complex.exp_im]
  rw [he]
  simp only [Complex.mul_re, Complex.mul_im, Prod.mk.injEq]
  constructor <;> ring

/-- **Rotation invariance**: `(X, Y) ↦ (X_s, Y_s)` preserves `γ ⊗ γ`. -/
theorem rot_preserving {ι : Type*} [Fintype ι] (s : ℝ) :
    MeasurePreserving (fun w : (ι → ℝ) × (ι → ℝ) => (rotX s w.1 w.2, rotY s w.1 w.2))
      ((stdGauss ι).prod (stdGauss ι)) ((stdGauss ι).prod (stdGauss ι)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ => gaussianReal 0 1)
    (fun _ => gaussianReal 0 1)
  have hpi := measurePreserving_pi (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1)) (fun _ => rot2_mp s)
  have h := he.comp (hpi.comp (he.symm _))
  unfold BstLean.Part29.stdGauss
  convert h using 1
  funext w
  rfl

end BstLean.Part48
