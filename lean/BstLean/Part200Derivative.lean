import BstLean.Part200Error
import BstLean.Part167J

/-! The fixed-pair vector is the actual tangential derivative almost everywhere in weights. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Matrix Filter Topology
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part151 (jac)
open BstLean.Part167 (NoKink noKink_ae hid2_eventuallyEq_jac)

variable {n m p : ℕ}

noncomputable def pairTest (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x' z : Fin n → ℝ) : ℝ :=
  hid2 A₁ A₂ z ⬝ᵥ hid2 A₁ A₂ x'

noncomputable def pairLinear (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ l, ((jac A₁ A₂ x)ᵀ *ᵥ hid2 A₁ A₂ x') l • ContinuousLinearMap.proj l

lemma pairLinear_apply (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' z : Fin n → ℝ) :
    pairLinear A₁ A₂ x x' z = (jac A₁ A₂ x *ᵥ z) ⬝ᵥ hid2 A₁ A₂ x' := by
  simp only [pairLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

/-- Local linearity includes a zero first-layer feature; no division by its length occurs. -/
theorem pairTest_hasFDerivAt (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ)
    (h : NoKink A₁ A₂ x) :
    HasFDerivAt (pairTest A₁ A₂ x') (pairLinear A₁ A₂ x x') x := by
  have he := hid2_eventuallyEq_jac h
  apply (pairLinear A₁ A₂ x x').hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [he] with z hz
  rw [pairLinear_apply]
  exact congrArg (fun a => a ⬝ᵥ hid2 A₁ A₂ x') hz

noncomputable def pairGradient (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ) : Fin n → ℝ :=
  fun l => fderiv ℝ (pairTest A₁ A₂ x') x (Pi.single l 1)

lemma pairGradient_eq (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ)
    (h : NoKink A₁ A₂ x) :
    pairGradient A₁ A₂ x x' = (jac A₁ A₂ x)ᵀ *ᵥ hid2 A₁ A₂ x' := by
  funext l
  unfold pairGradient
  rw [(pairTest_hasFDerivAt A₁ A₂ x x' h).fderiv]
  simp [pairLinear, Pi.single_apply]

lemma projT_transpose (x : Fin n → ℝ) : (projT x)ᵀ = projT x := by
  ext i j
  simp only [projT, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply]
  congr 1
  · simp [eq_comm]
  · ring

theorem pairVector_eq_gradient (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ)
    (h : NoKink A₁ A₂ x) :
    pairVector A₁ A₂ x x' = projT x *ᵥ pairGradient A₁ A₂ x x' := by
  rw [pairGradient_eq A₁ A₂ x x' h]
  simp only [pairVector, jacT, Matrix.transpose_mul, projT_transpose,
    Matrix.mulVec_mulVec]

/-- The derivative identity holds for a deterministic nonzero input and Gaussian weights. -/
theorem pairVector_eq_gradient_ae {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    {x : Fin n → ℝ} (hx : x ≠ 0) (x' : Fin n → ℝ) :
    ∀ᵐ θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ
      ∂((gaussMat m n v₁).prod (gaussMat p m v₂)),
      pairVector θ.1 θ.2 x x' = projT x *ᵥ pairGradient θ.1 θ.2 x x' :=
  (noKink_ae hv₁ hv₂ hx).mono fun θ h => pairVector_eq_gradient θ.1 θ.2 x x' h

/-- The coarse all-order bound controls the actual derivative error, not only a mask matrix. -/
theorem derivativeError_joint_moment {s : ℕ} (hs : 1 ≤ s) {v₁ v₂ : ℝ}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) (α : ℝ) (v : Fin n → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      nrm (α • (projT x *ᵥ pairGradient θ.1 θ.2 x x') - v) ^ s)
      ((gaussMat m n v₁).prod (gaussMat p m v₂)) ∧
    (∫ θ, nrm (α • (projT x *ᵥ pairGradient θ.1 θ.2 x x') - v) ^ s
      ∂((gaussMat m n v₁).prod (gaussMat p m v₂))) ≤
      2 ^ (s - 1) * (|α| ^ s *
        (matrixMoment m n s v₁ * matrixMoment p m s v₂ * nrm x' ^ s) + nrm v ^ s) := by
  have hx0 : x ≠ 0 := by
    intro h; simp [h, normSq] at hx
  have he := (pairVector_eq_gradient_ae (m := m) (p := p) hv₁ hv₂ hx0 x').mono
    (fun θ h => congrArg (fun z => nrm (α • z - v) ^ s) h)
  obtain ⟨hi, hb⟩ := pairError_joint_moment (m := m) (p := p) hs hv₁.le hv₂.le hx x' α v
  exact ⟨hi.congr he, (integral_congr_ae he).symm.trans_le hb⟩

end BstLean.Part200
