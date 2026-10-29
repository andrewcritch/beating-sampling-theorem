import BstLean.Part216NetworkLocation
import BstLean.Part186RA2

/-! Conditional means are functions of the original matrix and its two retained images. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part134 (lam res)

variable {m q : ℕ}

noncomputable def planeMean (v : ℝ) (h g : Fin m → ℝ)
    (f : Matrix (Fin q) (Fin m) ℝ → ℝ) (y z : Fin q → ℝ) : ℝ :=
  ∫ N, f (reb h y (reb (res h g) (z - lam h g • y) N)) ∂gaussMat q m v

lemma measurable_planeMean (v : ℝ) (h g : Fin m → ℝ)
    {f : Matrix (Fin q) (Fin m) ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) => planeMean v h g f p.1 p.2) := by
  have hr : Measurable (fun p : ((Fin q → ℝ) × (Fin q → ℝ)) ×
      Matrix (Fin q) (Fin m) ℝ =>
      reb h p.1.1 (reb (res h g) (p.1.2 - lam h g • p.1.1) p.2)) :=
    measurable_reb_comp measurable_const (measurable_fst.comp measurable_fst)
      (measurable_reb_comp measurable_const (by fun_prop) measurable_snd)
  exact (hf.comp hr).stronglyMeasurable.integral_prod_right'.measurable

noncomputable def originalPlaneMean (v : ℝ) (h g : Fin m → ℝ)
    (f : Matrix (Fin q) (Fin m) ℝ → ℝ) (M : Matrix (Fin q) (Fin m) ℝ) : ℝ :=
  planeMean v h g f (M *ᵥ h) (M *ᵥ g)

lemma measurable_originalPlaneMean (v : ℝ) (h g : Fin m → ℝ)
    {f : Matrix (Fin q) (Fin m) ℝ → ℝ} (hf : Measurable f) :
    Measurable (originalPlaneMean v h g f) :=
  (measurable_planeMean v h g hf).comp
    ((BstLean.Part167.measurable_mulVec_pair h).prodMk
      (BstLean.Part167.measurable_mulVec_pair g))

lemma planeMean_coordinates (v : ℝ) (h g : Fin m → ℝ)
    (f : Matrix (Fin q) (Fin m) ℝ → ℝ) (ξ₁ ξ₂ : Fin q → ℝ) :
    planeMean v h g f (cOf v h ξ₁)
      (lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂) =
      ∫ N, f (reb h (cOf v h ξ₁) (reb (res h g) (cOf v (res h g) ξ₂) N))
        ∂gaussMat q m v := by
  simp only [planeMean, add_sub_cancel_left]

/-- The moment is over one original matrix. Both retained images come from that matrix. -/
theorem originalPlaneFluct_moment (v : ℝ) (h g : Fin m → ℝ)
    {f : Matrix (Fin q) (Fin m) ℝ → ℝ} (hf : Measurable f) (k : ℕ) :
    (∫⁻ M, ENNReal.ofReal (|f M - originalPlaneMean v h g f M| ^ k)
      ∂gaussMat q m v) =
    ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal
      (|f (reb h (cOf v h ξ₁) (reb (res h g) (cOf v (res h g) ξ₂) N)) -
        ∫ P, f (reb h (cOf v h ξ₁) (reb (res h g) (cOf v (res h g) ξ₂) P))
          ∂gaussMat q m v| ^ k)
      ∂gaussMat q m v ∂stdGauss (Fin q) ∂stdGauss (Fin q) := by
  have hm : Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ×
      Matrix (Fin q) (Fin m) ℝ =>
      ENNReal.ofReal (|f p.2.2 - planeMean v h g f p.1 p.2.1| ^ k)) :=
    ((hf.comp (measurable_snd.comp measurable_snd)).sub
      ((measurable_planeMean v h g hf).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).abs.pow_const k
        |>.ennreal_ofReal
  have he := BstLean.Part167.plane_split v h g hm
  simpa only [originalPlaneMean, planeMean_coordinates] using he

theorem originalPlaneMean_moment (v : ℝ) (h g : Fin m → ℝ)
    {f : Matrix (Fin q) (Fin m) ℝ → ℝ} (hf : Measurable f) (k : ℕ) :
    (∫⁻ M, ENNReal.ofReal (|originalPlaneMean v h g f M| ^ k) ∂gaussMat q m v) =
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal
      (|∫ P, f (reb h (cOf v h ξ₁) (reb (res h g) (cOf v (res h g) ξ₂) P))
          ∂gaussMat q m v| ^ k) ∂stdGauss (Fin q) ∂stdGauss (Fin q) := by
  have hm : Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ×
      Matrix (Fin q) (Fin m) ℝ =>
      ENNReal.ofReal (|planeMean v h g f p.1 p.2.1| ^ k)) :=
    ((measurable_planeMean v h g hf).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).abs.pow_const k
      |>.ennreal_ofReal
  have he := BstLean.Part167.plane_split v h g hm
  simpa only [originalPlaneMean, planeMean_coordinates, lintegral_const,
    measure_univ, mul_one] using he

#print axioms originalPlaneFluct_moment
#print axioms originalPlaneMean_moment
end BstLean.Part223
