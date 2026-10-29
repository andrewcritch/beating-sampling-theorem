import BstLean.Part53Defs

namespace BstLean.Part53.FloorEnergy

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)

variable {n : ℕ}

lemma sphere_cont_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  letI := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma gaussian_eval_integrable {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e he
  have hprod (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) (e i))).const_mul _


private lemma separated_integral {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    (∫ Z, ∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ ∂stdGauss κ) =
      ∫ x, ∫ Z, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂stdGauss κ ∂μ := by
  classical
  have hx (Z : κ → ℝ) :
      (∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ) =
        ∑ i ∈ S, (∫ x, F i x ∂μ) * MvPolynomial.eval Z (G i) := by
    rw [integral_finsetSum _ (fun i hi => (sphere_cont_integrable hμ (hF i hi)).mul_const _)]
    simp only [integral_mul_const]
  have hZ (x : Fin n → ℝ) :
      (∫ Z, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂stdGauss κ) =
        ∑ i ∈ S, F i x * ∫ Z, MvPolynomial.eval Z (G i) ∂stdGauss κ := by
    rw [integral_finsetSum _ (fun i _ => (gaussian_eval_integrable (G i)).const_mul _)]
    simp only [integral_const_mul]
  simp_rw [hx, hZ]
  rw [integral_finsetSum _ (fun i _ => (gaussian_eval_integrable (G i)).const_mul _),
    integral_finsetSum _ (fun i hi => (sphere_cont_integrable hμ (hF i hi)).mul_const _)]
  simp only [integral_const_mul, integral_mul_const]

private lemma separated_square_integral {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    (∫ Z, ∫ x, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 ∂μ ∂stdGauss κ) =
      ∫ x, ∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 ∂stdGauss κ ∂μ := by
  classical
  have he (x : Fin n → ℝ) (Z : κ → ℝ) :
      (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 =
        ∑ ij ∈ S ×ˢ S, (F ij.1 x * F ij.2 x) * MvPolynomial.eval Z (G ij.1 * G ij.2) := by
    rw [pow_two, Finset.sum_mul, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul]
    ring
  simp_rw [he]
  apply separated_integral hμ
  intro ij hij
  exact (hF ij.1 (Finset.mem_product.mp hij).1).mul
    (hF ij.2 (Finset.mem_product.mp hij).2)


private lemma square_expand {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (x : Fin n → ℝ) (Z : κ → ℝ) :
    (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 =
      ∑ ij ∈ S ×ˢ S, (F ij.1 x * F ij.2 x) * MvPolynomial.eval Z (G ij.1 * G ij.2) := by
  classical
  rw [pow_two, Finset.sum_mul, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul]
  ring

private lemma mean_separated {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) (Z : κ → ℝ) :
    (∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ) =
      ∑ i ∈ S, (∫ x, F i x ∂μ) * MvPolynomial.eval Z (G i) := by
  rw [integral_finsetSum _ (fun i hi => (sphere_cont_integrable hμ (hF i hi)).mul_const _)]
  simp only [integral_mul_const]

private lemma mean_separated_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    Integrable (fun Z => ∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ) (stdGauss κ) := by
  simp_rw [mean_separated hμ S F G hF]
  exact integrable_finsetSum _ (fun i _ => (gaussian_eval_integrable (G i)).const_mul _)

private lemma mean_square_separated_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    Integrable (fun Z => ∫ x, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 ∂μ)
      (stdGauss κ) := by
  simp_rw [square_expand S F G]
  apply mean_separated_integrable hμ
  intro ij hij
  exact (hF ij.1 (Finset.mem_product.mp hij).1).mul
    (hF ij.2 (Finset.mem_product.mp hij).2)

private lemma square_mean_separated_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    Integrable (fun Z => (∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ) ^ 2)
      (stdGauss κ) := by
  simp_rw [mean_separated hμ S F G hF]
  have hp := gaussian_eval_integrable ((∑ i ∈ S, MvPolynomial.C (∫ x, F i x ∂μ) * G i) ^ 2)
  simpa only [map_pow, map_sum, map_mul, MvPolynomial.eval_C] using hp

lemma sphere_var_expansion {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
    varU μ f = (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  letI := hμ.prob
  unfold varU
  have he (x : Fin n → ℝ) :
      (f x - ∫ y, f y ∂μ) ^ 2 =
        f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x + (∫ y, f y ∂μ) ^ 2 := by ring
  simp_rw [he]
  have hlin : Integrable (fun x : Fin n → ℝ => (2 * ∫ y, f y ∂μ) * f x) μ :=
    (sphere_cont_integrable hμ hf).const_mul _
  have hsq : Integrable (fun x => f x ^ 2) μ := sphere_cont_integrable hμ (hf.pow 2)
  have hconst : Integrable (fun _x : Fin n → ℝ => (∫ y, f y ∂μ) ^ 2) μ := integrable_const _
  rw [integral_add (μ := μ)
      (f := fun x : Fin n → ℝ => f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x)
      (g := fun _x : Fin n → ℝ => (∫ y, f y ∂μ) ^ 2) (hsq.sub hlin) hconst,
    integral_sub hsq hlin, integral_const_mul]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  ring

private lemma cross_expand {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (x y : Fin n → ℝ) (Z : κ → ℝ) :
    (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) *
        (∑ i ∈ S, F i y * MvPolynomial.eval Z (G i)) =
      ∑ ij ∈ S ×ˢ S, (F ij.1 x * F ij.2 y) * MvPolynomial.eval Z (G ij.1 * G ij.2) := by
  classical
  rw [Finset.sum_mul, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul]
  ring

private lemma cross_gaussian_integral {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (x y : Fin n → ℝ) :
    (∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) *
        (∑ i ∈ S, F i y * MvPolynomial.eval Z (G i)) ∂stdGauss κ) =
      ∑ ij ∈ S ×ˢ S, (F ij.1 x * F ij.2 y) *
        ∫ Z, MvPolynomial.eval Z (G ij.1 * G ij.2) ∂stdGauss κ := by
  simp_rw [cross_expand S F G x y]
  rw [integral_finsetSum _ (fun ij _ => (gaussian_eval_integrable (G ij.1 * G ij.2)).const_mul _)]
  simp only [integral_const_mul]

private lemma separated_mean_square {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    (∫ Z, (∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ) ^ 2 ∂stdGauss κ) =
      ∫ x, ∫ y, ∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) *
        (∑ i ∈ S, F i y * MvPolynomial.eval Z (G i)) ∂stdGauss κ ∂μ ∂μ := by
  classical
  let I (ij : ι × ι) := ∫ Z, MvPolynomial.eval Z (G ij.1 * G ij.2) ∂stdGauss κ
  have hl : (∫ Z, (∫ x, ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i) ∂μ) ^ 2 ∂stdGauss κ) =
      ∑ ij ∈ S ×ˢ S, ((∫ x, F ij.1 x ∂μ) * (∫ x, F ij.2 x ∂μ)) * I ij := by
    simp_rw [mean_separated hμ S F G hF]
    have he (Z : κ → ℝ) := square_expand S
      (fun i (_x : Fin n → ℝ) => ∫ x, F i x ∂μ) G 0 Z
    simp_rw [he]
    rw [integral_finsetSum _ (fun ij _ =>
      (gaussian_eval_integrable (G ij.1 * G ij.2)).const_mul _)]
    simp only [integral_const_mul, I]
  have hy (x : Fin n → ℝ) :
      (∫ y, ∑ ij ∈ S ×ˢ S, (F ij.1 x * F ij.2 y) * I ij ∂μ) =
        ∑ ij ∈ S ×ˢ S, (F ij.1 x * (∫ y, F ij.2 y ∂μ)) * I ij := by
    rw [integral_finsetSum _ (fun ij hij =>
      ((sphere_cont_integrable hμ (hF ij.2 (Finset.mem_product.mp hij).2)).const_mul _).mul_const _)]
    simp only [integral_mul_const, integral_const_mul]
  rw [hl]
  simp_rw [cross_gaussian_integral S F G, ← show ∀ ij, I ij =
    ∫ Z, MvPolynomial.eval Z (G ij.1 * G ij.2) ∂stdGauss κ from fun _ => rfl, hy]
  rw [integral_finsetSum _ (fun ij hij =>
    ((sphere_cont_integrable hμ (hF ij.1 (Finset.mem_product.mp hij).1)).mul_const _).mul_const _)]
  simp only [integral_mul_const]

/-- Expected variance is the diagonal covariance minus the averaged covariance. -/
theorem separated_variance_pair {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ : Type*} [Fintype κ] (S : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    Integrable (fun Z => varU μ (fun x => ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)))
      (stdGauss κ) ∧
    (∫ Z, varU μ (fun x => ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ∂stdGauss κ) =
      (∫ x, ∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 ∂stdGauss κ ∂μ) -
        ∫ x, ∫ y, ∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) *
          (∑ i ∈ S, F i y * MvPolynomial.eval Z (G i)) ∂stdGauss κ ∂μ ∂μ := by
  have hc (Z : κ → ℝ) : Continuous (fun x => ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) :=
    continuous_finsetSum _ (fun i hi => (hF i hi).mul_const _)
  simp_rw [sphere_var_expansion hμ _ (hc _)]
  have h1 := mean_square_separated_integrable hμ S F G hF
  have h2 := square_mean_separated_integrable hμ S F G hF
  refine ⟨h1.sub h2, ?_⟩
  rw [integral_sub h1 h2, separated_square_integral hμ S F G hF,
    separated_mean_square hμ S F G hF]

/-- A finite covariance kernel gives the exact sum of centered kernel energies. -/
theorem finite_kernel_variance {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {ι κ α : Type*} [Fintype κ] (S : Finset ι) (R : Finset α)
    (F : ι → (Fin n → ℝ) → ℝ) (G : ι → MvPolynomial κ ℝ)
    (hF : ∀ i ∈ S, Continuous (F i))
    (K : α → (Fin n → ℝ) → ℝ) (hK : ∀ a ∈ R, Continuous (K a))
    (hpair : ∀ x y : Fin n → ℝ,
      (∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) *
          (∑ i ∈ S, F i y * MvPolynomial.eval Z (G i)) ∂stdGauss κ) =
        ∑ a ∈ R, K a x * K a y) :
    Integrable (fun Z => varU μ (fun x => ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)))
      (stdGauss κ) ∧
    (∫ Z, varU μ (fun x => ∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ∂stdGauss κ) =
      ∑ a ∈ R, varU μ (K a) := by
  obtain ⟨hint, he⟩ := separated_variance_pair hμ S F G hF
  refine ⟨hint, ?_⟩
  have hd (x : Fin n → ℝ) :
      (∫ Z, (∑ i ∈ S, F i x * MvPolynomial.eval Z (G i)) ^ 2 ∂stdGauss κ) =
        ∑ a ∈ R, K a x ^ 2 := by
    simpa only [pow_two] using hpair x x
  have hy (x : Fin n → ℝ) : (∫ y, ∑ a ∈ R, K a x * K a y ∂μ) =
      ∑ a ∈ R, K a x * (∫ y, K a y ∂μ) := by
    rw [integral_finsetSum _ (fun a ha => (sphere_cont_integrable hμ (hK a ha)).const_mul _)]
    simp only [integral_const_mul]
  rw [he]
  simp_rw [hd, hpair, hy]
  have hsq (a : α) (ha : a ∈ R) : Integrable (fun x => K a x ^ 2) μ :=
    sphere_cont_integrable hμ ((hK a ha).pow 2)
  rw [integral_finsetSum _ hsq,
    integral_finsetSum _ (fun a ha => (sphere_cont_integrable hμ (hK a ha)).mul_const _),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_mul_const, sphere_var_expansion hμ (K a) (hK a ha)]
  ring

end BstLean.Part53.FloorEnergy
