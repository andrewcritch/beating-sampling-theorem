import BstLean.Part56PropD_Kernel

/-! The covariance matrix estimate used to remove the anchor projection in Prop D. -/
namespace BstLean.Part56

open MeasureTheory

section
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
variable (μ : Measure X)

private lemma integral_sum_sum (F : ι → ι → X → ℝ)
    (hF : ∀ i j, Integrable (F i j) μ) :
    (∫ x, ∑ i, ∑ j, F i j x ∂μ) = ∑ i, ∑ j, ∫ x, F i j x ∂μ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hF i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (fun j _ => hF i j)

/-- The squared kernel integral is the squared Frobenius norm of its second moment matrix. -/
theorem gram_secondMoment (f : X → ι → ℝ)
    (hf : ∀ i j, Integrable (fun x => f x i * f x j) μ) :
    (∫ x, ∫ y, (∑ i, f x i * f y i) ^ 2 ∂μ ∂μ) =
      ∑ i, ∑ j, (∫ x, f x i * f x j ∂μ) ^ 2 := by
  classical
  have hexp (x y : X) : (∑ i, f x i * f y i) ^ 2 =
      ∑ i, ∑ j, (f x i * f x j) * (f y i * f y j) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hinner (x : X) :
      (∫ y, (∑ i, f x i * f y i) ^ 2 ∂μ) =
        ∑ i, ∑ j, (f x i * f x j) * ∫ y, f y i * f y j ∂μ := by
    simp_rw [hexp]
    rw [integral_sum_sum μ _ (fun i j => (hf i j).const_mul _)]
    simp_rw [integral_const_mul]
  simp_rw [hinner]
  rw [integral_sum_sum μ _ (fun i j => (hf i j).mul_const _)]
  simp_rw [integral_mul_const]
  simp only [pow_two]

/-- The square of a finite Gram kernel is integrable on the product law. -/
theorem gram_sq_integrable [SFinite μ] (f : X → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 μ) :
    Integrable (fun p : X × X => (∑ i, f p.1 i * f p.2 i) ^ 2) (μ.prod μ) := by
  classical
  have hexp (x y : X) : (∑ i, f x i * f y i) ^ 2 =
      ∑ i, ∑ j, (f x i * f x j) * (f y i * f y j) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexp]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((hf i).integrable_mul (hf j)).mul_prod ((hf i).integrable_mul (hf j))))

theorem cross_gram_sq_integrable [SFinite μ] (f g : X → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 μ) (hg : ∀ i, MemLp (fun x => g x i) 2 μ) :
    Integrable (fun p : X × X => (∑ i, f p.1 i * g p.2 i) ^ 2) (μ.prod μ) := by
  classical
  have hexp (x y : X) : (∑ i, f x i * g y i) ^ 2 =
      ∑ i, ∑ j, (f x i * f x j) * (g y i * g y j) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexp]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((hf i).integrable_mul (hf j)).mul_prod ((hg i).integrable_mul (hg j))))

theorem dot_sq_integrable (g : X → ι → ℝ)
    (hg : ∀ i, MemLp (fun x => g x i) 2 μ) (a : ι → ℝ) :
    Integrable (fun x => (∑ i, a i * g x i) ^ 2) μ := by
  have h : MemLp (fun x => ∑ i, a i * g x i) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => (hg i).const_mul (a i))
  convert h.integrable_mul h using 1
  ext x
  simp only [pow_two, Pi.mul_apply]

/-- Projection commutes with an integrable vector expectation. -/
theorem projectOff_integral (u : ι → ℝ) (f : X → ι → ℝ)
    (hf : ∀ i, Integrable (fun x => f x i) μ) (i : ι) :
    (∫ x, projectOff u (f x) i ∂μ) = projectOff u (fun j => ∫ x, f x j ∂μ) i := by
  have hs : Integrable (fun x => ∑ j, f x j * u j) μ :=
    integrable_finsetSum _ (fun j _ => (hf j).mul_const _)
  unfold projectOff
  rw [integral_sub (hf i) ((hs.div_const _).mul_const _), integral_mul_const,
    integral_div, integral_finsetSum _ (fun j _ => (hf j).mul_const _)]
  simp_rw [integral_mul_const]

private lemma projectOff_mul (u a : ι → ℝ) (c : ℝ) (i : ι) :
    projectOff u (fun j => a j * c) i = projectOff u a i * c := by
  classical
  have he : (∑ j, (a j * c) * u j) = (∑ j, a j * u j) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [projectOff, he]
  ring

theorem projectOff_memLp (u : ι → ℝ) (f : X → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 μ) (i : ι) :
    MemLp (fun x => projectOff u (f x) i) 2 μ := by
  have hs : MemLp (fun x => ∑ j, f x j * u j) 2 μ :=
    memLp_finsetSum Finset.univ (fun j _ => (hf j).mul_const (u j))
  convert (hf i).sub ((hs.mul_const (∑ j, u j ^ 2)⁻¹).mul_const (u i)) using 1
  ext x
  simp only [projectOff, div_eq_mul_inv, Pi.sub_apply]

/-- The projected second moment matrix is the original matrix projected on both sides. -/
theorem projectOff_secondMoment (u : ι → ℝ) (f : X → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 μ) (i j : ι) :
    (∫ x, projectOff u (f x) i * projectOff u (f x) j ∂μ) =
      projectOff u (fun j => projectOff u (fun i => ∫ x, f x i * f x j ∂μ) i) j := by
  classical
  have hp : ∀ i, MemLp (fun x => projectOff u (f x) i) 2 μ :=
    projectOff_memLp μ u f hf
  have he (x : X) : projectOff u (f x) i * projectOff u (f x) j =
      projectOff u (fun q => projectOff u (fun p => f x p * f x q) i) j := by
    simp_rw [projectOff_mul]
    rw [show (fun q => projectOff u (f x) i * f x q) =
      (fun q => f x q * projectOff u (f x) i) by ext q; ring, projectOff_mul]
    ring
  simp_rw [he]
  rw [projectOff_integral μ u _ (fun q => by
    simp_rw [projectOff_mul]
    exact (hp i).integrable_mul (hf q))]
  congr 1
  ext q
  exact projectOff_integral μ u _ (fun p => (hf p).integrable_mul (hf q)) i

/-- Removing an anchor cannot increase the squared kernel integral. -/
theorem projectOff_gram_integral_le (u : ι → ℝ) (f : X → ι → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) 2 μ) :
    (∫ x, ∫ y, (∑ i, projectOff u (f x) i * projectOff u (f y) i) ^ 2 ∂μ ∂μ) ≤
      ∫ x, ∫ y, (∑ i, f x i * f y i) ^ 2 ∂μ ∂μ := by
  have hp := projectOff_memLp μ u f hf
  rw [gram_secondMoment μ _ (fun i j => (hp i).integrable_mul (hp j)),
    gram_secondMoment μ _ (fun i j => (hf i).integrable_mul (hf j))]
  simp_rw [projectOff_secondMoment μ u f hf]
  exact projectOff_frob_le u _

end
end BstLean.Part56
