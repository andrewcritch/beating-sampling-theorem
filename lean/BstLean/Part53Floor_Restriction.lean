import BstLean.Part53Defs

/-!
Constant-coordinate restriction for the tensor variance in Prop F.
The constant coordinate of the raw feature vector is exactly one. Restricting all
but one tensor slot to this coordinate retains the full feature variance.
-/

namespace BstLean.Part53

open MeasureTheory
open BstLean.Part41 (varU phiM Mono frob)

private lemma variance_const_mul {n : ℕ} (μ : Measure (Fin n → ℝ)) (a : ℝ)
    (h : (Fin n → ℝ) → ℝ) :
    varU μ (fun x => a * h x) = a ^ 2 * varU μ h := by
  unfold varU
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [integral_const_mul]
  ring

private def restrictionWord {ι : Type*} (o : ι) (c : ℕ) (p : ι) : Fin (c + 1) → ι :=
  Fin.cases p (fun _ => o)

private lemma restrictionWord_injective {ι : Type*} (o : ι) (c : ℕ) :
    Function.Injective (restrictionWord o c) := by
  intro p q h
  exact congrFun h 0

/-- Restrict all but the first tensor slot to a coordinate equal to one. -/
theorem tensor_feature_variance_floor53 {n : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (Fin n → ℝ)) (ψ : (Fin n → ℝ) → ι → ℝ)
    (o : ι) (ho : ∀ x, ψ x o = 1) (c : ℕ) :
    (∑ p : ι, varU μ (fun x => ψ x p)) ≤
      ∑ w : Fin (c + 1) → ι, varU μ (fun x => ∏ t, ψ x (w t)) := by
  classical
  let E (w : Fin (c + 1) → ι) := varU μ (fun x => ∏ t, ψ x (w t))
  have hE (w : Fin (c + 1) → ι) : 0 ≤ E w := by
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hrestrict (p : ι) : E (restrictionWord o c p) = varU μ (fun x => ψ x p) := by
    change varU μ (fun x => ∏ t, ψ x (restrictionWord o c p t)) = _
    apply congrArg (varU μ)
    funext x
    simp [restrictionWord, Fin.prod_univ_succ, ho]
  calc
    _ = ∑ p : ι, E (restrictionWord o c p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (hrestrict p).symm
    _ = ∑ w ∈ Finset.univ.image (restrictionWord o c), E w := by
      rw [Finset.sum_image]
      exact fun p _ q _ h => restrictionWord_injective o c h
    _ ≤ ∑ w, E w := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun w _ _ => hE w)

/-- The raw monomial feature has a constant coordinate at every point. -/
theorem phiM_default_floor53 {n d : ℕ} (x : Fin n → ℝ) :
    phiM x (default : Mono n d) = 1 := by
  change ((0 : Multiset (Fin n)).map x).prod = 1
  simp

/-- The tensor variance dominates the feature variance at every positive order. -/
theorem raw_feature_variance_floor53 {n d : ℕ} (μ : Measure (Fin n → ℝ)) (c : ℕ) :
    (∑ p : Mono n d, varU μ (fun x => phiM x p)) ≤
      ∑ w : Fin (c + 1) → Mono n d, varU μ (fun x => ∏ t, phiM x (w t)) := by
  exact tensor_feature_variance_floor53 μ (fun x p => phiM x p) default
    phiM_default_floor53 c

/-- A fixed coefficient tensor factors out of the feature variance. -/
theorem tensor_coefficient_variance_floor53 {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (μ : Measure (Fin n → ℝ))
    (ψ : (Fin n → ℝ) → ι → ℝ) (A : κ → ℝ)
    (o : ι) (ho : ∀ x, ψ x o = 1) (c : ℕ) :
    (∑ a, A a ^ 2) * (∑ p, varU μ (fun x => ψ x p)) ≤
      ∑ a, ∑ w : Fin (c + 1) → ι,
        varU μ (fun x => A a * ∏ t, ψ x (w t)) := by
  have hmain := tensor_feature_variance_floor53 μ ψ o ho c
  calc
    _ ≤ (∑ a, A a ^ 2) *
        (∑ w : Fin (c + 1) → ι, varU μ (fun x => ∏ t, ψ x (w t))) :=
      mul_le_mul_of_nonneg_left hmain (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by
      simp_rw [variance_const_mul]
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- The quadratic estimate used for the heat correction. -/
theorem floor_quadratic_correction53 (a b : ℝ) : a ^ 2 / 2 - b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a + 2 * b)]

/-- The trace of the coordinate covariance on the sphere. -/
theorem sphere_coordinate_variance53 {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ]
    (hsphere : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1)
    (hcoord : ∀ i : Fin n, Integrable (fun x => x i) μ)
    (hcoord2 : ∀ i : Fin n, Integrable (fun x => x i ^ 2) μ) :
    (∑ i : Fin n, varU μ (fun x => x i)) =
      1 - ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2 := by
  have hvar (i : Fin n) : varU μ (fun x => x i) =
      (∫ x, x i ^ 2 ∂μ) - (∫ x, x i ∂μ) ^ 2 := by
    unfold varU
    have he (x : Fin n → ℝ) :
        (x i - ∫ y, y i ∂μ) ^ 2 =
          x i ^ 2 - (2 * ∫ y, y i ∂μ) * x i + (∫ y, y i ∂μ) ^ 2 := by ring
    simp_rw [he]
    have hlin : Integrable (fun x : Fin n → ℝ => (2 * ∫ y, y i ∂μ) * x i) μ :=
      (hcoord i).const_mul _
    have hconst : Integrable (fun _x : Fin n → ℝ => (∫ y, y i ∂μ) ^ 2) μ :=
      integrable_const _
    rw [integral_add (μ := μ)
        (f := fun x : Fin n → ℝ => x i ^ 2 - (2 * ∫ y, y i ∂μ) * x i)
        (g := fun _x : Fin n → ℝ => (∫ y, y i ∂μ) ^ 2)
        ((hcoord2 i).sub hlin) hconst,
      integral_sub (hcoord2 i) hlin, integral_const_mul]
    simp only [integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    ring
  simp_rw [hvar]
  rw [Finset.sum_sub_distrib, ← integral_finsetSum _ (fun i _ => hcoord2 i)]
  have he : (∫ x, ∑ i : Fin n, x i ^ 2 ∂μ) = 1 := by
    calc
      _ = ∫ _x : Fin n → ℝ, (1 : ℝ) ∂μ := integral_congr_ae hsphere
      _ = 1 := by simp
  rw [he]

private def linearFeature {n d : ℕ} (hd : 1 ≤ d) (a : Fin n) : Mono n d :=
  ⟨⟨1, by omega⟩, Sym.oneEquiv a⟩

private lemma linearFeature_eval {n d : ℕ} (hd : 1 ≤ d) (a : Fin n)
    (x : Fin n → ℝ) : phiM x (linearFeature hd a) = x a := by
  change (({a} : Multiset (Fin n)).map x).prod = x a
  simp

private lemma linearFeature_injective {n d : ℕ} (hd : 1 ≤ d) :
    Function.Injective (linearFeature (n := n) hd) := by
  classical
  intro a b h
  have he := congrArg (phiM (fun i => if i = a then (1 : ℝ) else 0)) h
  rw [linearFeature_eval, linearFeature_eval] at he
  by_contra hab
  have hba : b ≠ a := Ne.symm hab
  simp [hba] at he

/-- Keeping only the degree-one monomials retains the coordinate covariance. -/
theorem raw_feature_coordinate_variance53 {n d : ℕ} (μ : Measure (Fin n → ℝ))
    (hd : 1 ≤ d) :
    (∑ i : Fin n, varU μ (fun x => x i)) ≤
      ∑ p : Mono n d, varU μ (fun x => phiM x p) := by
  classical
  let E (p : Mono n d) := varU μ (fun x => phiM x p)
  have hE (p : Mono n d) : 0 ≤ E p := integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ = ∑ i : Fin n, E (linearFeature hd i) := by
      simp only [E, linearFeature_eval]
    _ = ∑ p ∈ Finset.univ.image (linearFeature hd), E p := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => linearFeature_injective hd h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => hE p)

/-- A bound on the coordinate mean gives a floor at every tensor order. -/
theorem sphere_tensor_variance53 {n d : ℕ} (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hsphere : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1)
    (hcoord : ∀ i : Fin n, Integrable (fun x => x i) μ)
    (hcoord2 : ∀ i : Fin n, Integrable (fun x => x i ^ 2) μ)
    (η : ℝ) (hmean : ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2 ≤ η) (c : ℕ) :
    1 - η ≤ ∑ w : Fin (c + 1) → Mono n d,
      varU μ (fun x => ∏ t, phiM x (w t)) := by
  calc
    _ ≤ 1 - ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2 := by linarith
    _ = ∑ i : Fin n, varU μ (fun x => x i) :=
      (sphere_coordinate_variance53 μ hsphere hcoord hcoord2).symm
    _ ≤ ∑ p : Mono n d, varU μ (fun x => phiM x p) :=
      raw_feature_coordinate_variance53 μ hd
    _ ≤ _ := raw_feature_variance_floor53 μ c

/-- Sum the main term and the heat correction, then absorb the correction. -/
theorem floor_absorb_correction53 {ι : Type*} [Fintype ι]
    (main correction energy : ι → ℝ) (N C : ℝ)
    (henergy : ∀ i, main i / 2 - correction i ≤ energy i)
    (hmain : N / 2 ≤ ∑ i, main i)
    (hcorrection : ∑ i, correction i ≤ C)
    (hsmall : C ≤ N / 8) :
    N / 8 ≤ ∑ i, energy i := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => henergy i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hsum
  linarith

end BstLean.Part53
