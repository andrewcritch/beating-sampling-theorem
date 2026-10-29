import BstLean.Part56Key_Linear

namespace BstLean.Part56

open MeasureTheory BstLean.Part29

noncomputable def linearPoly56 {n : ℕ} (a w : Fin n → ℝ) (l : Fin n) : Polynomial ℝ :=
  Polynomial.C (a l) + Polynomial.X * Polynomial.C (w l)

noncomputable def tensorPoly56 {n : ℕ} (j : ℕ) (a w : Fin n → ℝ)
    (τ : Fin j → Fin n) : Polynomial ℝ := ∏ t, linearPoly56 a w (τ t)

noncomputable def tensorCoeff56 {n : ℕ} (j i : ℕ) (a w : Fin n → ℝ)
    (τ : Fin j → Fin n) : ℝ := (tensorPoly56 j a w τ).coeff i

private lemma linear_power_coeff56 {R : Type*} [CommSemiring R] (a b : R) (j i : ℕ) :
    ((Polynomial.C a + Polynomial.X * Polynomial.C b) ^ j).coeff i =
      a ^ (j - i) * (j.choose i : R) * b ^ i := by
  have he : (Polynomial.C a + Polynomial.X * Polynomial.C b) ^ j =
      ((Polynomial.X + Polynomial.C a) ^ j).comp (Polynomial.C b * Polynomial.X) := by
    simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    congr 1
    ring
  rw [he, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X_add_C_pow]

private lemma tensor_bivariate56 {n : ℕ} (j : ℕ) (a w w' : Fin n → ℝ) :
    (∑ τ : Fin j → Fin n,
      (tensorPoly56 j a w τ).map Polynomial.C * Polynomial.C (tensorPoly56 j a w' τ)) =
      (∑ l, (linearPoly56 a w l).map Polynomial.C * Polynomial.C (linearPoly56 a w' l)) ^ j := by
  classical
  simp only [tensorPoly56, Polynomial.map_prod, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin j) (l : Fin n) =>
    (linearPoly56 a w l).map Polynomial.C * Polynomial.C (linearPoly56 a w' l))]
  simp

private lemma linear_bivariate56 {n : ℕ} (a w w' : Fin n → ℝ)
    (hw : dot56 a w = 0) (hw' : dot56 a w' = 0) :
    (∑ l, (linearPoly56 a w l).map Polynomial.C * Polynomial.C (linearPoly56 a w' l)) =
      Polynomial.C (Polynomial.C (dot56 a a)) +
        Polynomial.X * Polynomial.C (Polynomial.X * Polynomial.C (dot56 w w')) := by
  have he (l : Fin n) :
      (linearPoly56 a w l).map Polynomial.C * Polynomial.C (linearPoly56 a w' l) =
      Polynomial.C (Polynomial.C (a l * a l)) +
      Polynomial.C Polynomial.X * Polynomial.C (Polynomial.C (a l * w' l)) +
      Polynomial.X * Polynomial.C (Polynomial.C (a l * w l)) +
      Polynomial.X * Polynomial.C Polynomial.X * Polynomial.C (Polynomial.C (w l * w' l)) := by
    simp only [linearPoly56, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.C_add, Polynomial.C_mul]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum]
  change (∑ l, a l * w l) = 0 at hw
  change (∑ l, a l * w' l) = 0 at hw'
  rw [hw, hw']
  unfold dot56
  simp only [Polynomial.C_0, mul_zero, add_zero, Polynomial.C_mul]
  ring

/-- Orthogonality diagonalizes the homogeneous blocks of the ordered tensor feature. -/
theorem tensorCoeff_inner56 {n : ℕ} (j i : ℕ) (a w w' : Fin n → ℝ)
    (hw : dot56 a w = 0) (hw' : dot56 a w' = 0) :
    (∑ τ : Fin j → Fin n, tensorCoeff56 j i a w τ * tensorCoeff56 j i a w' τ) =
      (j.choose i : ℝ) * dot56 a a ^ (j - i) * dot56 w w' ^ i := by
  have h := congrArg (fun Q : Polynomial (Polynomial ℝ) => (Q.coeff i).coeff i)
    (tensor_bivariate56 j a w w')
  rw [linear_bivariate56 a w w' hw hw', linear_power_coeff56] at h
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    Polynomial.coeff_C_mul] at h
  unfold tensorCoeff56
  rw [h]
  rw [show (j.choose i : Polynomial ℝ) = Polynomial.C (j.choose i : ℝ) by simp]
  simp only [← Polynomial.C_pow, mul_pow]
  rw [← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    Polynomial.coeff_X_pow_self]
  ring

private lemma enum_exists56 {ι : Type*} {j : ℕ} (β : Sym ι j) :
    ∃ τ : Fin j → ι, Finset.univ.val.map τ = β.val := by
  have hen (m : Multiset ι) : ∃ (r : ℕ) (τ : Fin r → ι),
      r = m.card ∧ Finset.univ.val.map τ = m := by
    induction m using Quot.inductionOn with
    | h l => exact ⟨l.length, l.get, rfl, by simp [Fin.univ_val_map]⟩
  obtain ⟨r, τ, hr, hτ⟩ := hen β.val
  have hrj : r = j := hr.trans β.property
  clear hr
  subst r
  exact ⟨τ, hτ⟩

noncomputable def enum56 {ι : Type*} {j : ℕ} (β : Sym ι j) : Fin j → ι :=
  Classical.choose (enum_exists56 β)

theorem enum_spec56 {ι : Type*} {j : ℕ} (β : Sym ι j) :
    Finset.univ.val.map (enum56 β) = β.val := Classical.choose_spec (enum_exists56 β)

theorem enum_injective56 {ι : Type*} {j : ℕ} :
    Function.Injective (enum56 : Sym ι j → Fin j → ι) := by
  intro β γ h
  apply Subtype.ext
  rw [← enum_spec56 β, ← enum_spec56 γ, h]

theorem tensorPoly_enum56 {n : ℕ} (j : ℕ) (a w : Fin n → ℝ) (β : Sym (Fin n) j) :
    tensorPoly56 j a w (enum56 β) =
      ((β.val.map fun l => Polynomial.C (a l) + Polynomial.X * Polynomial.C (w l)).prod) := by
  rw [← enum_spec56 β, Multiset.map_map]
  rfl

private lemma continuous_multiset_coeff56 {n : ℕ} (a : Fin n → ℝ)
    (m : Multiset (Fin n)) (i : ℕ) :
    Continuous (fun w : Fin n → ℝ => ((m.map (linearPoly56 a w)).prod).coeff i) := by
  induction m using Multiset.induction_on generalizing i with
  | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : Polynomial ℝ).coeff i))
  | @cons l m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.coeff_mul]
    apply continuous_finsetSum
    intro p hp
    apply Continuous.mul
    · simp only [linearPoly56, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_mul_C, Polynomial.coeff_X]
      fun_prop
    · exact ih p.2

theorem continuous_tensorCoeff56 {n : ℕ} (j i : ℕ) (a : Fin n → ℝ) (τ : Fin j → Fin n) :
    Continuous (fun w => tensorCoeff56 j i a w τ) := by
  have h := continuous_multiset_coeff56 a (Finset.univ.val.map τ) i
  simpa only [Multiset.map_map, Finset.prod_map_val, tensorCoeff56, tensorPoly56,
    Function.comp_def] using h

theorem integrable_cont_perpDir56 {n : ℕ} (v : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) : Integrable (fun g => f (perpDir v g)) (stdGauss (Fin n)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound (hf.measurable.comp (measurable_perpDir56 v)).aestronglyMeasurable C
  filter_upwards [] with g
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · exact (abs_le.mp (perpDir_abs_le_one56 v g i)).1
  · exact (abs_le.mp (perpDir_abs_le_one56 v g i)).2

theorem integrable_tensorCoeff_product56 {n : ℕ} (v a : Fin n → ℝ) (j i : ℕ)
    (τ υ : Fin j → Fin n) : Integrable (fun g =>
      tensorCoeff56 j i a (perpDir v g) τ * tensorCoeff56 j i a (perpDir v g) υ)
      (stdGauss (Fin n)) :=
  integrable_cont_perpDir56 v _
    ((continuous_tensorCoeff56 j i a τ).mul (continuous_tensorCoeff56 j i a υ))

end BstLean.Part56
