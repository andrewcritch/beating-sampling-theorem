import BstLean.Part130Moments
import BstLean.Part109Gram

/-! Exact cubic moments of Gaussian diagonal forms. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130

lemma coordinate_three_squares {ι : Type} [Fintype ι] [DecidableEq ι] (i j k : ι) :
    Integrable (fun x : ι → ℝ => x i ^ 2 * x j ^ 2 * x k ^ 2) (stdGauss ι) ∧
    (∫ x : ι → ℝ, x i ^ 2 * x j ^ 2 * x k ^ 2 ∂stdGauss ι) =
      1 + (if i = j then 2 else 0) + (if i = k then 2 else 0) +
        (if j = k then 2 else 0) + (if i = j ∧ j = k then 8 else 0) := by
  let c : ι → ℕ := fun l => (if l = i then 2 else 0) +
    (if l = j then 2 else 0) + (if l = k then 2 else 0)
  have he : (fun x : ι → ℝ => ∏ l, x l ^ c l) =
      fun x => x i ^ 2 * x j ^ 2 * x k ^ 2 := by
    funext x
    simp only [c, pow_add, Finset.prod_mul_distrib]
    simp [pow_ite]
  have hi : Integrable (fun x : ι → ℝ => ∏ l, x l ^ c l) (stdGauss ι) :=
    Integrable.fintype_prod (fun l => integrable_pow_gauss (c l))
  refine ⟨he ▸ hi, ?_⟩
  rw [← he, stdGauss, integral_fintype_prod_eq_prod (fun l (x : ℝ) => x ^ c l)]
  simp_rw [gaussMom_eq]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      have hc : ∀ l, gaussMom (c l) = if l = i then 15 else 1 := by
        intro l; by_cases h : l = i <;> simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff]
      simp_rw [hc]
      norm_num
    · have hc : ∀ l, gaussMom (c l) = if l = i then 3 else 1 := by
        intro l; by_cases h : l = i
        · subst l; simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff, eq_comm]
        · by_cases h' : l = k <;> simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff]
      simp_rw [hc]
      norm_num [hik]
  · by_cases hik : i = k
    · subst k
      have hc : ∀ l, gaussMom (c l) = if l = i then 3 else 1 := by
        intro l; by_cases h : l = i
        · subst l; simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff, eq_comm]
        · by_cases h' : l = j <;> simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff]
      simp_rw [hc]
      norm_num [hij, Ne.symm hij]
    · by_cases hjk : j = k
      · subst k
        have hc : ∀ l, gaussMom (c l) = if l = j then 3 else 1 := by
          intro l; by_cases h : l = j
          · subst l; simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff, eq_comm]
          · by_cases h' : l = i <;> simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff]
        simp_rw [hc]
        norm_num [hij]
      · have hc : ∀ l, gaussMom (c l) = 1 := by
          intro l
          by_cases h : l = i
          · subst l; simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff, eq_comm]
          · by_cases h' : l = j
            · subst l; simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff, eq_comm]
            · by_cases h'' : l = k <;> simp_all [c, gaussMom, Nat.doubleFactorial, Nat.even_iff]
        simp_rw [hc]
        simp [hij, hik, hjk]

/-- The cubic moment retains the trace, squared trace and cubic trace terms. -/
theorem diagonal_cubic {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    Integrable (fun x : ι → ℝ => (∑ i, a i * x i ^ 2) ^ 3) (stdGauss ι) ∧
    (∫ x : ι → ℝ, (∑ i, a i * x i ^ 2) ^ 3 ∂stdGauss ι) =
      (∑ i, a i) ^ 3 + 6 * (∑ i, a i) * (∑ i, a i ^ 2) + 8 * ∑ i, a i ^ 3 := by
  have he : ∀ x : ι → ℝ, (∑ i, a i * x i ^ 2) ^ 3 =
      ∑ i, ∑ j, ∑ k, (a i * a j * a k) * (x i ^ 2 * x j ^ 2 * x k ^ 2) := by
    intro x
    calc
      _ = (∑ i, a i * x i ^ 2) * (∑ i, a i * x i ^ 2) * (∑ i, a i * x i ^ 2) := by ring
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _; ring
  have hi := fun i j k => (coordinate_three_squares i j k).1.const_mul (a i * a j * a k)
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => hi i j k))), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => hi i j k)))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi _ j k)),
    integral_finsetSum _ (fun k _ => hi _ _ k), integral_const_mul,
    (coordinate_three_squares _ _ _).2]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end BstLean.Part218
#print axioms BstLean.Part218.diagonal_cubic
