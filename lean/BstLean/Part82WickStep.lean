import BstLean.Part82Defs
import BstLean.Part78Wick
import BstLean.Part78MeanA

/-!
# Part 82: the Wick recursion for products of linear forms of a standard Gaussian vector
-/

namespace BstLean.Part82.WickAux

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part35 (stdGauss_wick_step stdGauss_prod_integrable)
open BstLean.Part78 (lin dot Good good_coord)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma good_lin (a : ι → ℝ) : Good (stdGauss ι) (fun u => lin a u) := by
  unfold lin
  exact Good.sum _ (fun j _ => (good_coord j).const_mul _)

lemma good_prod : ∀ (m : ℕ) (b : Fin m → ι → ℝ),
    Good (stdGauss ι) (fun u => ∏ k, lin (b k) u)
  | 0, b => by simpa using Good.const (μ := stdGauss ι) 1
  | m + 1, b => by
      simp_rw [Fin.prod_univ_succ]
      exact (good_lin _).mul (good_prod m _)

lemma prod_lin_ex {m : ℕ} (b : Fin m → ι → ℝ) (u : ι → ℝ) :
    ∏ k, lin (b k) u = ∑ f : Fin m → ι, (∏ k, b k (f k)) * ∏ k, u (f k) := by
  unfold lin
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

/-- The moment of a product of coordinates. -/
noncomputable def cm (ι : Type*) [Fintype ι] {m : ℕ} (g : Fin m → ι) : ℝ :=
  ∫ u, ∏ l, u (g l) ∂stdGauss ι

lemma int_prod_lin {m : ℕ} (b : Fin m → ι → ℝ) :
    ∫ u, ∏ k, lin (b k) u ∂stdGauss ι = ∑ g : Fin m → ι, (∏ k, b k (g k)) * cm ι g := by
  simp_rw [prod_lin_ex]
  rw [integral_finsetSum _ (fun g _ => (stdGauss_prod_integrable m g).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

lemma prod_erase {m : ℕ} (k : Fin (m + 1)) (F : Fin (m + 1) → ℝ) :
    ∏ l ∈ Finset.univ.erase k, F l = ∏ l : Fin m, F (k.succAbove l) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
    Finset.prod_image (fun x _ y _ h => Fin.succAbove_right_injective h)]

lemma coord_step (j : ι) {m : ℕ} (f : Fin (m + 1) → ι) :
    ∫ u, u j * ∏ l, u (f l) ∂stdGauss ι =
      ∑ k, if f k = j then cm ι (fun l => f (k.succAbove l)) else 0 := by
  rw [stdGauss_wick_step]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [prod_erase k]
  rfl

/-- **The Wick recursion for linear forms.** -/
theorem lin_step (a : ι → ℝ) {m : ℕ} (b : Fin (m + 1) → ι → ℝ) :
    ∫ u, lin a u * ∏ k, lin (b k) u ∂stdGauss ι =
      ∑ k, dot a (b k) * ∫ u, ∏ l : Fin m, lin (b (k.succAbove l)) u ∂stdGauss ι := by
  have hex (u : ι → ℝ) : lin a u * ∏ k, lin (b k) u =
      ∑ j, ∑ f : Fin (m + 1) → ι, (a j * ∏ k, b k (f k)) * (u j * ∏ k, u (f k)) := by
    rw [prod_lin_ex]
    unfold lin
    rw [Finset.sum_mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have hi (j : ι) (f : Fin (m + 1) → ι) :
      Integrable (fun u : ι → ℝ => u j * ∏ k, u (f k)) (stdGauss ι) := by
    have := stdGauss_prod_integrable (m + 2) (Fin.cons (α := fun _ => ι) j f)
    simpa [Fin.prod_univ_succ] using this
  simp_rw [hex]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun f _ => (hi j f).const_mul _))]
  simp_rw [integral_finsetSum _ (fun f _ => (hi _ f).const_mul _), integral_const_mul,
    coord_step, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset (Fin (m+1))))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [int_prod_lin]
  simp_rw [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← (Fin.insertNthEquiv (fun _ => ι) k).sum_comp, Fintype.sum_prod_type]
  unfold dot
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro g _
  simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [Fin.prod_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

/-! ### Concrete moments of five and six linear forms -/

open BstLean.Part78 (lin3 lin4)

private lemma sa4 (b c d e : ι → ℝ) (k : Fin 4) :
    (fun l : Fin 3 => ![b, c, d, e] (k.succAbove l)) =
      ![![c, d, e], ![b, d, e], ![b, c, e], ![b, c, d]] k := by
  fin_cases k <;> (funext l; fin_cases l <;> rfl)

private lemma sa5 (b c d e f : ι → ℝ) (k : Fin 5) :
    (fun l : Fin 4 => ![b, c, d, e, f] (k.succAbove l)) =
      ![![c, d, e, f], ![b, d, e, f], ![b, c, e, f], ![b, c, d, f], ![b, c, d, e]] k := by
  fin_cases k <;> (funext l; fin_cases l <;> rfl)

lemma lin5 (a b c d e : ι → ℝ) :
    ∫ u, lin a u * (lin b u * lin c u * lin d u * lin e u) ∂stdGauss ι = 0 := by
  have h := lin_step a ![b, c, d, e]
  have hs (k : Fin 4) : ∫ u, ∏ l : Fin 3, lin (![b, c, d, e] (k.succAbove l)) u ∂stdGauss ι = 0 := by
    have := congrFun (sa4 b c d e k)
    simp only [this]
    fin_cases k <;> simpa [Fin.prod_univ_succ, mul_assoc] using lin3 _ _ _
  simp only [hs, mul_zero, Finset.sum_const_zero] at h
  rw [← h]
  congr 1; funext u
  simp [Fin.prod_univ_succ, mul_assoc]

lemma lin6 (a b c d e f : ι → ℝ) :
    ∫ u, lin a u * (lin b u * lin c u * lin d u * lin e u * lin f u) ∂stdGauss ι =
      dot a b * (dot c d * dot e f + dot c e * dot d f + dot c f * dot d e) +
      dot a c * (dot b d * dot e f + dot b e * dot d f + dot b f * dot d e) +
      dot a d * (dot b c * dot e f + dot b e * dot c f + dot b f * dot c e) +
      dot a e * (dot b c * dot d f + dot b d * dot c f + dot b f * dot c d) +
      dot a f * (dot b c * dot d e + dot b d * dot c e + dot b e * dot c d) := by
  have h := lin_step a ![b, c, d, e, f]
  have hs (x y z w : ι → ℝ) : ∫ u, ∏ l : Fin 4, lin (![x, y, z, w] l) u ∂stdGauss ι =
      dot x y * dot z w + dot x z * dot y w + dot x w * dot y z := by
    rw [← lin4]
    congr 1; funext u
    simp [Fin.prod_univ_succ, mul_assoc]
  have hk (k : Fin 5) := congrFun (sa5 b c d e f k)
  simp only [hk] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simp [hs] at h
  have h' : ∫ u, lin a u * (lin b u * lin c u * lin d u * lin e u * lin f u) ∂stdGauss ι =
      ∫ u, lin a u * ∏ x, lin (![b, c, d, e, f] x) u ∂stdGauss ι := by
    congr 1; funext u
    simp [Fin.prod_univ_succ, mul_assoc]
  rw [h', h]
  ring

end BstLean.Part82.WickAux

#print axioms BstLean.Part82.WickAux.lin_step
#print axioms BstLean.Part82.WickAux.lin6
