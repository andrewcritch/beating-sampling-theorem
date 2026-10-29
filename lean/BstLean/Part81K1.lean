import BstLean.Part81Defs
import BstLean.Part78SharpMom

/-!
# Part 81, the constants at map degree 1

At `d = 1` the non-constant monomials are the coordinates: `κ(x,y) = Σ x_i y_i`.

* `eD_one : eD 1 = 1`, `kap1_formula`.
* `featOp1 : FeatOp n 1 1` (with equality).
* `sphC1 : SphC n 1 0 1 0 0 1`.
-/

namespace BstLean.Part81.K1

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)
open BstLean.Part81

variable {n : ℕ}

/-- The coordinate monomial. -/
def lin1 (i : Fin n) : Mono n 1 := ⟨1, Sym.oneEquiv i⟩

lemma phi_lin1 (x : Fin n → ℝ) (i : Fin n) : phiM x (lin1 i) = x i := by
  show (Multiset.map x {i}).prod = x i
  simp

lemma sumJJ1 (g : Mono n 1 → ℝ) : ∑ q : JJ n 1, g q.1 = ∑ i, g (lin1 i) := by
  classical
  have h : ∑ q : JJ n 1, g q.1
      = ∑ p ∈ Finset.univ.filter (fun p : Mono n 1 => p ≠ default), g p := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [h, Finset.filter_ne' Finset.univ (default : Mono n 1),
    Finset.sum_erase_eq_sub (Finset.mem_univ _), Fintype.sum_sigma, Fin.sum_univ_two]
  have e0 : ∑ β : Sym (Fin n) 0, g ⟨0, β⟩ = g default := by
    rw [Fintype.sum_unique]
    congr 1
  have e1 : ∑ β : Sym (Fin n) 1, g ⟨1, β⟩ = ∑ i, g (lin1 i) :=
    (Fintype.sum_equiv (Sym.oneEquiv (α := Fin n)) (fun i => g (lin1 i))
      (fun β : Sym (Fin n) 1 => g ⟨1, β⟩) (fun i => rfl)).symm
  show (∑ β : Sym (Fin n) 0, g ⟨0, β⟩) + (∑ β : Sym (Fin n) 1, g ⟨1, β⟩) - g default = _
  rw [e0, e1]
  ring

lemma int_coord (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∫ y, ∑ i, x i * y i ∂uniformSphere n = 0 := by
  have h := BstLean.Part29.uniformSphere_moments n hn
  rw [integral_finsetSum _ (fun i _ => (h.int1 i).const_mul _)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, h.m1, mul_zero]

lemma int_sq (hn : 1 ≤ n) (a : Fin n → ℝ) :
    ∫ y, (∑ i, a i * y i) ^ 2 ∂uniformSphere n = (∑ i, a i * a i) / n := by
  have h := BstLean.Part78.int_lin_lin hn a a
  unfold BstLean.Part78.linF at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [sq]

lemma int_sphere_one (hn : 1 ≤ n) (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → F x = 1) :
    ∫ x, F x ∂uniformSphere n = 1 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h : ∫ x, F x ∂uniformSphere n = ∫ _x, (1 : ℝ) ∂uniformSphere n := by
    refine integral_congr_ae ?_
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact hF x hx
  rw [h]; simp

end BstLean.Part81.K1

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part41 (Mono phiM)

theorem eD_one : eD 1 = 1 := by
  unfold eD BstLean.Part53.c0
  norm_num [Finset.sum_range_succ]

theorem kap1_formula (n : ℕ) (x y : Fin n → ℝ) : kap 1 x y = ∑ i, x i * y i := by
  unfold kap pf
  rw [K1.sumJJ1 (fun p => phiM x p * phiM y p)]
  simp only [K1.phi_lin1]

/-- **Feature operator bound at map degree 1**, constant `1` (an equality). -/
theorem featOp1 (n : ℕ) (hn : 1 ≤ n) : FeatOp n 1 1 := by
  classical
  intro c
  let c' : Mono n 1 → ℝ := fun q => if h : q ≠ default then c ⟨q, h⟩ else 0
  have hc : ∀ q : JJ n 1, c' q.1 = c q := fun q => by simp [c', q.2]
  have e1 : ∀ x : Fin n → ℝ, ∑ q, c q * pf x q = ∑ i, c' (K1.lin1 i) * x i := by
    intro x
    rw [← (funext fun i => by rw [K1.phi_lin1] :
      (fun i => c' (K1.lin1 i) * phiM x (K1.lin1 i)) = fun i => c' (K1.lin1 i) * x i),
      ← K1.sumJJ1 (fun p => c' p * phiM x p)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hc]; rfl
  have e2 : ∑ q, c q ^ 2 = ∑ i, c' (K1.lin1 i) ^ 2 := by
    rw [← K1.sumJJ1 (fun p => c' p ^ 2)]
    exact Finset.sum_congr rfl fun q _ => by rw [hc]
  simp_rw [e1]
  rw [e2, K1.int_sq hn]
  apply le_of_eq
  rw [one_div, inv_mul_eq_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Sphere constants at map degree 1.** -/
theorem sphC1 (n : ℕ) (hn : 1 ≤ n) : SphC n 1 0 1 0 0 1 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hdiag : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → kap 1 x x = 1 := by
    intro x hx
    rw [kap1_formula, ← hx]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hy : ∀ x : Fin n → ℝ, ∫ y, kap 1 x y ∂uniformSphere n = 0 := by
    intro x
    simp only [kap1_formula]
    exact K1.int_coord hn x
  have htG : tG n 1 = 1 := by
    unfold tG; exact K1.int_sphere_one hn _ hdiag
  have hkk : kk2 n 1 = 1 := by
    unfold kk2
    exact K1.int_sphere_one hn _ fun x hx => by rw [hdiag x hx]; norm_num
  have hmm : mm1 n 1 = 0 := by
    unfold mm1; simp only [hy]; simp
  have hss : ss2 n 1 = 1 / (n : ℝ) := by
    unfold ss2
    simp only [kap1_formula, K1.int_sq hn]
    have h : ∫ x : Fin n → ℝ, (∑ i, x i * x i) / (n : ℝ) ∂uniformSphere n
        = ∫ _x : Fin n → ℝ, 1 / (n : ℝ) ∂uniformSphere n := by
      refine integral_congr_ae ?_
      filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      have : ∑ i, x i * x i = 1 := by
        rw [← hx]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
    rw [h]; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [SphC, eD_one, htG, hkk, hmm, hss]
  refine ⟨le_rfl, by simp, le_rfl, by simp, by positivity, le_rfl, by norm_num, by simp, ?_⟩
  intro x hx
  rw [hdiag x hx, hy x]
  exact ⟨le_rfl, le_rfl, le_rfl, zero_le_one⟩

end BstLean.Part81

#print axioms BstLean.Part81.eD_one
#print axioms BstLean.Part81.kap1_formula
#print axioms BstLean.Part81.featOp1
#print axioms BstLean.Part81.sphC1
