import BstLean.Part81Defs
import BstLean.Part71Feature

/-!
# Part 81 (F3, general): the feature operator bound with constant `d + 1`, every map degree

`featOpGen : FeatOp n d (d + 1)`, from `Part71.Feat71.featureBound` by extending the coefficient
vector by zero at the constant monomial. Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part81.F3

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part41 (Mono phiM)

variable {n d : ℕ}

/-- A sum over the non-constant monomials is the full sum when the constant term vanishes. -/
lemma sumJJ0 (g : Mono n d → ℝ) (h0 : g default = 0) : ∑ q : JJ n d, g q.1 = ∑ p, g p := by
  classical
  have h : ∑ q : JJ n d, g q.1 =
      ∑ p ∈ Finset.univ.filter (fun p : Mono n d => p ≠ default), g p := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [h, Finset.filter_ne' Finset.univ (default : Mono n d),
    Finset.sum_erase_eq_sub (Finset.mem_univ _), h0, sub_zero]

/-- Reduction of `FeatOp` to a bound for coefficient vectors on `Mono n d` that vanish at the
constant monomial. -/
lemma featOp_of_mono (CF : ℝ)
    (h : ∀ a : Mono n d → ℝ, a default = 0 →
      ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n ≤ CF / (n : ℝ) * ∑ p, a p ^ 2) :
    FeatOp n d CF := by
  classical
  intro c
  let a : Mono n d → ℝ := fun p => if h : p ≠ default then c ⟨p, h⟩ else 0
  have ha0 : a default = 0 := by simp [a]
  have haq : ∀ q : JJ n d, a q.1 = c q := fun q => by simp [a, q.2]
  have e1 : ∀ x : Fin n → ℝ, ∑ q : JJ n d, c q * pf x q = ∑ p, a p * phiM x p := by
    intro x
    rw [← sumJJ0 (fun p => a p * phiM x p) (by simp [ha0])]
    exact Finset.sum_congr rfl (fun q _ => by rw [haq]; rfl)
  have e2 : ∑ q : JJ n d, c q ^ 2 = ∑ p, a p ^ 2 := by
    rw [← sumJJ0 (fun p => a p ^ 2) (by simp [ha0])]
    exact Finset.sum_congr rfl (fun q _ => by rw [haq])
  simp_rw [e1]
  rw [e2]
  exact h a ha0

end BstLean.Part81.F3

namespace BstLean.Part81

/-- **(C) Feature operator bound with constant `d + 1`, every map degree.** -/
theorem featOpGen (n d : ℕ) (hn : 1 ≤ n) : FeatOp n d ((d : ℝ) + 1) :=
  F3.featOp_of_mono _ fun a ha0 => BstLean.Part71.Feat71.featureBound d n hn a ha0

end BstLean.Part81

#print axioms BstLean.Part81.featOpGen
