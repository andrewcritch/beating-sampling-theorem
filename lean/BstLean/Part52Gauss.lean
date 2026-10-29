import BstLean.Part29GaussProd
import BstLean.Part29Index

/-!
# Part 52, wave 3: products of coordinates under the standard Gaussian on `ℝ^ι`

Copies of Part 29's `gaussProd_integrable`, `gaussProd_moment` for an arbitrary finite index type, and
the pair formula used by Lemma P:

* `pair_moment`: if `b, b' : Fin k → ι` are injective and `b t = b' t'` forces `t = t'`, then
  `E[∏_t z_{b t} · ∏_t z_{b' t}] = [b = b']`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part52

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)

variable {ι ρ : Type} [Fintype ι] [Fintype ρ]

theorem gProd_integrable (τ : ρ → ι) :
    Integrable (fun z : ι → ℝ => ∏ r, z (τ r)) (stdGauss ι) := by
  classical
  have hp (z : ι → ℝ) : (∏ r, z (τ r)) =
      ∏ i, z i ^ (Finset.univ.filter fun r => τ r = i).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ z).symm
  simp_rw [hp]
  exact Integrable.fintype_prod (f := fun i x => x ^
    (Finset.univ.filter fun r => τ r = i).card) (fun i =>
      integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) _)

theorem gProd_moment [DecidableEq ι] (τ : ρ → ι) :
    ∫ z, ∏ r, z (τ r) ∂stdGauss ι = ∏ i, gaussMom (Finset.univ.filter fun r => τ r = i).card := by
  have hp (z : ι → ℝ) : (∏ r, z (τ r)) =
      ∏ i, z i ^ (Finset.univ.filter fun r => τ r = i).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ z).symm
  simp_rw [hp]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun (i : ι) (x : ℝ) => x ^
    (Finset.univ.filter fun r => τ r = i).card)]
  simp_rw [gaussMom_eq]

theorem gaussMom_zero : gaussMom 0 = 1 := by simp [gaussMom]
theorem gaussMom_one : gaussMom 1 = 0 := by simp [gaussMom]
theorem gaussMom_two : gaussMom 2 = 1 := by simp [gaussMom]

theorem pairProd_integrable {k : ℕ} (b b' : Fin k → ι) :
    Integrable (fun z : ι → ℝ => (∏ t, z (b t)) * ∏ t, z (b' t)) (stdGauss ι) := by
  have h := gProd_integrable (ρ := Fin k ⊕ Fin k) (Sum.elim b b')
  simpa [Fintype.prod_sum_type] using h

/-- **The pair formula.** -/
theorem pair_moment [DecidableEq ι] {k : ℕ} (b b' : Fin k → ι) (hb : Function.Injective b)
    (hrow : ∀ t t', b t = b' t' → t = t') :
    ∫ z, (∏ t, z (b t)) * (∏ t, z (b' t)) ∂stdGauss ι = if b = b' then 1 else 0 := by
  have h := gProd_moment (ρ := Fin k ⊕ Fin k) (Sum.elim b b')
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at h
  rw [h]
  have hcard : ∀ i, (Finset.univ.filter fun r : Fin k ⊕ Fin k => Sum.elim b b' r = i).card =
      (Finset.univ.filter fun t => b t = i).card + (Finset.univ.filter fun t => b' t = i).card := by
    intro i
    simp only [Finset.card_filter, Fintype.sum_sum_type]
    rfl
  have hle : ∀ i, (Finset.univ.filter fun t => b t = i).card ≤ 1 := by
    intro i
    rw [Finset.card_le_one]
    intro a ha a' ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hb (ha.trans ha'.symm)
  split_ifs with hbb
  · subst hbb
    apply Finset.prod_eq_one
    intro i _
    rw [hcard]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle i) with h0 | h1
    · rw [h0]; exact gaussMom_zero
    · rw [h1]; exact gaussMom_two
  · obtain ⟨t0, ht0⟩ : ∃ t0, b t0 ≠ b' t0 := by
      by_contra hc; push Not at hc; exact hbb (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ (b t0))
    rw [hcard]
    have h1 : (Finset.univ.filter fun t => b t = b t0).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨t0, ?_⟩
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hb h, fun h => h ▸ rfl⟩
    have h2 : (Finset.univ.filter fun t => b' t = b t0).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _ ht
      have := hrow t0 t ht.symm
      subst this
      exact ht0 ht.symm
    rw [h1, h2]
    exact gaussMom_one

end BstLean.Part52
