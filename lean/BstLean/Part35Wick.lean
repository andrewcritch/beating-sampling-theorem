import BstLean.Part35Defs

/-!
# Part 35, wave 1: Gaussian integration by parts on coordinate products (medium)

Generic in the index type. `E[z_i ∏ₛ z_{τ s}] = Σ_{s : τ s = i} E[∏_{s' ≠ s} z_{τ s'}]` (Wick's recursion). It follows
from Part 29's `gaussProd_moment` (reindexed along `Fintype.equivFin`) and `gaussMom (k+2) = (k+1) gaussMom k`.
`Part35GaussQuad` uses it to evaluate the degree-8 moments.
-/

namespace BstLean.Part35

open MeasureTheory
open BstLean.Part29 (stdGauss gaussMom)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stdGauss_prod_integrable (r : ℕ) (τ : Fin r → ι) :
    Integrable (fun z : ι → ℝ => ∏ s, z (τ s)) (stdGauss ι) := by
  classical
  have hp (z : ι → ℝ) : (∏ s, z (τ s)) =
      ∏ i, z i ^ (Finset.univ.filter fun s => τ s = i).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ z).symm
  simp_rw [hp]
  exact Integrable.fintype_prod (f := fun i x => x ^
    (Finset.univ.filter fun s => τ s = i).card) (fun i =>
      ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
        (X := fun x : ℝ => x) (by simp) _)

/-- The product moment: `E ∏ₛ z_{τ s} = ∏ᵢ gaussMom (#{s | τ s = i})`. -/
theorem stdGauss_prod_moment (r : ℕ) (τ : Fin r → ι) :
    ∫ z, ∏ s, z (τ s) ∂stdGauss ι = ∏ i, gaussMom (Finset.univ.filter fun s => τ s = i).card := by
  classical
  have hp (z : ι → ℝ) : (∏ s, z (τ s)) =
      ∏ i, z i ^ (Finset.univ.filter fun s => τ s = i).card := by
    simpa using (Finset.prod_fiberwise' Finset.univ τ z).symm
  simp_rw [hp]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun (i : ι) (x : ℝ) => x ^
    (Finset.univ.filter fun s => τ s = i).card)]
  simp_rw [BstLean.Part29.gaussMom_eq]

private lemma moment_finset {κ : Type*} [DecidableEq κ] (S : Finset κ) (τ : κ → ι) :
    ∫ z, ∏ s ∈ S, z (τ s) ∂stdGauss ι =
      ∏ j, gaussMom (S.filter fun s => τ s = j).card := by
  have hp (z : ι → ℝ) : (∏ s ∈ S, z (τ s)) =
      ∏ j, z j ^ (S.filter fun s => τ s = j).card := by
    simpa using (Finset.prod_fiberwise' S τ z).symm
  simp_rw [hp]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun (j : ι) (x : ℝ) =>
    x ^ (S.filter fun s => τ s = j).card)]
  simp_rw [BstLean.Part29.gaussMom_eq]

private lemma mom_rec (k : ℕ) : gaussMom (k + 2) = (k + 1 : ℝ) * gaussMom k := by
  unfold gaussMom
  have h : Even (k + 2) ↔ Even k := by simp [Nat.even_add]
  simp only [h]
  split_ifs with hk
  · rw [show k + 2 - 1 = k + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl
  · ring

/-- Wick's recursion. -/
theorem stdGauss_wick_step (i : ι) (r : ℕ) (τ : Fin r → ι) :
    ∫ z, z i * ∏ s, z (τ s) ∂stdGauss ι =
      ∑ s, if τ s = i then ∫ z, ∏ s' ∈ Finset.univ.erase s, z (τ s') ∂stdGauss ι else 0 := by
  classical
  let C (j : ι) := (Finset.univ.filter fun s => τ s = j).card
  let P := ∏ j ∈ Finset.univ.erase i, gaussMom (C j)
  have hl : (∫ z, z i * ∏ s, z (τ s) ∂stdGauss ι) = gaussMom (C i + 1) * P := by
    have he (z : ι → ℝ) : z i * ∏ s, z (τ s) =
        ∏ s : Fin (r + 1), z (Fin.cons (α := fun _ => ι) i τ s) := by
      simp [Fin.prod_univ_succ]
    simp_rw [he]
    rw [stdGauss_prod_moment]
    have hc (j : ι) : (Finset.univ.filter fun s =>
        Fin.cons (α := fun _ => ι) i τ s = j).card =
        C j + if i = j then 1 else 0 := by
      simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, C]
      rw [Finset.sum_boole]
      simp [add_comm]
    simp_rw [hc]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [ite_eq_right (Ne.symm hji), add_zero]
  have hr (s : Fin r) (hs : τ s = i) :
      (∫ z, ∏ s' ∈ Finset.univ.erase s, z (τ s') ∂stdGauss ι) =
        gaussMom (C i - 1) * P := by
    rw [moment_finset]
    have hc (j : ι) : ((Finset.univ.erase s).filter fun s' => τ s' = j).card =
        if i = j then C j - 1 else C j := by
      rw [Finset.filter_erase]
      by_cases hij : i = j
      · simp [hij, C, Finset.card_erase_of_mem, hs]
      · have hn : s ∉ Finset.univ.filter (fun s' => τ s' = j) := by simp [hs, hij]
        simp [hij, Finset.erase_eq_of_notMem hn, C]
    simp_rw [hc]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [ite_eq_right (Ne.symm hji)]
  rw [hl]
  have he : (∑ s, if τ s = i then
      ∫ z, ∏ s' ∈ Finset.univ.erase s, z (τ s') ∂stdGauss ι else 0) =
      (C i : ℝ) * (gaussMom (C i - 1) * P) := by
    trans ∑ s : Fin r, if τ s = i then gaussMom (C i - 1) * P else 0
    · apply Finset.sum_congr rfl
      intro s _
      split_ifs with hs
      · exact hr s hs
      · rfl
    · rw [← Finset.sum_filter]
      simp [C]
  rw [he]
  by_cases h : C i = 0
  · simp [h, gaussMom]
  · have hk : C i = (C i - 1) + 1 := by omega
    rw [show C i + 1 = (C i - 1) + 2 by omega, mom_rec]
    have hc : (C i : ℝ) = (C i - 1 : ℕ) + 1 := by exact_mod_cast hk
    rw [hc]
    ring

end BstLean.Part35
