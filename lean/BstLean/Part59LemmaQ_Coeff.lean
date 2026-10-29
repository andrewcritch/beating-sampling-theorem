import BstLean.Part59Defs
import BstLean.Part53Cost_Orbits

namespace BstLean.Part59
open BstLean.Part41 (Mono Tens IsSymmT mset wordOf)
open BstLean.Part53 (TF fvA)
open BstLean.Part53.CostAux

set_option backward.isDefEq.respectTransparency false

lemma tensOf_symm59x (n k : ℕ) (c : Mono n k → ℝ) :
    ∀ j, IsSymmT (tensOf k c j) := by
  classical
  intro j σ w
  have hm : mset (w ∘ σ) = mset w := by
    unfold mset
    rw [← Multiset.map_map]
    congr 1
    exact Multiset.map_univ_val_equiv σ
  simp only [tensOf]
  split_ifs with h
  · have hmono : monoOf k h (w ∘ σ) = monoOf k h w := by
      unfold monoOf
      congr 1
      exact Subtype.ext hm
    rw [hmono]
    simp only [orb, hm]
  · rfl

lemma orb_wordOf59x {n j : ℕ} [Inhabited (Fin n)] (q : Sym (Fin n) j) :
    (orb (wordOf j q.val) : ℝ) = (orbitCount q : ℝ) := by
  classical
  rw [orb, mset_wordOf _ _ q.property, orbitCount_multinomial,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  rfl

lemma orbitCount_pos59x {n j : ℕ} [Inhabited (Fin n)] (q : Sym (Fin n) j) :
    0 < orbitCount q := by
  classical
  unfold orbitCount
  apply Finset.card_pos.mpr
  exact ⟨wordOf j q.val, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, mset_wordOf _ _ q.property⟩⟩

lemma fvA_tensOf59x {n k : ℕ} [Inhabited (Fin n)] (c : Mono n k → ℝ)
    (y : Fin n → ℝ) : fvA k (tensOf k c) y = polyEval k c y := by
  classical
  rw [fvA_orbit_mono _ (tensOf_symm59x n k c)]
  apply Finset.sum_congr rfl
  intro p hp
  have hk : p.1.val ≤ k := by omega
  have he : monoOf k hk (wordOf p.1.val p.2.val) = p := by
    unfold monoOf
    cases p with
    | mk i q =>
      congr 1
      exact Subtype.ext (mset_wordOf _ _ q.property)
  simp only [tensOf, dif_pos hk, he, orb_wordOf59x, polyEval,
    BstLean.Part41.phiM]
  have hn : (orbitCount p.2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (orbitCount_pos59x p.2))
  field_simp

lemma TF_tensOf59x (n k : ℕ) (c : Mono n k → ℝ) :
    TF k (c default) (tensOf k c) = tensOf k c := by
  funext j w
  unfold TF tensOf
  split_ifs with hz hk hk
  · subst j
    have hm : monoOf k hk w = (default : Mono n k) := by
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Subtype.ext
      simp [monoOf, mset]
    rw [hm]
    simp [orb, mset, Nat.multinomial]
  · omega
  · rfl
  · rfl

end BstLean.Part59
