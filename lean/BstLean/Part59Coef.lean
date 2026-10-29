import BstLean.Part59Defs
import BstLean.Part53Cost_Orbits
import BstLean.Part53Laws

/-!
# Part 59, wave 1: Coefficient form and tensor form of `f`

Specification: `delegations/answers/p59-spec-opus.md` §3.3.

Suggested route.
* Symmetry: `mset (w ∘ σ) = mset w` (`Multiset.map` over `Finset.univ.val` is invariant under a
  permutation), so `monoOf` and `orb` agree; the dependent index `j` is fixed.
* `contr (tensOf k c j) (fun _ => y) = Σ_{|α| = j} c_α y^α` for `1 ≤ j ≤ k`: group the words `w` by
  `mset w` (`Finset.sum_fiberwise`); the fibre of `α` has `orb` elements (`Nat.multinomial`; Mathlib's
  `Multiset.multinomial`/`Sym` counting, or Part 41's `wordOf` and orbit lemmas in `Part41*.lean` and
  Part 53's `Part53Cost_Orbits.lean`), and on it `Π_t y_{w t} = monoVal y α`.
* Then split `Σ_{α : Mono n k}` by degree (`Fintype.sum_sigma`); degree `0` gives `c default`.
* `TopNZ → 0 < frob`: the word `wordOf k α` of a top monomial `α` with `c α ≠ 0` has
  `tensOf k c k (wordOf k α) = c α / orb ≠ 0`; `frob` is a sum of squares.

Replace each `sorry` by a proof. Do not edit the statements or `Part59Defs.lean`. Do not use
`native_decide` or `axiom` anywhere. This file imports `Part59Defs` only; a prover may also import
finished files of Parts 29–58, but no other Part 59 wave-1 file. Name private helpers with the suffix
`59x` or make them `private`, so that `Part59Final` does not see a name clash.
-/

namespace BstLean.Part59

set_option backward.isDefEq.respectTransparency false

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

open BstLean.Part41 (mset wordOf)
open BstLean.Part53.CostAux (orbitCount mset_wordOf orbitCount_multinomial monoVal_wordOf)

private lemma symm59x (k : ℕ) (c : Mono n k → ℝ) (j : ℕ) :
    IsSymmT (tensOf k c j) := by
  intro σ w
  have hm : mset (w ∘ σ) = mset w := by
    simp only [mset, Fin.univ_val_map]
    exact Quot.sound (σ.ofFn_comp_perm w)
  simp only [tensOf, monoOf, orb, hm]

private lemma orb_count59x {j : ℕ} (w : Fin j → Fin n) :
    (orb w : ℝ) = (orbitCount (⟨mset w, by simp [mset]⟩ : Sym (Fin n) j) : ℝ) := by
  rw [orbitCount_multinomial]
  congr 1
  unfold orb
  have hf : (fun i => (mset w).count i) = ⇑(mset w).toFinsupp := by
    funext i
    exact (Multiset.toFinsupp_apply _ _).symm
  rw [hf]
  exact (Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)).symm

private lemma mono_word59x [Inhabited (Fin n)] (k : ℕ) (p : Mono n k) :
    monoOf k (by omega : p.1.val ≤ k) (wordOf p.1.val p.2.val) = p := by
  apply Sigma.ext
  · exact Fin.eta _ _
  · simp only [monoOf, mset_wordOf _ _ p.2.property]
    rfl

private lemma orb_ne59x {j : ℕ} (w : Fin j → Fin n) : (orb w : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos _ _))

private lemma zero_tensor59x (k : ℕ) (c : Mono n k → ℝ) (w : Fin 0 → Fin n) :
    tensOf k c 0 w = c default := by
  have hm : mset w = 0 := by simp [mset]
  have ho : orb w = 1 := by simp [orb, hm, Nat.multinomial]
  have hmono : monoOf k (Nat.zero_le k) w = (default : Mono n k) := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact hm
  simp [tensOf, ho, hmono]

private lemma fval_fvA59x (k : ℕ) (c : Mono n k → ℝ) (y : Fin n → ℝ) :
    fval k (c default) (tensOf k c) y = fvA k (tensOf k c) y := by
  unfold fvA fval
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by rfl,
      Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm 1 i]
  · simp [contr, zero_tensor59x]

/-- **Coefficient form = tensor form.** -/
theorem coefTens59 : CoefTens59 := by
  classical
  intro n k c
  refine ⟨fun j _ _ => symm59x k c j, ?_, ?_⟩
  · intro y
    rw [fval_fvA59x]
    by_cases hn : n = 0
    · subst n
      have hdeg (p : Mono 0 k) : p = default := by
        have hm : p.2.val = 0 := Multiset.eq_zero_of_forall_notMem (by
          intro a; exact Fin.elim0 a)
        have hj : p.1 = 0 := Fin.ext (by
          have hh := p.2.property
          rw [hm, Multiset.card_zero] at hh
          exact hh.symm)
        apply Sigma.ext hj
        cases p with
        | mk i q =>
          dsimp at hj hm ⊢
          subst i
          apply heq_of_eq
          apply Subtype.ext
          exact hm
      let : Unique (Mono 0 k) := ⟨inferInstance, hdeg⟩
      unfold fvA polyEval
      rw [Finset.sum_range_succ']
      have hz (j : ℕ) : contr (tensOf k c (j + 1)) (fun _ => y) = 0 := by
        have : IsEmpty (Fin (j + 1) → Fin 0) := ⟨fun w => Fin.elim0 (w 0)⟩
        simp [contr]
      simp only [hz, Finset.sum_const_zero, zero_add]
      rw [Fintype.sum_unique]
      change contr (tensOf k c 0) (fun _ => y) = c default * BstLean.Part36.monoVal y 0
      simp [contr, zero_tensor59x, BstLean.Part36.monoVal]
    · let : NeZero n := ⟨hn⟩
      let : Inhabited (Fin n) := ⟨0⟩
      rw [BstLean.Part53.CostAux.fvA_orbit_mono _ (symm59x k c)]
      unfold polyEval
      apply Finset.sum_congr rfl
      intro p _
      have hj : p.1.val ≤ k := by omega
      have hm := mset_wordOf p.1.val p.2.val p.2.property
      have ho := orb_count59x (wordOf p.1.val p.2.val)
      have hq : (⟨mset (wordOf p.1.val p.2.val), by simp [mset]⟩ : Sym (Fin n) p.1.val) = p.2 := Subtype.ext hm
      rw [hq] at ho
      simp only [tensOf, dite_eq_left hj, mono_word59x, phiM]
      rw [← ho]
      have hne := orb_ne59x (wordOf p.1.val p.2.val)
      field_simp
  · intro htop
    obtain ⟨p, hp, hc⟩ := htop
    have hcard : p.2.val.card = k := by simp [hp]
    have hw : ∃ w : Fin k → Fin n, mset w = p.2.val := by
      by_cases hn : n = 0
      · subst n
        have hm : p.2.val = 0 := Multiset.eq_zero_of_forall_notMem (by
          intro a; exact Fin.elim0 a)
        have hk : k = 0 := by rw [hm, Multiset.card_zero] at hcard; exact hcard.symm
        subst k
        exact ⟨Fin.elim0, by simpa only [mset, Finset.univ_eq_empty, Finset.empty_val, Multiset.map_zero] using hm.symm⟩
      · let : NeZero n := ⟨hn⟩
        let : Inhabited (Fin n) := ⟨0⟩
        exact ⟨wordOf k p.2.val, mset_wordOf _ _ hcard⟩
    obtain ⟨w, hw⟩ := hw
    have hm : monoOf k (le_refl k) w = p := by
      apply Sigma.ext
      · exact hp.symm
      · simp only [monoOf]
        cases p with
        | mk i q =>
          dsimp at hp hw ⊢
          subst i
          apply heq_of_eq
          apply Subtype.ext
          exact hw
    have ht : tensOf k c k w ≠ 0 := by
      simpa [tensOf, hm] using div_ne_zero hc (orb_ne59x w)
    unfold frob
    exact (sq_pos_of_ne_zero ht).trans_le
      (Finset.single_le_sum (fun v _ => sq_nonneg (tensOf k c k v)) (Finset.mem_univ w))

end BstLean.Part59
