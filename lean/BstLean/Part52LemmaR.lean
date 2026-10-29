import BstLean.Part43Defs
import BstLean.Part52Reads

/-!
# Part 52, wave 1: Lemma R (a coefficient that is not read)

Role: `delegations/statements/p52-spec.md`. Source: `delegations/answers/omDL-opus-prover.md` §4.2.

The program class is that of Theorem G (`part48_general`), with `f` an input: one branch program
`pg : Prog (In43 n d k) Unit` and one vector `c` of moment values (computed from `θ`, not from `f`),
used for **every** `f`. `failSet` is Part 48's failure event. `Guar μ k ε δ pg c` says that the failure
probability over `Z` is `≤ δ` for every `f = (f₀, T)` with `T` symmetric and `T_k ≠ 0`.

`Tal k α` is the word tensor of a multiset `α` of size `k`: `T_k[w] = 1` if the word `w` has the
multiset `α`, and `0` otherwise; `T_j = 0` for `j ≠ k`. So `f = Tal k α` is `c_α · y^α` with
`c_α = #{w : mset w = α}`.

* `lemmaR`: if `pg` reads no input `T_k[w]` with `mset w = α`, then
  `Pr_Z{Z ≠ 0, ε² Var_μ(f_α) < B_μ(f_α)²} ≤ 2δ` at `f_α = Tal k α` and `M = Z/‖Z‖`.
  The proof compares `f_α` with `−f_α`: the program returns the same value at both, and
  `B(−f_α) = −B(f_α)`, `Var(−f_α) = Var(f_α)`. No limit in `t` is needed.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part52

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD mapMD)
open BstLean.Part41 (Tens TSymm frob mset contr fval varU IsSymmT)
open BstLean.Part43 (BofQ varFQ inp43 In43 KeyF)

variable {n d : ℕ}

/-- Part 48's failure event for `f = (f₀, T)`, program `pg` and moment values `c`. -/
def failSet (μ : Measure (Fin n → ℝ)) (k : ℕ) (ε : ℝ) (pg : Prog (In43 n d k) Unit)
    (c : KeyF n d k → ℝ) (f0 : ℝ) (T : Tens n) : Set (CoefIdxD n d → ℝ) :=
  {Z | Z ≠ 0 ∧ ε ^ 2 * varFQ μ k f0 T (unitOfD Z) <
    (BofQ μ k f0 T (unitOfD Z) - pg.eval (inp43 f0 T (unitOfD Z) c) ()) ^ 2}

/-- The guarantee of the class: failure probability `≤ δ` for **every** admissible `f`. -/
def Guar (μ : Measure (Fin n → ℝ)) (k : ℕ) (ε δ : ℝ) (pg : Prog (In43 n d k) Unit)
    (c : KeyF n d k → ℝ) : Prop :=
  ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
    stdGauss (CoefIdxD n d) (failSet μ k ε pg c f0 T) ≤ ENNReal.ofReal δ

/-- The input index of the entry `T_k[w]`. -/
def tIdx (k : ℕ) (w : Fin k → Fin n) : In43 n d k :=
  Sum.inl (Sum.inr (Sum.inr ⟨⟨k, Nat.lt_succ_self k⟩, w⟩))

/-- The word tensor of `α`: `T_k[w] = [mset w = α]`, `T_j = 0` for `j ≠ k`. -/
noncomputable def Tal (k : ℕ) (α : Multiset (Fin n)) : Tens n := fun j w => by
  classical exact if j = k ∧ mset w = α then 1 else 0

/-- The negated tensor. -/
def negT (T : Tens n) : Tens n := fun j w => -T j w

theorem mset_comp_perm {j : ℕ} (w : Fin j → Fin n) (σ : Equiv.Perm (Fin j)) :
    mset (w ∘ σ) = mset w := by
  unfold mset
  rw [← Multiset.map_map]
  congr 1
  have := congrArg Finset.val (Finset.univ_map_equiv_to_embedding σ)
  rwa [Finset.map_val] at this

theorem Tal_symm (k : ℕ) (α : Multiset (Fin n)) : TSymm k (Tal k α) := by
  intro j _ _ σ w
  simp only [Tal, mset_comp_perm]

theorem negT_symm (k : ℕ) (T : Tens n) (hT : TSymm k T) : TSymm k (negT T) := by
  intro j h1 h2 σ w
  simp only [negT, hT j h1 h2 σ w]

/-- A word with multiset `α`, when `|α| = k`. -/
noncomputable def wordAl (k : ℕ) (α : Multiset (Fin n)) (hα : Multiset.card α = k) : Fin k → Fin n :=
  fun t => α.toList.get ⟨t.1, by rw [Multiset.length_toList, hα]; exact t.2⟩

theorem mset_wordAl (k : ℕ) (α : Multiset (Fin n)) (hα : Multiset.card α = k) :
    mset (wordAl k α hα) = α := by
  unfold mset
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList α]
  congr 1
  apply List.ext_get
  · simp [hα]
  · intro i h1 h2
    simp [wordAl]

theorem frob_Tal_pos (k : ℕ) (α : Multiset (Fin n)) (hα : Multiset.card α = k) :
    0 < frob (Tal k α k) := by
  classical
  unfold frob
  have h0 : Tal k α k (wordAl k α hα) ^ 2 = 1 := by
    simp [Tal, mset_wordAl k α hα]
  calc (0 : ℝ) < Tal k α k (wordAl k α hα) ^ 2 := by rw [h0]; norm_num
    _ ≤ ∑ w, Tal k α k w ^ 2 :=
      Finset.single_le_sum (f := fun w => Tal k α k w ^ 2) (fun w _ => sq_nonneg _) (Finset.mem_univ _)

theorem frob_negT (k : ℕ) (T : Tens n) : frob (negT T k) = frob (T k) := by
  simp [frob, negT]

theorem fval_negT (k : ℕ) (T : Tens n) (y : Fin n → ℝ) : fval k 0 (negT T) y = -fval k 0 T y := by
  simp [fval, contr, negT, Finset.sum_neg_distrib]

theorem BofQ_negT (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    BofQ μ k 0 (negT T) M = -BofQ μ k 0 T M := by
  simp [BofQ, fval_negT, integral_neg]

theorem varFQ_negT (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    varFQ μ k 0 (negT T) M = varFQ μ k 0 T M := by
  simp only [varFQ, varU, fval_negT, integral_neg]
  congr 1
  funext x
  ring

/-- The inputs at `Tal k α` and at `negT (Tal k α)` differ only at the entries `T_k[w]`, `mset w = α`. -/
theorem inp_agree (k : ℕ) (α : Multiset (Fin n)) (M : CoefIdxD n d → ℝ) (c : KeyF n d k → ℝ)
    (i : In43 n d k) (hi : ∀ w : Fin k → Fin n, mset w = α → i ≠ tIdx k w) :
    inp43 0 (Tal k α) M c i = inp43 0 (negT (Tal k α)) M c i := by
  classical
  rcases i with (a | u | ⟨⟨jv, hj⟩, w⟩) | κ
  · rfl
  · rfl
  · simp only [inp43, Sum.elim_inl, Sum.elim_inr, negT]
    by_cases hjk : jv = k
    · subst hjk
      by_cases hw : mset w = α
      · exact absurd rfl (hi w hw)
      · simp [Tal, hw]
    · simp [Tal, hjk]
  · rfl

/-- **Lemma R.** If `pg` reads no entry `T_k[w]` with `mset w = α` (`|α| = k`), then the guarantee
forces `Pr_Z{Z ≠ 0, ε² Var_μ(f_α) < B_μ(f_α)²} ≤ 2δ`. -/
theorem lemmaR (μ : Measure (Fin n → ℝ)) (k : ℕ) (ε δ : ℝ) (pg : Prog (In43 n d k) Unit)
    (c : KeyF n d k → ℝ) (hG : Guar μ k ε δ pg c) (α : Multiset (Fin n)) (hα : Multiset.card α = k)
    (hnr : ∀ w : Fin k → Fin n, mset w = α → ¬ Reads pg (tIdx k w)) :
    stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
      ε ^ 2 * varFQ μ k 0 (Tal k α) (unitOfD Z) < BofQ μ k 0 (Tal k α) (unitOfD Z) ^ 2} ≤
      ENNReal.ofReal δ + ENNReal.ofReal δ := by
  have h1 := hG 0 (Tal k α) (Tal_symm k α) (frob_Tal_pos k α hα)
  have h2 := hG 0 (negT (Tal k α)) (negT_symm k _ (Tal_symm k α))
    (by rw [frob_negT]; exact frob_Tal_pos k α hα)
  refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans (add_le_add h1 h2))
  intro Z ⟨hZ, hlt⟩
  have hg : pg.eval (inp43 0 (Tal k α) (unitOfD Z) c) () =
      pg.eval (inp43 0 (negT (Tal k α)) (unitOfD Z) c) () := by
    apply eval_congr_reads
    intro i hri
    apply inp_agree
    intro w hw hiw
    exact hnr w hw (hiw ▸ hri)
  by_contra hno
  simp only [Set.mem_union, failSet, Set.mem_ofPred_eq, not_or, not_and, not_lt] at hno
  obtain ⟨hA, hB⟩ := hno
  have hA' := hA hZ
  have hB' := hB hZ
  rw [BofQ_negT, varFQ_negT, ← hg] at hB'
  set X := BofQ μ k 0 (Tal k α) (unitOfD Z)
  set g := pg.eval (inp43 0 (Tal k α) (unitOfD Z) c) ()
  set V := ε ^ 2 * varFQ μ k 0 (Tal k α) (unitOfD Z)
  nlinarith [sq_nonneg (X - g + (-X - g)), sq_nonneg g]

end BstLean.Part52
