import BstLean.Part78Defs

/-!
# Part 78 (sharp), combinatorics: sums over the non-constant monomials of degree `≤ 2`

`Σ_{q : JJ n} F q = Σ_i F(x_i) + Σ_{z : Sym2} F(x_z)`, and a sum over `Sym2 (Fin n)` in terms of the
sum over ordered pairs. Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part78

open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

/-- The linear monomial `x_i`. -/
def linQ (i : Fin n) : Mono n 2 := ⟨1, Sym.oneEquiv i⟩

/-- The quadratic monomial `x_z`, `z` an unordered pair. -/
def quadQ (z : Sym2 (Fin n)) : Mono n 2 := ⟨2, Sym2.equivSym (Fin n) z⟩

lemma linQ_ne (i : Fin n) : linQ i ≠ default := by
  intro h
  have := congrArg (fun q : Mono n 2 => (q.1 : ℕ)) h
  simp [linQ, default] at this

lemma quadQ_ne (z : Sym2 (Fin n)) : quadQ z ≠ default := by
  intro h
  have := congrArg (fun q : Mono n 2 => (q.1 : ℕ)) h
  simp [quadQ, default] at this

lemma phiM_linQ (x : Fin n → ℝ) (i : Fin n) : phiM x (linQ i) = x i := by
  have h : ((linQ i).2 : Multiset (Fin n)) = {i} := rfl
  simp [phiM, monoVal, h]

lemma phiM_quadQ (x : Fin n → ℝ) (i j : Fin n) : phiM x (quadQ s(i, j)) = x i * x j := by
  have h : ((quadQ s(i, j)).2 : Multiset (Fin n)) = {i, j} := rfl
  simp [phiM, monoVal, h]

lemma phiM_default (x : Fin n → ℝ) : phiM x (default : Mono n 2) = 1 := by
  have h : ((default : Mono n 2).2 : Multiset (Fin n)) = 0 := rfl
  simp [phiM, monoVal, h]

private lemma sum_sym0 (G : Sym (Fin n) 0 → ℝ) : ∑ s, G s = G Sym.nil := by
  rw [Fintype.sum_unique]; congr 1

/-- A sum over the monomials of degree `≤ 2`. -/
lemma sum_mono (F : Mono n 2 → ℝ) :
    ∑ q, F q = F default + ∑ i, F (linQ i) + ∑ z, F (quadQ z) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_three]
  congr 1
  · congr 1
    · exact sum_sym0 (fun s => F ⟨0, s⟩)
    · exact (Fintype.sum_equiv Sym.oneEquiv _ _ (fun i => rfl)).symm
  · exact (Fintype.sum_equiv (Sym2.equivSym (Fin n)) _ _ (fun i => rfl)).symm

/-- A sum over the non-constant monomials. -/
lemma sum_JJ (F : Mono n 2 → ℝ) :
    ∑ q : JJ n, F q.1 = ∑ i, F (linQ i) + ∑ z, F (quadQ z) := by
  classical
  have h := sum_mono F
  have h2 : ∑ q : JJ n, F q.1 = ∑ q ∈ Finset.univ.filter (fun q : Mono n 2 => q ≠ default), F q := by
    rw [Finset.sum_subtype (p := fun q : Mono n 2 => q ≠ default)]
    simp
  rw [h2, Finset.filter_ne' , Finset.sum_erase_eq_sub (Finset.mem_univ _), h]
  ring

/-- A sum over unordered pairs in terms of the sum over ordered pairs. -/
lemma sum_sym2 (f : Sym2 (Fin n) → ℝ) :
    ∑ z, f z = (∑ i, ∑ j, f s(i, j) + ∑ i, f s(i, i)) / 2 := by
  classical
  have k1 : ∀ z : Sym2 (Fin n),
      ((Finset.univ.filter (fun p : Fin n × Fin n => s(p.1, p.2) = z)).card : ℝ) =
        2 - (if z.IsDiag then 1 else 0) := by
    intro z
    induction z with
    | _ a b =>
      have : Finset.univ.filter (fun p : Fin n × Fin n => s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨c, d⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
      rw [this]
      by_cases hab : a = b
      · subst hab; simp; norm_num
      · have : (a, b) ≠ (b, a) := by
          intro h; exact hab (Prod.ext_iff.mp h).1
        rw [Finset.card_pair this]
        simp [hab]
  have k2 : ∀ z : Sym2 (Fin n),
      ((Finset.univ.filter (fun i : Fin n => s(i, i) = z)).card : ℝ) =
        (if z.IsDiag then 1 else 0) := by
    intro z
    induction z with
    | _ a b =>
      by_cases hab : a = b
      · subst hab
        have : Finset.univ.filter (fun i : Fin n => s(i, i) = s(a, a)) = {a} := by
          ext c; simp [Sym2.eq_iff]
        rw [this]; simp
      · have : Finset.univ.filter (fun i : Fin n => s(i, i) = s(a, b)) = ∅ := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq_iff,
            Finset.notMem_empty, iff_false]
          rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hab rfl
        rw [this]; simp [hab]
  have e1 : ∑ i, ∑ j, f s(i, j) = ∑ z, (2 - (if z.IsDiag then 1 else 0)) * f z := by
    rw [← Fintype.sum_prod_type' (f := fun i j => f s(i, j)),
      ← Finset.sum_fiberwise Finset.univ (fun p : Fin n × Fin n => s(p.1, p.2))]
    apply Finset.sum_congr rfl; intro z _
    rw [← k1 z, Finset.sum_congr rfl (g := fun _ => f z)
      (fun p hp => by rw [← (Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
  have e2 : ∑ i, f s(i, i) = ∑ z, (if z.IsDiag then 1 else 0) * f z := by
    rw [← Finset.sum_fiberwise Finset.univ (fun i : Fin n => s(i, i))]
    apply Finset.sum_congr rfl; intro z _
    rw [← k2 z, Finset.sum_congr rfl (g := fun _ => f z)
      (fun p hp => by rw [← (Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
  rw [e1, e2, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl; intro z _
  ring

end BstLean.Part78
