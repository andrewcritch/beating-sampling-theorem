import BstLean.Part41Defs

/-!
# Part 41, wave 1: elementary tensor facts

Paper: the Setting (`‖tr^l T‖² ≤ n^l ‖T‖²` by Cauchy–Schwarz) and the symmetry of traces and of the
moment tensors. Specification: `delegations/answers/p41-spec-opus.md`. Do not use `native_decide`.

Routes: `frob_trL_le` is Cauchy–Schwarz over `c : Fin l → ι` (`n^l` terms) and injectivity of
`(c, w) ↦ glue j l c w` when `2l ≤ j`. `trL_symm`: a permutation of the free slots of `glue` is a
permutation of `Fin j`. `HQ_symm`, `HQ_nonneg`: `HQ l (w ∘ σ)` has the same exponent vector.
-/

namespace BstLean.Part41

variable {n d : ℕ}

/-- `‖tr^l A‖² ≤ |ι|^l ‖A‖²` (`2l ≤ j`). -/
theorem frob_trL_le {ι : Type*} [Fintype ι] {j : ℕ} (l : ℕ) (hl : 2 * l ≤ j) (A : (Fin j → ι) → ℝ) :
    frob (trL l A) ≤ (Fintype.card ι : ℝ) ^ l * frob A := by
  classical
  let G : (Fin l → ι) × (Fin (j - 2 * l) → ι) → (Fin j → ι) :=
    fun p => glue j l p.1 p.2
  have hinj : Function.Injective G := by
    intro p q h
    apply Prod.ext
    · funext t
      have h' := congrFun h ⟨2 * t.val, by omega⟩
      simpa [G, glue, show 2 * t.val < 2 * l by omega] using h'
    · funext t
      have h' := congrFun h ⟨2 * l + t.val, by omega⟩
      simpa [G, glue, show ¬2 * l + t.val < 2 * l by omega] using h'
  have hsum : (∑ w, ∑ c, A (glue j l c w) ^ 2) ≤ frob A := by
    rw [Finset.sum_comm]
    change (∑ c, ∑ w, A (G (c, w)) ^ 2) ≤ frob A
    rw [← Fintype.sum_prod_type (fun p => A (G p) ^ 2)]
    calc
      _ = ∑ v ∈ Finset.univ.image G, A v ^ 2 := by
        rw [Finset.sum_image (fun p _ q _ h => hinj h)]
      _ ≤ frob A := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  unfold frob trL
  calc
    _ ≤ ∑ w, (Fintype.card ι : ℝ) ^ l * ∑ c, A (glue j l c w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin l → ι => (1 : ℝ)) (fun c => A (glue j l c w))
      simpa using h
    _ = (Fintype.card ι : ℝ) ^ l * ∑ w, ∑ c, A (glue j l c w) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The partial trace of a symmetric tensor is symmetric. -/
theorem trL_symm {ι R : Type*} [Fintype ι] [AddCommMonoid R] {j : ℕ} (l : ℕ) (hl : 2 * l ≤ j)
    (A : (Fin j → ι) → R) (hA : IsSymmT A) : IsSymmT (trL l A) := by
  classical
  intro σ w
  let e : Fin (j - 2 * l) ≃ {t : Fin j // 2 * l ≤ t.val} :=
    { toFun := fun t => ⟨⟨2 * l + t.val, by omega⟩, by simp⟩
      invFun := fun t => ⟨t.val.val - 2 * l, by have := t.val.isLt; have := t.property; omega⟩
      left_inv := by intro t; apply Fin.ext; simp
      right_inv := by intro t; apply Subtype.ext; apply Fin.ext; simp; have := t.property; omega }
  let τ := σ.extendDomain e
  unfold trL
  apply Finset.sum_congr rfl
  intro c hc
  have heq : glue j l c (w ∘ σ) = glue j l c w ∘ τ := by
    funext t
    by_cases ht : t.val < 2 * l
    · have hτ : τ t = t := σ.extendDomain_apply_not_subtype e (by omega)
      simp [hτ, glue, ht]
    · let u : Fin (j - 2 * l) := ⟨t.val - 2 * l, by have := t.isLt; omega⟩
      have hu : (e u).val = t := by apply Fin.ext; dsimp [e, u]; omega
      have hτ : τ t = (e (σ u)).val := by
        rw [← hu]
        exact σ.extendDomain_apply_image e u
      simp [glue, ht, hτ, e, u]
  rw [heq]
  exact hA τ (glue j l c w)

/-- `H_{j,l}` is a symmetric tensor. -/
theorem HQ_symm {s : ℕ} (l : ℕ) : IsSymmT (fun w : Fin s → Mono n d => HQ l w) := by
  classical
  intro σ w
  unfold HQ
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  funext a
  congr 1
  exact Equiv.sum_comp σ (fun t => expo (w t) a)

private lemma rhoQ_pos (hn : 1 ≤ n) (m : ℕ) : 0 < rhoQ n m := by
  unfold rhoQ
  apply Finset.prod_pos
  intro t ht
  have : (0 : ℚ) < n := by exact_mod_cast hn
  positivity

private lemma num_le_rho (hn : 1 ≤ n) (a : Fin n → ℕ) :
    (∏ i, ((2 * a i - 1).doubleFactorial : ℚ)) ≤ rhoQ n (∑ i, a i) := by
  classical
  generalize hm : (∑ i, a i) = m
  induction m using Nat.strong_induction_on generalizing a with
  | h m ih =>
    by_cases hz : m = 0
    · have ha : ∀ i, a i = 0 := by
        intro i
        have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
        omega
      simp [ha, hz, rhoQ, Nat.doubleFactorial]
    · have hex : ∃ i, a i ≠ 0 := by
        by_contra h
        push Not at h
        simp [h] at hm
        omega
      obtain ⟨i, hi⟩ := hex
      let b := Function.update a i (a i - 1)
      have hb : (∑ j, b j) + 1 = m := by
        have h1 := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) a (Finset.mem_univ i)
        have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) b (Finset.mem_univ i)
        have he : ∑ j ∈ Finset.univ.erase i, b j = ∑ j ∈ Finset.univ.erase i, a j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [b, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have hbi : b i = a i - 1 := by simp [b]
        rw [he, hbi] at h2
        omega
      have hind := ih (∑ j, b j) (by omega) b rfl
      have hp : (∏ j, ((2 * a j - 1).doubleFactorial : ℚ)) =
          (2 * (a i : ℚ) - 1) * ∏ j, ((2 * b j - 1).doubleFactorial : ℚ) := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
          ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        have he : (∏ j ∈ Finset.univ.erase i, ((2 * b j - 1).doubleFactorial : ℚ)) =
            ∏ j ∈ Finset.univ.erase i, ((2 * a j - 1).doubleFactorial : ℚ) := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [b, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        rw [he]
        have hd : (2 * a i - 1).doubleFactorial =
            (2 * a i - 1) * (2 * (a i - 1) - 1).doubleFactorial := by
          obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero hi
          rw [hv]
          simpa [Nat.mul_add, Nat.add_sub_assoc] using Nat.doubleFactorial_add_one (2 * v)
        rw [hd]
        simp only [Nat.cast_mul]
        have hc : ((2 * a i - 1 : ℕ) : ℚ) = 2 * (a i : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        rw [hc]
        simp [b]
        ring
      have hr : rhoQ n m = rhoQ n (∑ j, b j) * ((n : ℚ) + 2 * (∑ j, b j : ℕ)) := by
        rw [← hb]
        simp [rhoQ, Finset.prod_range_succ]
      have hfac : 0 ≤ 2 * (a i : ℚ) - 1 := by
        have : (1 : ℚ) ≤ a i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
        linarith
      have hle : 2 * (a i : ℚ) - 1 ≤ (n : ℚ) + 2 * (∑ j, b j : ℕ) := by
        have hs := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
        have hs' : (a i : ℚ) ≤ m := by exact_mod_cast (hm ▸ hs)
        have hb' : ((∑ j, b j : ℕ) : ℚ) + 1 = m := by exact_mod_cast hb
        have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
        linarith
      rw [hp, hr]
      calc
        _ ≤ (2 * (a i : ℚ) - 1) * rhoQ n (∑ j, b j) := mul_le_mul_of_nonneg_left hind hfac
        _ ≤ _ := by
          rw [mul_comm (rhoQ n _)]
          exact mul_le_mul_of_nonneg_right hle (rhoQ_pos hn _).le

/-- Every entry of `H_{j,l}` is `≥ 0` and `≤ N^l` (each sphere moment is in `[0, 1]`). -/
theorem HQ_bounds {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) :
    0 ≤ HQ l w ∧ HQ l w ≤ (Fintype.card (Mono n d) : ℚ) ^ l := by
  classical
  have hmoment (e : Fin n → ℕ) : 0 ≤ sphMomQ e ∧ sphMomQ e ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      simp [sphMomQ, rhoQ]
    have hn' : 1 ≤ n := by omega
    unfold sphMomQ
    split_ifs with he
    · let a : Fin n → ℕ := fun i => e i / 2
      have ha : ∀ i, e i = 2 * a i := by
        intro i
        obtain ⟨v, hv⟩ := he i
        simp [a, hv, ← two_mul]
      have hs : (∑ i, e i) / 2 = ∑ i, a i := by
        simp_rw [ha]
        rw [← Finset.mul_sum]
        omega
      rw [hs]
      constructor
      · exact div_nonneg (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
          (rhoQ_pos hn' _).le
      · apply (div_le_one (rhoQ_pos hn' _)).mpr
        simpa only [ha] using num_le_rho hn' a
    · norm_num
  unfold HQ
  constructor
  · exact Finset.sum_nonneg (fun c _ => (hmoment _).1)
  · calc
      _ ≤ ∑ _c : Fin l → Mono n d, (1 : ℚ) :=
        Finset.sum_le_sum (fun c _ => (hmoment _).2)
      _ = _ := by simp

/-- `𝒩(f) > 0` when `T_k ≠ 0` (the level `(k, 0)` term is `k! k ‖T_k‖²/D^k`; the others are `≥ 0`). -/
theorem Nn_pos (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (T : Tens n) (hTk : 0 < frob (T k)) : 0 < Nn n d k T := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < BstLean.Part36.DD n d := by
    let : Nonempty (BstLean.Part36.CoefIdxD n d) :=
      ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
    unfold BstLean.Part36.DD
    exact_mod_cast Fintype.card_pos
  have hf (j l : ℕ) : 0 ≤ frob (trL l (T j)) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ha (j l : ℕ) : 0 ≤ aSq n d T j l := by
    unfold aSq
    exact mul_nonneg (div_nonneg (sq_nonneg _) (le_of_lt (pow_pos hD _))) (hf j l)
  have ht : trL 0 (T k) = T k := by
    funext w
    simp only [trL, Finset.univ_unique, Finset.sum_singleton]
    congr 1
  have hc : cQ k 0 = 1 := by simp [cQ, Nat.factorial_ne_zero]
  have hapos : 0 < aSq n d T k 0 := by
    unfold aSq
    rw [ht, hc]
    norm_num
    exact mul_pos (inv_pos.mpr (pow_pos hD k)) hTk
  unfold Nn
  apply Finset.sum_pos'
  · intro jl hjl
    have := ha jl.1 jl.2
    positivity
  · refine ⟨(k, 0), ?_, ?_⟩
    · simp [levels, hk]; omega
    · simp only [mul_zero, Nat.sub_zero, pow_zero, Nat.sub_self, div_one]
      have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      positivity

end BstLean.Part41

