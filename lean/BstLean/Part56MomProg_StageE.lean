import BstLean.Part56MomProg_StageA

/-! Stage E: the tilted moment table `T(μ) = Σ_{i ≤ K} t^i/i! m(i, μ)`. -/

namespace BstLean.Part56.MomProg

open BstLean.Cost BstLean.Part56

variable {n : ℕ}

lemma gmN_le (c : ℕ) : gmN c ≤ c ^ c := by
  unfold gmN
  split_ifs
  · calc (c - 1).doubleFactorial ≤ (c - 1).factorial := Nat.doubleFactorial_le_factorial _
      _ ≤ c.factorial := Nat.factorial_le (Nat.sub_le _ _)
      _ ≤ c ^ c := Nat.factorial_le_pow c
  · exact Nat.zero_le _

lemma sum_eq_fdeg (μ : Fin n →₀ ℕ) : ∑ l, μ l = fdeg μ := by
  unfold fdeg
  rw [Finsupp.sum_fintype]
  intro i; rfl

lemma apply_le_fdeg (μ : Fin n →₀ ℕ) (l : Fin n) : μ l ≤ fdeg μ := by
  rw [← sum_eq_fdeg]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

lemma momNum_le {D : ℕ} (μ : Fin n →₀ ℕ) (hμ : fdeg μ ≤ D) : momNum μ ≤ D ^ D := by
  unfold momNum
  calc ∏ l, gmN (μ l) ≤ ∏ l, D ^ (μ l) := by
        apply Finset.prod_le_prod'
        intro l _
        calc gmN (μ l) ≤ μ l ^ μ l := gmN_le _
          _ ≤ D ^ μ l := Nat.pow_le_pow_left ((apply_le_fdeg μ l).trans hμ) _
    _ = D ^ fdeg μ := by rw [Finset.prod_pow_eq_pow_sum, sum_eq_fdeg]
    _ ≤ D ^ D := by
        rcases Nat.eq_zero_or_pos D with h | h
        · subst h; simp at hμ; simp [hμ]
        · exact Nat.pow_le_pow_right h hμ

lemma momDen_le (hn : 1 ≤ n) {D : ℕ} (μ : Fin n →₀ ℕ) (hμ : fdeg μ ≤ D) :
    momDen n μ ≤ (n + D) ^ D := by
  unfold momDen
  calc ∏ j ∈ Finset.range (fdeg μ / 2), (n + 2 * j) ≤ ∏ _j ∈ Finset.range (fdeg μ / 2), (n + D) := by
        apply Finset.prod_le_prod'
        intro j hj
        rw [Finset.mem_range] at hj
        omega
    _ = (n + D) ^ (fdeg μ / 2) := by simp
    _ ≤ (n + D) ^ D := Nat.pow_le_pow_right (by omega) (by omega)

/-- The table entries for one exponent. -/
noncomputable def eTab (a : Fin n) (ν : Fin n →₀ ℕ) (w : Unit → ℝ) (i : ℕ) (_ : Unit) : ℝ :=
  (w ()) ^ i / (i.factorial : ℝ) * momA a i ν

/-- The step cost. -/
def stepC (n : ℕ) (ν : Fin n →₀ ℕ) (a : Fin n) (k : ℕ) : ℕ :=
  (2 * k + ν a + 1) + (k + 1) + (n + 2 * (k + fdeg ν / 2)) + 4

lemma hp_Ttab1 (hn : 1 ≤ n) (a : Fin n) (K : ℕ) (ν : Fin n →₀ ℕ) :
    HasProg (fun (w : Unit → ℝ) (_ : Unit) => Ttab a K (w ()) ν)
      (momNum ν + momDen n ν + 1 + ∑ k ∈ Finset.range K, stepC n ν a k + K) := by
  classical
  have h0 : HasProg (fun w => eTab a ν w 0) (momNum ν + momDen n ν + 1) := by
    have h := hp_op2 (ι := Unit) .div (hp_nat (momNum ν)) (hp_nat (momDen n ν))
    refine hp_congr h ?_
    intro w u
    simp [eTab, Op.eval, momA_zero hn]
  let g : ℕ → ((Unit ⊕ (ℕ × Unit)) → ℝ) → Unit → ℝ := fun k s _ =>
    s (Sum.inr (k, ())) * s (Sum.inl ()) * ((2 * k + ν a + 1 : ℕ) : ℝ) /
      (((k + 1 : ℕ) : ℝ) * ((n + 2 * (k + fdeg ν / 2) : ℕ) : ℝ))
  have hs : ∀ k, k < K → HasProg (g k) (stepC n ν a k) := by
    intro k _
    have h := hp_op2 .div
      (hp_op2 .mul (hp_op .mul (Arg.inp (Sum.inr (k, ()))) (Arg.inp (Sum.inl ())) rfl rfl)
        (hp_nat (2 * k + ν a + 1)))
      (hp_op2 .mul (hp_nat (k + 1)) (hp_nat (n + 2 * (k + fdeg ν / 2))))
    refine hp_mono (hp_congr h ?_) (by unfold stepC; omega)
    intro s u
    simp only [Op.eval, Arg.eval, g]
  have he : ∀ k, k < K → ∀ w a', g k (Sum.elim w (tab (eTab a ν) k w)) a' =
      eTab a ν w (k + 1) a' := by
    intro k _ w a'
    simp only [g, Sum.elim_inr, Sum.elim_inl, tab, le_refl, if_true, eTab]
    rw [momA_succ hn, Nat.factorial_succ]
    have hC : (0 : ℝ) < ((n + 2 * (k + fdeg ν / 2) : ℕ) : ℝ) := by
      have : 1 ≤ n + 2 * (k + fdeg ν / 2) := by omega
      exact_mod_cast this
    have hF : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    push_cast
    field_simp
    ring
  have ht := hp_table (eTab a ν) g _ _ h0 K hs he
  have hsum := hp_seq ht (hp_sum (ι := ℕ × Unit) (κ := Fin (K + 1))
    (fun i => Arg.inp (i.val, ())) (fun _ => rfl))
  refine hp_mono (hp_congr hsum ?_) (by simp)
  intro w u
  simp only [Arg.eval]
  rw [Fin.sum_univ_eq_sum_range (fun i => tab (eTab a ν) K w (i, ())) (K + 1)]
  unfold Ttab
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [tab, show i ≤ K by omega, if_true, eTab]

lemma hp_stageE (hn : 1 ≤ n) (a : Fin n) (d k K : ℕ) :
    HasProg (fun (w : Unit → ℝ) => TF (2 * d * k) a K (w ()))
      (costE n d k K (Fintype.card (Idx n (2 * d * k)))) := by
  classical
  set D := 2 * d * k with hD
  have h : ∀ μ : Idx n D, HasProg (fun (w : Unit → ℝ) (_ : Unit) => TF D a K (w ()) μ)
      (D ^ D + (n + D) ^ D + 2 + K * (n + 6 * K + 8 * d * k + 10)) := by
    intro μ
    refine hp_mono (hp_Ttab1 hn a K μ.1) ?_
    have h1 := momNum_le μ.1 μ.2
    have h2 := momDen_le hn μ.1 μ.2
    have h3 : ∑ k ∈ Finset.range K, stepC n μ.1 a k ≤ K * (n + 5 * K + 2 * D + 5) := by
      calc ∑ k ∈ Finset.range K, stepC n μ.1 a k
          ≤ ∑ _k ∈ Finset.range K, (n + 5 * K + 2 * D + 5) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Finset.mem_range] at hj
            have ha := apply_le_fdeg μ.1 a
            have hf := μ.2
            unfold stepC
            omega
        _ = K * (n + 5 * K + 2 * D + 5) := by simp
    have h4 : K * (n + 5 * K + 2 * D + 5) + K ≤ K * (n + 6 * K + 8 * d * k + 10) := by
      have : n + 5 * K + 2 * D + 5 + 1 ≤ n + 6 * K + 8 * d * k + 10 := by
        rw [hD]; nlinarith
      nlinarith
    omega
  have hp := hp_par h
  unfold costE
  exact hp_congr hp (fun w μ => rfl)

end BstLean.Part56.MomProg
