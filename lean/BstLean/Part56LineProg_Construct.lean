import BstLean.Part56LineProg_Basic
import BstLean.Part56Defs

namespace BstLean.Part56
open BstLean.Cost BstLean.Part41 BstLean.Part53
noncomputable section
variable {n d k : ℕ}

def phiProg56 (n d k : ℕ) : Prog (In56 n d k) (Mono n d) :=
  Prog.par (fun p => prodArgs (p.2.1.toList.map fun a => .inp (.inr (.inl a))))
    Finset.univ.toList

lemma phiProg56_eval (f0 : ℝ) (T : Tens n) (M : BstLean.Part36.CoefIdxD n d → ℝ)
    (v : Fin n → ℝ) (c : KeyRK k d → ℝ) (p : Mono n d) :
    (phiProg56 n d k).eval (inp56 f0 T M v c) p = phiM v p := by
  classical
  rw [phiProg56, eval_par_mem _ _ _ _ (by simp), prodArgs_eval]
  simp [phiM, BstLean.Part36.monoVal, List.map_map, Function.comp_def, Arg.eval, inp56]

abbrev Anchor56 (n d : ℕ) := Fin (d + 1) × Fin n

def anchorSlot56 (j : Anchor56 n d) : Prog (In56 n d k ⊕ Mono n d) Unit :=
  Prog.sumProd ((Finset.univ.filter fun p : Mono n d => p.1 = j.1).toList.map fun p =>
    (.inp (.inl (.inl (.inl ⟨p.1, (p.2, j.2)⟩))), .inp (.inr p)))

def anchorProg56 (n d k : ℕ) : Prog (In56 n d k ⊕ Mono n d) (Anchor56 n d) :=
  Prog.par anchorSlot56 Finset.univ.toList

lemma anchorSlot56_eval (f0 : ℝ) (T : Tens n)
    (M : BstLean.Part36.CoefIdxD n d → ℝ) (v : Fin n → ℝ) (c : KeyRK k d → ℝ)
    (j : Anchor56 n d) :
    (anchorSlot56 j).eval
      (Sum.elim (inp56 f0 T M v c) (phiM v)) () = ancRK M v j.1 j.2 := by
  classical
  rw [anchorSlot56, eval_sumProd]
  simp only [List.map_map, Function.comp_def, Arg.eval, Sum.elim_inl, Sum.elim_inr,
    inp56, inp53]
  rw [Finset.sum_map_toList, Finset.sum_filter]
  simp only [ancRK, linZ, colM, phiB]
  apply Finset.sum_congr rfl
  intro p _
  have he : (p.1 = j.1) ↔ (p.1 : ℕ) = (j.1 : ℕ) := Fin.ext_iff
  by_cases h : p.1 = j.1
  · simp [h, he.mp h]
  · have hv : (p.1 : ℕ) ≠ (j.1 : ℕ) := fun hv => h (he.mpr hv)
    simp [h, hv]

lemma anchorProg56_eval (f0 : ℝ) (T : Tens n)
    (M : BstLean.Part36.CoefIdxD n d → ℝ) (v : Fin n → ℝ) (c : KeyRK k d → ℝ)
    (j : Anchor56 n d) :
    (anchorProg56 n d k).eval
      (Sum.elim (inp56 f0 T M v c) (phiM v)) j = ancRK M v j.1 j.2 := by
  classical
  rw [anchorProg56, eval_par_mem _ _ _ _ (by simp), anchorSlot56_eval]

abbrev Online56 (n d k : ℕ) := (In56 n d k ⊕ Mono n d) ⊕ Anchor56 n d

def tensorArg56 (i : Fin (k + 1)) (w : Fin i → Fin n) : Arg (Online56 n d k) :=
  if h : (i : ℕ) = 0 then .inp (.inl (.inl (.inl (.inr (.inl ())))))
  else .inp (.inl (.inl (.inl (.inr (.inr ⟨i, w⟩)))))

def keyTerm56 (κ : KeyRK k d)
    (wc : (Fin ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)) → Fin n) ×
      (Fin (κ.1.2 : ℕ) → Fin n)) : Prog (Online56 n d k) Unit :=
  prodArgs (tensorArg56 κ.1.1 (glue κ.1.1 κ.1.2 wc.2 wc.1) ::
    (List.finRange ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ))).map fun r =>
      .inp (.inr (κ.2 r, wc.1 r)))

def keyProg56 (κ : KeyRK k d) : Prog (Online56 n d k) Unit :=
  if 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) then
    (sumProgs (keyTerm56 κ)).bind
      (Prog.op1 .mul (.inp (.inl (.inl (.inl (.inr (.inr κ)))))) (.inp (.inr ())))
  else Prog.ofArgs fun _ => .cst 0

def lineProg56 (n d k : ℕ) : Prog (In56 n d k) Unit :=
  (phiProg56 n d k).bind ((anchorProg56 n d k).bind (sumProgs keyProg56))

lemma keyProg56_eval (f0 : ℝ) (T : Tens n)
    (M : BstLean.Part36.CoefIdxD n d → ℝ) (v : Fin n → ℝ) (c : KeyRK k d → ℝ)
    (κ : KeyRK k d) :
    (keyProg56 κ).eval
      (Sum.elim (Sum.elim (inp56 f0 T M v c) (phiM v))
        (fun j : Anchor56 n d => ancRK M v j.1 j.2)) () =
      if 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) then
        c κ * contr (trL (κ.1.2 : ℕ) (TF k f0 T κ.1.1))
          (fun r => ancRK M v (κ.2 r)) else 0 := by
  classical
  unfold keyProg56
  split_ifs with h
  · rw [eval_bind, eval_op1]
    simp only [Op.eval, Arg.eval, Sum.elim_inl, Sum.elim_inr, inp56]
    rw [sumProgs_eval, Fintype.sum_prod_type]
    congr 1
    simp only [contr, trL, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro b _
    rw [keyTerm56, prodArgs_eval]
    simp only [List.map_cons, List.prod_cons, List.map_map, Function.comp_def,
      List.finRange, List.map_ofFn, List.prod_ofFn, Arg.eval, Sum.elim_inr]
    congr 1
    unfold tensorArg56
    split_ifs with hz
    · simp [Arg.eval, inp56, inp53, TF, hz]
    · simp [Arg.eval, inp56, inp53, TF, hz, Nat.le_of_lt_succ κ.1.1.isLt]
  · simp [eval_ofArgs, Arg.eval]

lemma lineProg56_spec : GSpec56 (lineProg56 n d k) := by
  classical
  intro f0 T M v c _
  rw [lineProg56, eval_bind]
  have hp : (phiProg56 n d k).eval (inp56 f0 T M v c) = phiM v := by
    funext p; exact phiProg56_eval f0 T M v c p
  rw [hp, eval_bind]
  have ha : (anchorProg56 n d k).eval
      (Sum.elim (inp56 f0 T M v c) (phiM v)) =
      fun j : Anchor56 n d => ancRK M v j.1 j.2 := by
    funext j; exact anchorProg56_eval f0 T M v c j
  rw [ha, sumProgs_eval]
  simp only [gW, keyProg56_eval]

lemma lineProg56_clean : Clean (lineProg56 n d k) := by
  classical
  apply clean_bind
  · apply clean_par
    intro p
    apply prodArgs_clean
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    rfl
  · apply clean_bind
    · apply clean_par
      intro j
      apply clean_sumProd
      intro ab hab
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hab
      exact ⟨rfl, rfl⟩
    · apply sumProgs_clean
      intro κ
      unfold keyProg56
      split_ifs
      · apply clean_bind
        · apply sumProgs_clean
          intro wc
          apply prodArgs_clean
          intro a ha
          simp only [List.mem_cons, List.mem_map] at ha
          rcases ha with rfl | ⟨r, _, rfl⟩
          · unfold tensorArg56; split_ifs <;> rfl
          · rfl
        · simp [Clean, Prog.op1, argHeavy]
      · simp [Clean, Prog.ofArgs, argHeavy]

lemma phiProg56_cost : (phiProg56 n d k).cost ≤
    d * Fintype.card (Mono n d) := by
  classical
  rw [phiProg56, cost_par, Finset.sum_map_toList]
  calc
    _ ≤ ∑ _p : Mono n d, d := by
      apply Finset.sum_le_sum
      intro p _
      simp only [prodArgs_cost, List.length_map, Multiset.length_toList]
      have hp := p.2.2
      change p.2.1.card = (p.1 : ℕ) at hp
      rw [hp]
      exact Nat.le_of_lt_succ p.1.isLt
    _ = _ := by simp [Nat.mul_comm]

lemma anchorProg56_cost : (anchorProg56 n d k).cost ≤
    2 * n * Fintype.card (Mono n d) := by
  classical
  rw [anchorProg56, cost_par, Finset.sum_map_toList]
  simp only [anchorSlot56, cost_sumProd, List.length_map, Finset.length_toList]
  calc
    _ ≤ ∑ j : Anchor56 n d,
        2 * (Finset.univ.filter fun p : Mono n d => p.1 = j.1).card := by
      apply Finset.sum_le_sum; intro j _; omega
    _ = 2 * n * Fintype.card (Mono n d) := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
      rw [← Finset.mul_sum]
      have hc : (∑ j : Fin (d + 1),
          (Finset.univ.filter fun p : Mono n d => p.1 = j).card) =
          Fintype.card (Mono n d) := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        simp
      rw [← Finset.mul_sum, hc]
      ring

lemma keyProg56_cost (hn : 1 ≤ n) (κ : KeyRK k d) :
    (keyProg56 (n := n) κ).cost ≤ (k + 3) * n ^ k := by
  classical
  unfold keyProg56
  split_ifs with h
  · rw [cost_bind, cost_op1]
    have ht : ∀ wc, (keyTerm56 (n := n) κ wc).cost =
        1 + ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)) := by
      intro wc
      simp [keyTerm56, prodArgs_cost, Nat.add_comm]
    have hs := sumProgs_cost (keyTerm56 (n := n) κ)
    simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin, smul_eq_mul] at hs
    have ha : (κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ) ≤ k := by omega
    have he : (κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ) + (κ.1.2 : ℕ) ≤ k := by omega
    have hp : n ^ ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)) * n ^ (κ.1.2 : ℕ) ≤ n ^ k := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hn he
    have hpos : 1 ≤ n ^ k := Nat.one_le_pow k n hn
    nlinarith
  · simp [cost_ofArgs]

lemma keyRK_card : Fintype.card (KeyRK k d) ≤ (k + 1) ^ 2 * (d + 1) ^ k := by
  classical
  simp only [KeyRK, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
  calc
    _ ≤ ∑ _il : Fin (k + 1) × Fin (k + 1), (d + 1) ^ k := by
      apply Finset.sum_le_sum
      intro il _
      apply Nat.pow_le_pow_right (by omega)
      omega
    _ = _ := by simp [Fintype.card_prod, pow_two]

lemma onlineProg56_cost (hn : 1 ≤ n) :
    (sumProgs (keyProg56 (n := n) (d := d) (k := k))).cost ≤
      (k + 4) * (k + 1) ^ 2 * (d + 1) ^ k * n ^ k := by
  classical
  have hs := sumProgs_cost (keyProg56 (n := n) (d := d) (k := k))
  have ht : (∑ κ : KeyRK k d, (keyProg56 (n := n) κ).cost) ≤
      Fintype.card (KeyRK k d) * ((k + 3) * n ^ k) := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun κ _ => keyProg56_cost hn κ)
  have hp := Nat.one_le_pow k n hn
  calc
    _ ≤ Fintype.card (KeyRK k d) * ((k + 3) * n ^ k + 1) := by nlinarith
    _ ≤ Fintype.card (KeyRK k d) * ((k + 4) * n ^ k) := by
      apply Nat.mul_le_mul_left; nlinarith
    _ ≤ ((k + 1) ^ 2 * (d + 1) ^ k) * ((k + 4) * n ^ k) :=
      Nat.mul_le_mul_right _ keyRK_card
    _ = _ := by ring

lemma lineProg56_cost (hn : 1 ≤ n) :
    ((lineProg56 n d k).cost : ℝ) ≤ costLine56 n d k := by
  classical
  have hp : ((phiProg56 n d k).cost : ℝ) ≤ (d : ℝ) * NN n d := by
    unfold NN
    exact_mod_cast phiProg56_cost (n := n) (d := d) (k := k)
  have hacard : Fintype.card (BstLean.Part36.CoefIdxD n d) =
      n * Fintype.card (Mono n d) := by
    simp only [BstLean.Part36.CoefIdxD, Mono, Fintype.card_sigma,
      Fintype.card_prod, Fintype.card_fin]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have ha : ((anchorProg56 n d k).cost : ℝ) ≤ 2 * Pn n d := by
    have ht := anchorProg56_cost (n := n) (d := d) (k := k)
    unfold Pn BstLean.Part36.DD
    rw [hacard]
    have ht' : (anchorProg56 n d k).cost ≤ 2 * (n * Fintype.card (Mono n d)) := by
      simpa [Nat.mul_assoc] using ht
    exact_mod_cast ht'
  have ho : ((sumProgs (keyProg56 (n := n) (d := d) (k := k))).cost : ℝ) ≤
      ((k : ℝ) + 4) * ((k : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) ^ k * (n : ℝ) ^ k := by
    exact_mod_cast onlineProg56_cost (d := d) (k := k) hn
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : 0 ≤ ((d : ℝ) + 1) ^ k := by positivity
  have hnk : (n : ℝ) ^ k ≤ ((n : ℝ) + 1) ^ k := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) k
  have hb : ((k : ℝ) + 4) * ((k : ℝ) + 1) ^ 2 ≤ 4 * ((k : ℝ) + 2) ^ 3 := by
    nlinarith only [hk, sq_nonneg (k : ℝ), mul_nonneg hk (sq_nonneg (k : ℝ))]
  have ho' : ((sumProgs (keyProg56 (n := n) (d := d) (k := k))).cost : ℝ) ≤
      4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k := by
    calc
      _ ≤ _ := ho
      _ ≤ _ := mul_le_mul_of_nonneg_left hnk (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb hd) (by positivity)
  have hNN : 0 ≤ NN n d := by unfold NN; positivity
  simp only [lineProg56, cost_bind, Nat.cast_add]
  calc
    _ ≤ (d : ℝ) * NN n d + 2 * Pn n d +
        4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k :=
      add_le_add hp (add_le_add ha ho') |>.trans_eq (by ring)
    _ ≤ costLine56 n d k := by
      unfold costLine56
      linarith only [hNN]

end
end BstLean.Part56
