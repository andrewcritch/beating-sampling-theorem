import BstLean.Part56MomProg_StageC

/-! Stage F: the weights from the key vectors and the moment table. -/

namespace BstLean.Part56.MomProg

open BstLean.Cost BstLean.Part56
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

lemma hp_powU (l : ℕ) : HasProg (fun (w : Unit → ℝ) (_ : Unit) => w () ^ l) l := by
  have h := hp_listprod (List.replicate l ())
  refine hp_mono (hp_congr h ?_) (by simp)
  intro w u
  simp [List.map_replicate, List.prod_replicate]

lemma card_coef_le (n d : ℕ) :
    Fintype.card (BstLean.Part36.CoefIdxD n d) ≤ n * (n + 1) ^ d := by
  have h := BstLean.Part36.DD_eq n d
  unfold BstLean.Part36.DD at h
  have h2 : Fintype.card (BstLean.Part36.CoefIdxD n d) = n * (n + d).choose d := by
    exact_mod_cast h
  rw [h2]
  exact Nat.mul_le_mul_left _ (choose_le_pow' n d)

lemma hp_stageF (d D k : ℕ) :
    HasProg (fun (s : (KeyRK k d × Idx n D) ⊕ Idx n D → ℝ) =>
      WF d D (fun x => s (Sum.inl x)) (fun μ => s (Sum.inr μ)))
      (costF n d k (Fintype.card (Idx n D)) (Fintype.card (KeyRK k d))) := by
  classical
  have hpos : 0 < Fintype.card (Idx n D) := Fintype.card_pos_iff.mpr ⟨Idx.zero D⟩
  have h : ∀ κ : KeyRK k d, HasProg (fun (s : (KeyRK k d × Idx n D) ⊕ Idx n D → ℝ)
      (_ : Unit) => WF d D (fun x => s (Sum.inl x)) (fun μ => s (Sum.inr μ)) κ)
      (2 * Fintype.card (Idx n D) + k.factorial + 2 ^ k * k.factorial ^ 2 +
        n * (n + 1) ^ d + 2 * k + 10) := by
    intro κ
    have hS := hp_dot (ι := (KeyRK k d × Idx n D) ⊕ Idx n D)
      (fun μ : Idx n D => Arg.inp (Sum.inl (κ, μ))) (fun μ => Arg.inp (Sum.inr μ))
      (fun _ => rfl) (fun _ => rfl)
    have hST := hp_op2 .div hS (hp_arg1 (Arg.inp (Sum.inr (Idx.zero D))) rfl)
    have hW := hp_op2 (ι := (KeyRK k d × Idx n D) ⊕ Idx n D) .div
      (hp_nat (κ.1.1 : ℕ).factorial)
      (hp_nat (2 ^ (κ.1.2 : ℕ) * (κ.1.2 : ℕ).factorial * ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)).factorial))
    have hD := hp_seq (hp_op2 (ι := (KeyRK k d × Idx n D) ⊕ Idx n D) .div
      (hp_arg1 (Arg.cst 1) rfl) (hp_nat (Fintype.card (BstLean.Part36.CoefIdxD n d))))
      (hp_powU (κ.1.2 : ℕ))
    have hall := hp_op2 .mul (hp_op2 .mul hW hD) hST
    refine hp_mono (hp_congr hall ?_) ?_
    · intro s u
      simp only [WF, Arg.eval, Op.eval, wickC, BstLean.Part36.DD]
      push_cast
      ring
    · have hi : (κ.1.1 : ℕ) ≤ k := Nat.le_of_lt_succ κ.1.1.isLt
      have hl : (κ.1.2 : ℕ) ≤ k := Nat.le_of_lt_succ κ.1.2.isLt
      have h1 : (κ.1.1 : ℕ).factorial ≤ k.factorial := Nat.factorial_le hi
      have h2 : 2 ^ (κ.1.2 : ℕ) * (κ.1.2 : ℕ).factorial *
          ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)).factorial ≤ 2 ^ k * k.factorial ^ 2 := by
        have a1 : 2 ^ (κ.1.2 : ℕ) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hl
        have a2 : (κ.1.2 : ℕ).factorial ≤ k.factorial := Nat.factorial_le hl
        have a3 : ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)).factorial ≤ k.factorial :=
          Nat.factorial_le (by omega)
        calc _ ≤ 2 ^ k * k.factorial * k.factorial := by gcongr
          _ = _ := by ring
      have h3 := card_coef_le n d
      omega
  have := hp_par h
  refine hp_mono this ?_
  unfold costF
  rfl

end BstLean.Part56.MomProg
