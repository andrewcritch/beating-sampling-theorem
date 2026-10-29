import BstLean.Part56MomProg_StageA

/-! Stage C (kernels, `τ`, `β`), stage D (the key products) and stage F (the weights). -/

namespace BstLean.Part56.MomProg

open BstLean.Cost BstLean.Part56
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

section stageC
variable (d D : ℕ)

lemma hp_kerP {ι : Type} (pvA : Mono n d → ι) (imgA : Mono n d × Idx n D → ι) :
    HasProg (fun (s : ι → ℝ) => kerF d D (fun p => s (pvA p)) (fun pμ => s (imgA pμ)))
      ((d + 1) * (Fintype.card (Idx n D) * (2 * Fintype.card (Mono n d)))) := by
  classical
  have h : ∀ j : Fin (d + 1), HasProg (fun (s : ι → ℝ) (μ : Idx n D) =>
      kerF d D (fun p => s (pvA p)) (fun pμ => s (imgA pμ)) (j, μ))
      (Fintype.card (Idx n D) * (2 * Fintype.card (Mono n d))) := by
    intro j
    have hμ : ∀ μ : Idx n D, HasProg (fun (s : ι → ℝ) (_ : Unit) =>
        kerF d D (fun p => s (pvA p)) (fun pμ => s (imgA pμ)) (j, μ))
        (2 * Fintype.card (Mono n d)) := by
      intro μ
      let ar : Mono n d → Arg ι := fun p =>
        if (p.1 : ℕ) = (j : ℕ) then Arg.inp (pvA p) else Arg.cst 0
      have har : ∀ p, BstLean.Part41.argHeavy (ar p) = 0 := by
        intro p; simp only [ar]; split_ifs <;> rfl
      have h1 := hp_dot ar (fun p => Arg.inp (imgA (p, μ))) har (fun _ => rfl)
      refine hp_mono (hp_congr h1 ?_) (by omega)
      intro s u
      simp only [kerF, ar]
      apply Finset.sum_congr rfl; intro p _; split_ifs <;> simp [Arg.eval]
    exact hp_par hμ
  simpa using hp_congr (hp_fam h) (fun s x => rfl)

lemma hp_sqP {ι : Type} (imgA : Mono n d × Idx n D → ι) :
    HasProg (fun (s : ι → ℝ) => sqF d D (fun pμ => s (imgA pμ)))
      (Fintype.card (Mono n d) * mulC n D) := by
  classical
  have h : ∀ p : Mono n d, HasProg (fun (s : ι → ℝ) (μ : Idx n D) =>
      sqF d D (fun pμ => s (imgA pμ)) (p, μ)) (mulC n D) := by
    intro p
    have h1 := hp_mul2 (hp_args (fun μ => Arg.inp (imgA (p, μ))) (fun _ => rfl))
      (hp_args (fun μ => Arg.inp (imgA (p, μ))) (fun _ => rfl))
    exact hp_mono (hp_congr h1 (fun s μ => rfl)) (by simp)
  exact hp_congr (hp_fam h) (fun s x => rfl)

lemma hp_kkP {ι : Type} (kerA : Fin (d + 1) × Idx n D → ι) :
    HasProg (fun (s : ι → ℝ) => kkF d D (fun x => s (kerA x))) ((d + 1) * mulC n D) := by
  classical
  have h : ∀ j : Fin (d + 1), HasProg (fun (s : ι → ℝ) (μ : Idx n D) =>
      kkF d D (fun x => s (kerA x)) (j, μ)) (mulC n D) := by
    intro j
    have h1 := hp_mul2 (hp_args (fun μ => Arg.inp (kerA (j, μ))) (fun _ => rfl))
      (hp_args (fun μ => Arg.inp (kerA (j, μ))) (fun _ => rfl))
    exact hp_mono (hp_congr h1 (fun s μ => rfl)) (by simp)
  simpa using hp_congr (hp_fam h) (fun s x => rfl)

lemma hp_diagP {ι : Type} (sqA : Mono n d × Idx n D → ι) :
    HasProg (fun (s : ι → ℝ) => diagF d D (fun x => s (sqA x)))
      ((d + 1) * (Fintype.card (Idx n D) * (2 * Fintype.card (Mono n d)))) := by
  classical
  have h : ∀ j : Fin (d + 1), HasProg (fun (s : ι → ℝ) (μ : Idx n D) =>
      diagF d D (fun x => s (sqA x)) (j, μ))
      (Fintype.card (Idx n D) * (2 * Fintype.card (Mono n d))) := by
    intro j
    have hμ : ∀ μ : Idx n D, HasProg (fun (s : ι → ℝ) (_ : Unit) =>
        diagF d D (fun x => s (sqA x)) (j, μ)) (2 * Fintype.card (Mono n d)) := by
      intro μ
      let ar : Mono n d → Arg ι := fun p =>
        if (p.1 : ℕ) = (j : ℕ) then Arg.inp (sqA (p, μ)) else Arg.cst 0
      have har : ∀ p, BstLean.Part41.argHeavy (ar p) = 0 := by
        intro p; simp only [ar]; split_ifs <;> rfl
      have h1 := hp_dot ar (fun _ => Arg.cst 1) har (fun _ => rfl)
      refine hp_mono (hp_congr h1 ?_) (by omega)
      intro s u
      simp only [diagF, ar]
      apply Finset.sum_congr rfl; intro p _; split_ifs <;> simp [Arg.eval]
    exact hp_par hμ
  simpa using hp_congr (hp_fam h) (fun s x => rfl)

lemma hp_tbP {ι : Type} (diagA : Fin (d + 1) × Idx n D → ι) (kiA : Fin (d + 1) → ι)
    (kkA kerA : Fin (d + 1) × Idx n D → ι) :
    HasProg (fun (s : ι → ℝ) => tbF d D (fun x => s (diagA x)) (fun j => s (kiA j))
      (fun x => s (kkA x)) (fun x => s (kerA x)))
      (Fintype.card (Idx n D) * (4 * d + 4)) := by
  classical
  have htau : ∀ μ : Idx n D, HasProg (fun (s : ι → ℝ) (_ : Unit) =>
      tauF d D (fun x => s (diagA x)) (fun j => s (kiA j)) (fun x => s (kkA x)) μ)
      ((d + 1) * 2 + (d + 1 - 1)) := by
    intro μ
    have hj : ∀ j : Fin (d + 1), HasProg (fun (s : ι → ℝ) (_ : Unit) =>
        if 1 ≤ (j : ℕ) then s (diagA (j, μ)) - s (kiA j) * s (kkA (j, μ)) else 0) 2 := by
      intro j
      by_cases h1 : 1 ≤ (j : ℕ)
      · have h2 := hp_op2 .sub (hp_arg1 (Arg.inp (diagA (j, μ))) rfl)
          (hp_op .mul (Arg.inp (kiA j)) (Arg.inp (kkA (j, μ))) rfl rfl)
        exact hp_congr h2 (fun s u => by simp [h1, Arg.eval, Op.eval])
      · exact hp_mono (hp_congr (hp_arg1 (ι := ι) (Arg.cst 0) rfl)
          (fun s u => by simp [h1, Arg.eval])) (by omega)
    have h3 := hp_sumF hj
    rw [Fintype.card_fin] at h3
    exact hp_congr h3 (fun s u => rfl)
  have hbeta : ∀ x : Fin (d + 1) × Idx n D, HasProg (fun (s : ι → ℝ) (_ : Unit) =>
      betaF d D (fun j => s (kiA j)) (fun x => s (kerA x)) x) 1 := by
    intro x
    exact hp_congr (hp_op .mul (Arg.inp (kiA x.1)) (Arg.inp (kerA x)) rfl rfl)
      (fun s u => by simp [betaF, Arg.eval, Op.eval])
  have h := hp_mapOut (hp_pair (hp_par htau) (hp_par hbeta))
    (fun oμ : Option (Fin (d + 1)) × Idx n D => match oμ.1 with
      | none => Sum.inl oμ.2
      | some j => Sum.inr (j, oμ.2))
  refine hp_mono (hp_congr h ?_) ?_
  · intro s x
    rcases x with ⟨_ | j, μ⟩ <;> rfl
  · simp only [Fintype.card_prod, Fintype.card_fin]
    have : (d + 1 - 1) = d := by omega
    rw [this]
    nlinarith

/-- The state after stages A and B. -/
abbrev S2 (n d D : ℕ) := SA n d ⊕ (Mono n d × Idx n D)

/-- Stage C. -/
lemma hp_stageC :
    HasProg (fun (s : S2 n d D → ℝ) =>
      let img := fun pμ => s (Sum.inr pμ)
      let ker := kerF d D (fun p => s (Sum.inl (Sum.inr (Sum.inl p)))) img
      tbF d D (diagF d D (sqF d D img)) (fun j => s (Sum.inl (Sum.inr (Sum.inr j))))
        (kkF d D ker) ker)
      (costC d (Fintype.card (Idx n D)) (Fintype.card (Mono n d))) := by
  have h12 := hp_pair (hp_kerP d D (ι := S2 n d D) (fun p => Sum.inl (Sum.inr (Sum.inl p)))
    (fun pμ => Sum.inr pμ)) (hp_sqP d D (ι := S2 n d D) (fun pμ => Sum.inr pμ))
  have h34 := hp_pair (hp_kkP d D (ι := S2 n d D ⊕ ((Fin (d + 1) × Idx n D) ⊕ (Mono n d × Idx n D)))
    (fun x => Sum.inr (Sum.inl x)))
    (hp_diagP d D (ι := S2 n d D ⊕ ((Fin (d + 1) × Idx n D) ⊕ (Mono n d × Idx n D)))
    (fun x => Sum.inr (Sum.inr x)))
  have h5 := hp_tbP d D
    (ι := (S2 n d D ⊕ ((Fin (d + 1) × Idx n D) ⊕ (Mono n d × Idx n D))) ⊕
      ((Fin (d + 1) × Idx n D) ⊕ (Fin (d + 1) × Idx n D)))
    (fun x => Sum.inr (Sum.inr x)) (fun j => Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr j)))))
    (fun x => Sum.inr (Sum.inl x)) (fun x => Sum.inl (Sum.inr (Sum.inl x)))
  have h := hp_seq (hp_keep h12) (hp_seq (hp_keep h34) h5)
  refine hp_mono (hp_congr h (fun s x => rfl)) ?_
  unfold costC
  rw [show mulC n D = mulCN (Fintype.card (Idx n D)) from rfl]
  nlinarith

end stageC

/-- Stage D: the products of the keys. -/
lemma hp_stageD (d D k : ℕ) :
    HasProg (fun (tb : Option (Fin (d + 1)) × Idx n D → ℝ) => QF d D (k := k) tb)
      (costD k (Fintype.card (Idx n D)) (Fintype.card (KeyRK k d))) := by
  classical
  have h : ∀ κ : KeyRK k d, HasProg (fun (tb : Option (Fin (d + 1)) × Idx n D → ℝ)
      (μ : Idx n D) => QF d D tb (κ, μ)) (2 * k * mulC n D) := by
    intro κ
    have h1 := hp_plist (ι := Option (Fin (d + 1)) × Idx n D) D (fun o μ => (o, μ)) (keyList d κ)
    refine hp_mono (hp_congr h1 (fun tb μ => rfl)) ?_
    apply Nat.mul_le_mul_right
    simp only [keyList, List.length_append, List.length_replicate, List.length_ofFn]
    have := κ.1.1.isLt; have := κ.1.2.isLt
    omega
  exact hp_congr (hp_fam h) (fun tb x => rfl)

end BstLean.Part56.MomProg
