import BstLean.Part56MomProg_Values

/-! Stage A (reflection matrix, monomials of `v`, kernel inverses) and stage B (monomial images). -/

namespace BstLean.Part56.MomProg

open BstLean.Cost BstLean.Part56
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

lemma hp_arg1 {ι : Type} (a : Arg ι) (ha : BstLean.Part41.argHeavy a = 0) :
    HasProg (fun v (_ : Unit) => a.eval v []) 0 := hp_args (fun _ => a) (fun _ => ha)

lemma hp_uvec (a : Fin n) :
    HasProg (fun (w : InM56 n → ℝ) l => uvec a (fun l => w (Sum.inr l)) l) n := by
  classical
  have h : ∀ l : Fin n, HasProg (fun (w : InM56 n → ℝ) (_ : Unit) =>
      uvec a (fun l => w (Sum.inr l)) l) 1 := by
    intro l
    refine hp_congr (hp_op .sub (Arg.inp (Sum.inr l)) (Arg.cst (if l = a then 1 else 0)) rfl
      (by split_ifs <;> rfl)) ?_
    intro w u
    simp only [Arg.eval, Op.eval, uvec]
    split_ifs <;> simp
  simpa using hp_par h

lemma hp_Rfrom_u (n : ℕ) :
    HasProg (fun (u : Fin n → ℝ) (ml : Fin n × Fin n) =>
      (if ml.1 = ml.2 then (1 : ℝ) else 0) - 2 / (∑ i, u i ^ 2) * u ml.1 * u ml.2)
      ((2 * n - 1 + 2) + n * n * 3) := by
  classical
  have hc : HasProg (fun (u : Fin n → ℝ) (_ : Unit) => 2 / (∑ i, u i ^ 2)) (2 * n - 1 + 2) := by
    have h := hp_op2 .div (hp_op (ι := Fin n) .add (Arg.cst 1) (Arg.cst 1) rfl rfl)
      (hp_dot (fun i : Fin n => Arg.inp i) (fun i => Arg.inp i) (fun _ => rfl) (fun _ => rfl))
    refine hp_mono (hp_congr h ?_) (by simp; omega)
    intro u x
    simp only [Arg.eval, Op.eval, pow_two]
    norm_num
  have he : ∀ ml : Fin n × Fin n, HasProg (fun (s : Fin n ⊕ Unit → ℝ) (_ : Unit) =>
      (if ml.1 = ml.2 then (1 : ℝ) else 0) - s (Sum.inr ()) * s (Sum.inl ml.1) * s (Sum.inl ml.2))
      3 := by
    intro ml
    have h := hp_op2 .sub (hp_arg1 (ι := Fin n ⊕ Unit)
        (Arg.cst (if ml.1 = ml.2 then 1 else 0)) (by split_ifs <;> rfl))
      (hp_op2 .mul (hp_op .mul (Arg.inp (Sum.inr ())) (Arg.inp (Sum.inl ml.1)) rfl rfl)
        (hp_arg1 (Arg.inp (Sum.inl ml.2)) rfl))
    refine hp_congr h ?_
    intro s x
    simp only [Arg.eval, Op.eval]
    split_ifs <;> simp
  have hp := hp_bind hc (hp_par he)
  refine hp_mono (hp_congr hp ?_) (by simp [Fintype.card_prod])
  intro u ml
  simp only [Sum.elim_inl, Sum.elim_inr]

lemma hp_RmF (a : Fin n) :
    HasProg (fun (w : InM56 n → ℝ) => RmF a (fun l => w (Sum.inr l)))
      (n + ((2 * n - 1 + 2) + n * n * 3)) := by
  have h := hp_seq (hp_uvec a) (hp_Rfrom_u n)
  refine hp_congr h ?_
  intro w ml
  rfl

lemma prod_toList_map {α : Type} (s : Multiset α) (f : α → ℝ) :
    ((s.toList).map f).prod = (s.map f).prod := by
  conv_rhs => rw [← Multiset.coe_toList s]
  rw [Multiset.map_coe, Multiset.prod_coe]

lemma hp_pvF (d : ℕ) :
    HasProg (fun (w : InM56 n → ℝ) => pvF d (fun l => w (Sum.inr l)))
      (Fintype.card (Mono n d) * d) := by
  classical
  have h : ∀ p : Mono n d, HasProg (fun (w : InM56 n → ℝ) (_ : Unit) =>
      pvF d (fun l => w (Sum.inr l)) p) d := by
    intro p
    have h1 := hp_mapIn (hp_listprod (ι := Fin n) (p.2.val.toList)) (Sum.inr : Fin n → InM56 n)
    refine hp_mono (hp_congr h1 ?_) ?_
    · intro w u
      simp only [pvF, phiM, BstLean.Part36.monoVal, Function.comp_def]
      exact prod_toList_map _ _
    · rw [Multiset.length_toList, p.2.2]; exact Nat.le_of_lt_succ p.1.isLt
  exact hp_par h

lemma hp_kiF (d : ℕ) :
    HasProg (fun (pv : Mono n d → ℝ) (j : Fin (d + 1)) =>
      1 / ∑ p : Mono n d, (if (p.1 : ℕ) = (j : ℕ) then pv p else 0) *
        (if (p.1 : ℕ) = (j : ℕ) then pv p else 0))
      ((d + 1) * (2 * Fintype.card (Mono n d))) := by
  classical
  have hpos : 0 < Fintype.card (Mono n d) := Fintype.card_pos
  have h : ∀ j : Fin (d + 1), HasProg (fun (pv : Mono n d → ℝ) (_ : Unit) =>
      1 / ∑ p : Mono n d, (if (p.1 : ℕ) = (j : ℕ) then pv p else 0) *
        (if (p.1 : ℕ) = (j : ℕ) then pv p else 0)) (2 * Fintype.card (Mono n d)) := by
    intro j
    let ar : Mono n d → Arg (Mono n d) := fun p =>
      if (p.1 : ℕ) = (j : ℕ) then Arg.inp p else Arg.cst 0
    have har : ∀ p, BstLean.Part41.argHeavy (ar p) = 0 := by
      intro p; simp only [ar]; split_ifs <;> rfl
    have h1 := hp_op2 .div (hp_arg1 (Arg.cst 1) rfl) (hp_dot ar ar har har)
    refine hp_mono (hp_congr h1 ?_) (by omega)
    intro pv u
    simp only [Arg.eval, Op.eval, ar]
    congr 1
    · simp
    · apply Finset.sum_congr rfl; intro p _; split_ifs <;> simp [Arg.eval]
  simpa using hp_par h

lemma kiF_eq (d : ℕ) (v : Fin n → ℝ) (j : Fin (d + 1)) :
    kiF d v j = 1 / ∑ p : Mono n d, (if (p.1 : ℕ) = (j : ℕ) then pvF d v p else 0) *
        (if (p.1 : ℕ) = (j : ℕ) then pvF d v p else 0) := by
  simp only [kiF, kJ, phiB, pvF]

/-- Stage A. -/
lemma hp_stageA (a : Fin n) (d : ℕ) :
    HasProg (fun (w : InM56 n → ℝ) => Sum.elim (RmF a (fun l => w (Sum.inr l)))
      (Sum.elim (pvF d (fun l => w (Sum.inr l))) (kiF d (fun l => w (Sum.inr l)))))
      (costA n d (Fintype.card (Mono n d))) := by
  have h2 := hp_seq (hp_pvF (n := n) d) (hp_keep (hp_kiF (n := n) d))
  have h := hp_pair (hp_RmF a) h2
  refine hp_mono (hp_congr h ?_) ?_
  · intro w x
    rcases x with x | x | x
    · rfl
    · rfl
    · simp only [Sum.elim_inr]; exact (kiF_eq d _ x).symm
  · unfold costA
    have : n + ((2 * n - 1 + 2) + n * n * 3) ≤ 4 * (n + 1) ^ 2 := by
      have : 2 * n - 1 ≤ 2 * n := Nat.sub_le _ _
      nlinarith
    nlinarith

/-- The state after stage A. -/
abbrev SA (n d : ℕ) := (Fin n × Fin n) ⊕ (Mono n d ⊕ Fin (d + 1))

/-- Stage B: the images of the monomials. -/
lemma hp_stageB (d D : ℕ) :
    HasProg (fun (s : SA n d → ℝ) => imgF d D (fun ml => s (Sum.inl ml)))
      (costB d (Fintype.card (Idx n D)) (Fintype.card (Mono n d))) := by
  classical
  have h : ∀ p : Mono n d, HasProg (fun (s : SA n d → ℝ) (μ : Idx n D) =>
      imgF d D (fun ml => s (Sum.inl ml)) (p, μ)) (d * mulC n D) := by
    intro p
    have h1 := hp_plist_lin (ι := SA n d) D (fun m j => Sum.inl (m, j)) (p.2.val.toList)
    refine hp_mono (hp_congr h1 (fun s μ => rfl)) ?_
    rw [Multiset.length_toList, p.2.2]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt_succ p.1.isLt)
  have := hp_fam h
  exact hp_congr this (fun s pμ => rfl)

end BstLean.Part56.MomProg
