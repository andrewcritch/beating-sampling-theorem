import BstLean.Part56MomProg_Formula

/-! Programs on coefficient vectors. -/

namespace BstLean.Part56.MomProg

open BstLean.Cost

variable {n : ℕ}

/-- A family of vector programs, run side by side. -/
lemma hp_famL {ι κ ν : Type} [DecidableEq κ] {F : κ → (ι → ℝ) → ν → ℝ} {c : ℕ}
    (hF : ∀ k, HasProg (F k) c) (l : List κ) :
    HasProg (fun w (kν : κ × ν) => if kν.1 ∈ l then F kν.1 w kν.2 else 0) (l.length * c) := by
  induction l with
  | nil =>
    refine hp_mono (hp_congr (hp_args (fun _ : κ × ν => Arg.cst (ι := ι) 0) (fun _ => rfl))
      (fun w kν => by simp [Arg.eval])) (by simp)
  | cons k l ih =>
    have h := hp_mapOut (hp_pair (hF k) ih)
      (fun kν : κ × ν => if kν.1 = k then Sum.inl kν.2 else Sum.inr kν)
    refine hp_mono (hp_congr h ?_) (by simp [Nat.succ_mul, Nat.add_comm])
    intro w kν
    by_cases h1 : kν.1 = k
    · simp [h1]
    · simp [h1]

lemma hp_fam {ι κ ν : Type} [Fintype κ] [DecidableEq κ] {F : κ → (ι → ℝ) → ν → ℝ} {c : ℕ}
    (hF : ∀ k, HasProg (F k) c) :
    HasProg (fun w (kν : κ × ν) => F kν.1 w kν.2) (Fintype.card κ * c) := by
  have h := hp_famL hF (Finset.univ.toList)
  refine hp_mono (hp_congr h ?_) (by simp)
  intro w kν; simp

/-- Cost of one truncated product. -/
noncomputable def mulC (n D : ℕ) : ℕ := Fintype.card (Idx n D) * (2 * Fintype.card (Idx n D) ^ 2)

/-- Argument reading `ext0 c ν` from the input copy `s`. -/
noncomputable def extArg {D : ℕ} {ι : Type} (s : Idx n D → ι) (ν : Fin n →₀ ℕ) : Arg ι :=
  if h : fdeg ν ≤ D then Arg.inp (s ⟨ν, h⟩) else Arg.cst 0

lemma extArg_heavy {D : ℕ} {ι : Type} (s : Idx n D → ι) (ν : Fin n →₀ ℕ) :
    BstLean.Part41.argHeavy (extArg s ν) = 0 := by
  unfold extArg; split_ifs <;> rfl

lemma extArg_eval {D : ℕ} {ι : Type} (s : Idx n D → ι) (ν : Fin n →₀ ℕ) (w : ι → ℝ) :
    (extArg s ν).eval w [] = ext0 (fun μ => w (s μ)) ν := by
  unfold extArg ext0; split_ifs <;> simp [Arg.eval]

lemma hp_pmul (D : ℕ) :
    HasProg (fun (w : Idx n D ⊕ Idx n D → ℝ) => pmul (fun μ => w (Sum.inl μ))
      (fun μ => w (Sum.inr μ))) (mulC n D) := by
  classical
  have h : ∀ μ : Idx n D, HasProg (fun (w : Idx n D ⊕ Idx n D → ℝ) (_ : Unit) =>
      pmul (fun μ => w (Sum.inl μ)) (fun μ => w (Sum.inr μ)) μ)
      (2 * Fintype.card (Idx n D) ^ 2) := by
    intro μ
    have hd := hp_dot (ι := Idx n D ⊕ Idx n D)
      (κ := (Finset.HasAntidiagonal.antidiagonal μ.1 : Set ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))))
      (fun x => extArg Sum.inl x.1.1) (fun x => extArg Sum.inr x.1.2)
      (fun _ => extArg_heavy _ _) (fun _ => extArg_heavy _ _)
    refine hp_mono (hp_congr hd ?_) ?_
    · intro w u
      simp only [extArg_eval, pmul]
    · have := card_antidiag_le μ
      rw [sq]; omega
  exact hp_par h

/-- Product of two vector programs. -/
lemma hp_mul2 {ι : Type} {D : ℕ} {F G : (ι → ℝ) → Idx n D → ℝ} {a b : ℕ}
    (hF : HasProg F a) (hG : HasProg G b) :
    HasProg (fun w => pmul (F w) (G w)) (a + b + mulC n D) := by
  have h := hp_seq (hp_pair hF hG) (hp_pmul D)
  exact hp_congr h (fun w μ => rfl)

lemma hp_oneVec {ι : Type} (D : ℕ) : HasProg (fun (_ : ι → ℝ) => oneVec (n := n) (D := D)) 0 := by
  classical
  have h := hp_args (fun μ : Idx n D => if μ.1 = 0 then Arg.cst (ι := ι) 1 else Arg.cst 0)
    (fun μ => by split_ifs <;> rfl)
  refine hp_congr h ?_
  intro w μ
  unfold oneVec
  split_ifs <;> simp [Arg.eval]

/-- A list product of input vectors. -/
lemma hp_plist {ι κ : Type} (D : ℕ) (vec : κ → Idx n D → ι) (l : List κ) :
    HasProg (fun (w : ι → ℝ) => plist (l.map fun k μ => w (vec k μ)))
      (l.length * mulC n D) := by
  induction l with
  | nil => exact hp_mono (hp_oneVec D) (by simp)
  | cons k l ih =>
    have hk := hp_args (fun μ => Arg.inp (vec k μ)) (fun _ => rfl)
    have h := hp_mul2 hk ih
    refine hp_mono (hp_congr h ?_) ?_
    · intro w μ; rfl
    · simp [Nat.succ_mul, Nat.add_comm]

/-- Argument for `linVec`. -/
noncomputable def linArg {D : ℕ} {ι : Type} (s : Fin n → ι) (μ : Idx n D) : Arg ι :=
  if h : ∃ l, μ.1 = Finsupp.single l 1 then Arg.inp (s h.choose) else Arg.cst 0

lemma linArg_eval {D : ℕ} {ι : Type} (s : Fin n → ι) (μ : Idx n D) (w : ι → ℝ) :
    (linArg s μ).eval w [] = linVec (fun l => w (s l)) μ := by
  unfold linArg linVec; split_ifs <;> simp [Arg.eval]

lemma hp_linVec {ι : Type} (D : ℕ) (s : Fin n → ι) :
    HasProg (fun (w : ι → ℝ) => linVec (D := D) (fun l => w (s l))) 0 := by
  have h := hp_args (fun μ : Idx n D => linArg s μ) (fun μ => by unfold linArg; split_ifs <;> rfl)
  exact hp_congr h (fun w μ => linArg_eval s μ w)

/-- A list product of linear forms read from a matrix input. -/
lemma hp_plist_lin {ι : Type} (D : ℕ) (s : Fin n → Fin n → ι) (l : List (Fin n)) :
    HasProg (fun (w : ι → ℝ) => plist (l.map fun m => linVec (D := D) (fun j => w (s m j))))
      (l.length * mulC n D) := by
  induction l with
  | nil => exact hp_mono (hp_oneVec D) (by simp)
  | cons k l ih =>
    have h := hp_mul2 (hp_linVec D (s k)) ih
    refine hp_mono (hp_congr h ?_) ?_
    · intro w μ; rfl
    · simp [Nat.succ_mul, Nat.add_comm]

end BstLean.Part56.MomProg
