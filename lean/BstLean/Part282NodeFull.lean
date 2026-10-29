import BstLean.Part282Node

/-!
# Part 282 (C2), one node pass with its rows (even `n`)

`nodeProg n`: the `m_A = n²` sphere rows (`rowProg n`, one per row, sharing `s_g` and
`√(1 − s_g²)`) and then the node pass after the rows (`nodeTail`). The inputs are `s_g`,
`√(1 − s_g²)`, the row data `α_i`, `κ_i`, the matrix `A₂`, the vector `b` and `|b|²`.

`passFSt_eq_nodeProg`, `passWSt_eq_nodeProg` (even `n`): the stored tables `f̃_g`, `ω̃_g` of
`statedDesign n` are the two outputs of `nodeProg n` at the node `s_g = nodeS c g`.
`nodeProg_cost`: `n²(6P + 58) + n²(2n² − 1) + 7n²(J_z + 1) + 6n² + 6`, `P = (n − 4)/2`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part150 BstLean.Part272
open BstLean.Part169 (A1 A2 Jz bR nodeS)

noncomputable section

/-- The inputs: `![s, w]`, `α`, `κ`; `A₂`; `b`; `|b|²`. -/
abbrev NFIn (M : ℕ) : Type := (Fin 2 ⊕ (Fin M ⊕ Fin M)) ⊕ ((Fin M × Fin M) ⊕ (Fin M ⊕ Unit))

def nfVal {M : ℕ} (s w : ℝ) (α κ : Fin M → ℝ) (A : Matrix (Fin M) (Fin M) ℝ) (b : Fin M → ℝ)
    (nb : ℝ) : NFIn M → ℝ :=
  Sum.elim (Sum.elim ![s, w] (Sum.elim α κ)) (Sum.elim (fun p => A p.1 p.2) (Sum.elim b fun _ => nb))

/-- The inputs of row `i`. -/
def rowIn (M : ℕ) (i : Fin M) : RowIn → NFIn M :=
  ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1), Sum.inl (Sum.inr (Sum.inl i)),
    Sum.inl (Sum.inr (Sum.inr i))]

def rowsProg (n : ℕ) : RProg (NFIn (mA n)) (Fin (mA n) × Fin 2) :=
  RProg.parL2 (fun i => (rowProg n).mapIn (rowIn (mA n) i)) (List.finRange (mA n))

def tailMap (M : ℕ) : NIn M → NFIn M ⊕ (Fin M × Fin 2) :=
  Sum.elim (Sum.elim (fun i => Sum.inr (i, 0)) (fun i => Sum.inr (i, 1))) (fun x => Sum.inl (Sum.inr x))

/-- **One node pass with its rows.** -/
def nodeProg (n : ℕ) : RProg (NFIn (mA n)) (Fin 2) :=
  (rowsProg n).bind ((nodeTail (mA n) (Jz n) n).mapIn (tailMap (mA n)))

theorem nodeProg_env (n : ℕ) (s w : ℝ) (α κ : Fin (mA n) → ℝ) (A : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (b : Fin (mA n) → ℝ) (nb : ℝ) :
    (Sum.elim (nfVal s w α κ A b nb) ((rowsProg n).eval (nfVal s w α κ A b nb)) ∘ tailMap (mA n)) =
      nVal (fun i => sphA n (s * α i) (w * κ i)) (fun i => sphE n (s * α i) (w * κ i)) A b nb := by
  have hr : ∀ i, (nfVal s w α κ A b nb ∘ rowIn (mA n) i) = rowVal s w (α i) (κ i) := by
    intro i; funext j; fin_cases j <;> rfl
  funext x
  rcases x with (i | i) | x
  · simp only [Function.comp_apply, tailMap, Sum.elim_inl, Sum.elim_inr, rowsProg]
    rw [RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), RProg.eval_mapIn, hr,
      (rowProg_eval n _ _ _ _).1]
    rfl
  · simp only [Function.comp_apply, tailMap, Sum.elim_inl, Sum.elim_inr, rowsProg]
    rw [RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), RProg.eval_mapIn, hr,
      (rowProg_eval n _ _ _ _).2]
    rfl
  · rfl

theorem nodeProg_eval (n : ℕ) (s w : ℝ) (α κ : Fin (mA n) → ℝ)
    (A : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (b : Fin (mA n) → ℝ) (nb : ℝ) (k : Fin 2) :
    (nodeProg n).eval (nfVal s w α κ A b nb) k =
      (nodeTail (mA n) (Jz n) n).eval
        (nVal (fun i => sphA n (s * α i) (w * κ i)) (fun i => sphE n (s * α i) (w * κ i)) A b nb) k := by
  rw [nodeProg, RProg.eval_bind, RProg.eval_mapIn, nodeProg_env]

/-- **The stored table `f̃_g` of the stated design is the node program (even `n`).** -/
theorem passFSt_eq_nodeProg {n : ℕ} (he : Even n) (c : BstLean.Part157.Ret n) (g : ℕ) :
    passFSt c g = (nodeProg n).eval
      (nfVal (nodeS c g) (√(1 - nodeS c g ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c)
        (normSq (bR c))) 0 := by
  rw [nodeProg_eval, (nodeTail_eval _ _ _ _ _ _ _).1]
  have ha : (fun i => sphA n (nodeS c g * alphaE c i) (√(1 - nodeS c g ^ 2) * kappaE c i)) =
      a1St c (nodeS c g) := by
    funext i; rw [a1St, if_pos he]
  have he' : (fun i => sphE n (nodeS c g * alphaE c i) (√(1 - nodeS c g ^ 2) * kappaE c i)) =
      e1St c (nodeS c g) := by
    funext i; rw [e1St, if_pos he]
  rw [ha, he']
  rfl

/-- **The stored table `ω̃_g` of the stated design is the node program (even `n`).** -/
theorem passWSt_eq_nodeProg {n : ℕ} (he : Even n) (c : BstLean.Part157.Ret n) (g : ℕ) :
    passWSt c g = (nodeProg n).eval
      (nfVal (nodeS c g) (√(1 - nodeS c g ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c)
        (normSq (bR c))) 1 := by
  rw [nodeProg_eval, (nodeTail_eval _ _ _ _ _ _ _).2]
  have ha : (fun i => sphA n (nodeS c g * alphaE c i) (√(1 - nodeS c g ^ 2) * kappaE c i)) =
      a1St c (nodeS c g) := by
    funext i; rw [a1St, if_pos he]
  have he' : (fun i => sphE n (nodeS c g * alphaE c i) (√(1 - nodeS c g ^ 2) * kappaE c i)) =
      e1St c (nodeS c g) := by
    funext i; rw [e1St, if_pos he]
  rw [ha, he']
  rfl

theorem nodeProg_cost {n : ℕ} (hn : 1 ≤ n) :
    (nodeProg n).cost = n ^ 2 * (6 * ((n - 4) / 2) + 58) +
      (n ^ 2 * (2 * n ^ 2 - 1) + 7 * n ^ 2 * (Jz n + 1) + 6 * n ^ 2 + 6) := by
  have hM : 1 ≤ mA n := Nat.one_le_pow _ _ hn
  rw [nodeProg, RProg.cost_bind, RProg.cost_mapIn, nodeTail_cost _ _ _ hM, rowsProg,
    RProg.cost_parL2, list_sum_const _ _ (6 * ((n - 4) / 2) + 58)
      (fun i => by rw [RProg.cost_mapIn, rowProg_cost])]
  simp [mA]

end

end BstLean.Part282

/-- info: 'BstLean.Part282.passFSt_eq_nodeProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.passFSt_eq_nodeProg
