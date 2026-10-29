import BstLean.Part282NodeFull
import BstLean.Part282RowOdd

/-!
# Part 282 (C2), one node pass for every `n` (even and odd)

`rowAny n` is `rowProg n` (even `n`) or `rowOdd n` (odd `n`); `nodeAny n` is the node pass of
`Part282NodeFull` with `rowAny n`. `passFSt_eq_nodeAny`, `passWSt_eq_nodeAny`: the stored tables
of `statedDesign n` are its outputs, for every `n`. `nodeAny_cost`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part150 BstLean.Part272
open BstLean.Part169 (A1 A2 Jz bR nodeS)

noncomputable section

def rowAny (n : ℕ) : RProg RowIn (Fin 2) := if n % 2 = 0 then rowProg n else rowOdd n

theorem rowAny_eval (n : ℕ) (s w α κ : ℝ) :
    (rowAny n).eval (rowVal s w α κ) 0 =
        (if Even n then sphA n (s * α) (w * κ) else sphAodd n (s * α) (w * κ)) ∧
      (rowAny n).eval (rowVal s w α κ) 1 =
        (if Even n then sphE n (s * α) (w * κ) else sphEodd n (s * α) (w * κ)) := by
  unfold rowAny
  by_cases he : n % 2 = 0
  · have he' : Even n := Nat.even_iff.mpr he
    rw [if_pos he, if_pos he', if_pos he']
    exact rowProg_eval n s w α κ
  · have he' : ¬ Even n := fun h => he (Nat.even_iff.mp h)
    rw [if_neg he, if_neg he', if_neg he']
    exact rowOdd_eval n s w α κ

theorem rowAny_cost (n : ℕ) :
    (rowAny n).cost = if n % 2 = 0 then 6 * ((n - 4) / 2) + 58 else 4 * Todd n + 5 * ((n - 5) / 2) + 108 := by
  unfold rowAny
  split_ifs
  · exact rowProg_cost n
  · exact rowOdd_cost n

def rowsAny (n : ℕ) : RProg (NFIn (mA n)) (Fin (mA n) × Fin 2) :=
  RProg.parL2 (fun i => (rowAny n).mapIn (rowIn (mA n) i)) (List.finRange (mA n))

/-- **One node pass, every `n`.** -/
def nodeAny (n : ℕ) : RProg (NFIn (mA n)) (Fin 2) :=
  (rowsAny n).bind ((nodeTail (mA n) (Jz n) n).mapIn (tailMap (mA n)))

theorem nodeAny_env (n : ℕ) (c : BstLean.Part157.Ret n) (s : ℝ) :
    (Sum.elim (nfVal s (√(1 - s ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c) (normSq (bR c)))
      ((rowsAny n).eval (nfVal s (√(1 - s ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c)
        (normSq (bR c)))) ∘ tailMap (mA n)) =
      nVal (a1St c s) (e1St c s) (A2 c) (bR c) (normSq (bR c)) := by
  have hr : ∀ i, (nfVal s (√(1 - s ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c) (normSq (bR c)) ∘
      rowIn (mA n) i) = rowVal s (√(1 - s ^ 2)) (alphaE c i) (kappaE c i) := by
    intro i; funext j; fin_cases j <;> rfl
  funext x
  rcases x with (i | i) | x
  · simp only [Function.comp_apply, tailMap, Sum.elim_inl, Sum.elim_inr, rowsAny]
    rw [RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), RProg.eval_mapIn, hr,
      (rowAny_eval n _ _ _ _).1]
    rfl
  · simp only [Function.comp_apply, tailMap, Sum.elim_inl, Sum.elim_inr, rowsAny]
    rw [RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), RProg.eval_mapIn, hr,
      (rowAny_eval n _ _ _ _).2]
    rfl
  · rfl

theorem passFSt_eq_nodeAny {n : ℕ} (c : BstLean.Part157.Ret n) (g : ℕ) :
    passFSt c g = (nodeAny n).eval
      (nfVal (nodeS c g) (√(1 - nodeS c g ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c)
        (normSq (bR c))) 0 := by
  rw [nodeAny, RProg.eval_bind, RProg.eval_mapIn, nodeAny_env, (nodeTail_eval _ _ _ _ _ _ _).1]
  rfl

theorem passWSt_eq_nodeAny {n : ℕ} (c : BstLean.Part157.Ret n) (g : ℕ) :
    passWSt c g = (nodeAny n).eval
      (nfVal (nodeS c g) (√(1 - nodeS c g ^ 2)) (alphaE c) (kappaE c) (A2 c) (bR c)
        (normSq (bR c))) 1 := by
  rw [nodeAny, RProg.eval_bind, RProg.eval_mapIn, nodeAny_env, (nodeTail_eval _ _ _ _ _ _ _).2]
  rfl

theorem nodeAny_cost {n : ℕ} (hn : 1 ≤ n) :
    (nodeAny n).cost = n ^ 2 * (rowAny n).cost +
      (n ^ 2 * (2 * n ^ 2 - 1) + 7 * n ^ 2 * (Jz n + 1) + 6 * n ^ 2 + 6) := by
  have hM : 1 ≤ mA n := Nat.one_le_pow _ _ hn
  rw [nodeAny, RProg.cost_bind, RProg.cost_mapIn, nodeTail_cost _ _ _ hM, rowsAny,
    RProg.cost_parL2, list_sum_const _ _ (rowAny n).cost (fun i => by rw [RProg.cost_mapIn])]
  simp [mA]

end

end BstLean.Part282

/-- info: 'BstLean.Part282.passFSt_eq_nodeAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.passFSt_eq_nodeAny
