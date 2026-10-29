import BstLean.Part282Draw
import BstLean.Part157Final

/-!
# Part 282 (C2), the output rule

`outProg k`: from the hit values `x₁, …, x_k` and the factor `a`, the output
`min(1, max(1/100, a·(Σx_i)/k))`, written as `1 − relu(1 − (1/100 + relu(aR − 1/100)))`.
`outProg_eval`: its value is `outRule a ((Σx_i)/k)`. `outProg_cost`: `(k − 1) + 8` operations.
Part 279 charges `k` additions and `outputWork` (4 operations): the count there is low by 3
for `k ≥ 1`.

`progOut_eq_outProg`: `progOut D t a k θ σ` is `outProg k` at the values `hitFn D t (ret θ, σ i)`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157

noncomputable section

/-- The inputs: the factor `a` and the `k` hit values. -/
abbrev OIn (k : ℕ) : Type := Unit ⊕ Fin k

def oVal {k : ℕ} (a : ℝ) (x : Fin k → ℝ) : OIn k → ℝ := Sum.elim (fun _ => a) x

def hitSumProg (k : ℕ) : RProg (OIn k) Unit :=
  RProg.ofProg (Prog.sumArgs ((List.finRange k).map fun i => Arg.inp (Sum.inr i)))

def outRuleE (k : ℕ) : RExpr (OIn k ⊕ Unit) :=
  RExpr.sub (.cst 1) (RExpr.relu (RExpr.sub (.cst 1) (RExpr.add (.cst (1 / 100))
    (RExpr.relu (RExpr.sub (RExpr.mul (.inp (Sum.inl (Sum.inl ())))
      (RExpr.div (.inp (Sum.inr ())) (.cst (k : ℚ)))) (.cst (1 / 100)))))))

/-- **The output program.** -/
def outProg (k : ℕ) : RProg (OIn k) Unit := (hitSumProg k).bind (outRuleE k).prog

theorem min_one_eq (y : ℝ) : min 1 y = 1 - relu (1 - y) := by
  unfold relu
  rcases le_total y 1 with h | h
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring

theorem max_hundredth_eq (x : ℝ) : max (1 / 100) x = 1 / 100 + relu (x - 1 / 100) := by
  unfold relu
  rcases le_total x (1 / 100) with h | h
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring

theorem outProg_eval {k : ℕ} (a : ℝ) (x : Fin k → ℝ) :
    (outProg k).eval (oVal a x) () = BstLean.Part156.outRule a ((∑ i, x i) / k) := by
  have hs : (hitSumProg k).eval (oVal a x) () = ∑ i, x i := by
    rw [hitSumProg, RProg.eval_ofProg, eval_sumArgs, List.map_map, Fin.sum_univ_def]
    rfl
  rw [outProg, RProg.eval_bind, RExpr.eval_prog]
  simp only [outRuleE, RExpr.eval_sub, RExpr.eval_relu, RExpr.eval_add, RExpr.eval_mul,
    RExpr.eval_div, RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr, Sum.elim_inl, hs]
  unfold BstLean.Part156.outRule
  rw [min_one_eq, max_hundredth_eq]
  simp [oVal]

theorem outProg_cost (k : ℕ) : (outProg k).cost = (k - 1) + 8 := by
  simp [outProg, hitSumProg, cost_sumArgs, outRuleE]

/-- **The output of the program is the output program at the hit values.** -/
theorem progOut_eq_outProg {n : ℕ} (D : Design n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) :
    progOut D t a k θ σ =
      (outProg k).eval (oVal a (fun i => hitFn D t (ret D.toCentres θ, σ i))) () := by
  rw [outProg_eval]
  rfl

end

end BstLean.Part282

/-- info: 'BstLean.Part282.progOut_eq_outProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.progOut_eq_outProg
