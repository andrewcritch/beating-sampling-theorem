import BstLean.Part59Defs
import BstLean.Part53Cost_Shared
import BstLean.Part36Index

namespace BstLean.Part59.ConstantAux59x

open BstLean.Cost
open BstLean.Part53.CostAux
open BstLean.Part41 (argHeavy)

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dimension59x (ι : Type) (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Prog ι Unit, Clean p ∧ (∀ v, p.eval v () = (n : ℝ)) ∧
      p.cost ≤ 2 * Nat.log 2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      refine ⟨Prog.ofArgs (fun _ => .cst 1), ?_, ?_, ?_⟩ <;>
        simp [Clean, Prog.ofArgs, Prog.eval, Arg.eval, argHeavy, Prog.cost]
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨p, hp, he, hc⟩ := ih (n / 2) (Nat.div_lt_self (by omega) (by omega))
        (Nat.div_pos hn2 (by omega))
      let dbl : Prog (ι ⊕ Unit) Unit := Prog.op1 .add (.inp (.inr ())) (.inp (.inr ()))
      have hdbl : Clean dbl := by simp [dbl, Clean, Prog.op1, argHeavy]
      by_cases hmod : n % 2 = 0
      · refine ⟨p.bind dbl, clean_bind hp hdbl, ?_, ?_⟩
        · intro v
          simp only [eval_bind, eval_op1, Arg.eval, Op.eval, Sum.elim_inr, he, dbl]
          have heq : n / 2 + n / 2 = n := by omega
          exact_mod_cast heq
        · rw [cost_bind]
          have hlog := Nat.log_of_one_lt_of_le (by omega : 1 < 2) hn2
          rw [show dbl.cost = 1 from rfl]
          omega
      · let add1 : Prog (ι ⊕ Unit) Unit := Prog.op1 .add (.inp (.inr ())) (.cst 1)
        have hadd : Clean add1 := by simp [add1, Clean, Prog.op1, argHeavy]
        refine ⟨(p.bind dbl).bind add1, clean_bind (clean_bind hp hdbl) hadd, ?_, ?_⟩
        · intro v
          simp only [eval_bind, eval_op1, Arg.eval, Op.eval, Sum.elim_inr, he, dbl, add1,
            Rat.cast_one]
          have heq : n / 2 + n / 2 + 1 = n := by omega
          exact_mod_cast heq
        · simp only [cost_bind]
          have hlog := Nat.log_of_one_lt_of_le (by omega : 1 < 2) hn2
          rw [show dbl.cost = 1 from rfl, show add1.cost = 1 from rfl]
          omega

/-- State entries: dimension, current integer, binomial product, reciprocal factorial, sum. -/
def step59x : Prog (Fin 5) (Fin 5) :=
  ⟨[⟨.add, .inp 1, .cst 1⟩,
    ⟨.add, .inp 0, .reg 0⟩,
    ⟨.div, .reg 1, .reg 0⟩,
    ⟨.mul, .inp 2, .reg 2⟩,
    ⟨.div, .inp 3, .reg 0⟩,
    ⟨.add, .inp 4, .reg 4⟩],
    fun i => if i = 0 then .inp 0 else if i = 1 then .reg 0 else
      if i = 2 then .reg 3 else if i = 3 then .reg 4 else .reg 5⟩

def state59x (n j : ℕ) : Fin 5 → ℝ := fun i =>
  if i = 0 then n else if i = 1 then j else if i = 2 then (n + j).choose j else
    if i = 3 then 1 / (j.factorial : ℝ) else
      (∑ r ∈ Finset.range (j + 1), 1 / (r.factorial : ℝ)) - 1

lemma step_clean59x : Clean step59x := by
  constructor
  · intro I hI
    simp only [step59x, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [argHeavy]
  · intro i
    dsimp [step59x]
    split_ifs <;> rfl

lemma step_cost59x : step59x.cost = 6 := rfl

lemma step_eval59x (n j : ℕ) : step59x.eval (state59x n j) = state59x n (j + 1) := by
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hchoose : (((n + j + 1).choose (j + 1) : ℕ) : ℝ) =
      (((n + j).choose j : ℕ) : ℝ) * ((n : ℝ) + (j : ℝ) + 1) / ((j : ℝ) + 1) := by
    apply (eq_div_iff hj).mpr
    have h := Nat.add_one_mul_choose_eq (n + j) j
    have h' : ((n : ℝ) + (j : ℝ) + 1) * ((n + j).choose j : ℝ) =
        ((n + j + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by exact_mod_cast h
    nlinarith
  have hfac : 1 / (j.factorial : ℝ) / ((j : ℝ) + 1) = 1 / ((j + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [div_div, mul_comm]
  funext i
  fin_cases i <;>
    simp [step59x, state59x, Prog.eval, run, Instr.eval, Arg.eval, Op.eval,
      List.getD, Finset.sum_range_succ, Nat.add_assoc]
  all_goals
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      add_comm, add_left_comm, add_assoc] at hchoose hfac ⊢
  · simpa only [mul_div_assoc] using hchoose.symm
  · simpa only [one_div] using hfac
  · simp only [one_div] at hfac
    rw [hfac]
    ring

theorem a_constant59x (ι : Type) (n d : ℕ) (hn : 1 ≤ n) :
    ∃ p : Prog ι Unit, Clean p ∧ (∀ v, p.eval v () = BstLean.Part53.aH n d) ∧
      p.cost ≤ 2 * Nat.log 2 n + 6 * d + 2 := by
  obtain ⟨pn, hpn, hen, hcn⟩ := dimension59x ι n hn
  let init : Prog (ι ⊕ Unit) (Fin 5) := Prog.ofArgs (fun i =>
    if i = 0 then .inp (.inr ()) else if i = 1 then .cst 0 else
      if i = 4 then .cst 0 else .cst 1)
  have hi : Clean init := by
    constructor
    · simp [init, Prog.ofArgs]
    · intro i; dsimp [init, Prog.ofArgs]; split_ifs <;> simp [argHeavy]
  have hei : ∀ v, (pn.bind init).eval v = state59x n 0 := by
    intro v
    funext i
    rw [eval_bind]
    fin_cases i <;> simp [init, state59x, eval_ofArgs, Arg.eval, hen]
  have hloop : ∀ j, ∃ p : Prog ι (Fin 5), Clean p ∧
      (∀ v, p.eval v = state59x n j) ∧ p.cost ≤ 2 * Nat.log 2 n + 6 * j := by
    intro j
    induction j with
    | zero =>
      refine ⟨pn.bind init, clean_bind hpn hi, hei, ?_⟩
      rw [cost_bind, show init.cost = 0 from rfl]
      simpa using hcn
    | succ j ih =>
      obtain ⟨p, hp, he, hc⟩ := ih
      refine ⟨p.bind (step59x.mapIn Sum.inr), clean_bind hp (clean_mapIn _ step_clean59x), ?_, ?_⟩
      · intro v
        funext i
        rw [eval_bind, eval_mapIn]
        change step59x.eval (p.eval v) i = _
        rw [he, step_eval59x]
      · rw [cost_bind, cost_mapIn, step_cost59x]
        omega
  obtain ⟨p, hp, he, hc⟩ := hloop d
  let out : Prog (ι ⊕ Fin 5) Unit :=
    (Prog.op1 .mul (.inp (.inr 0)) (.inp (.inr 2))).bind
      (Prog.op1 .div (.inp (.inl (.inr 4))) (.inp (.inr ())))
  have hout : Clean out := by
    apply clean_bind <;> simp [Clean, Prog.op1, argHeavy]
  refine ⟨p.bind out, clean_bind hp hout, ?_, ?_⟩
  · intro v
    simp only [out, eval_bind, eval_op1, Arg.eval, Op.eval, Sum.elim_inr, Sum.elim_inl, he]
    change ((∑ r ∈ Finset.range (d + 1), 1 / (r.factorial : ℝ)) - 1) /
      ((n : ℝ) * ((n + d).choose d : ℝ)) = _
    rw [← BstLean.Part36.DD_eq]
    rfl
  · have ho : out.cost = 2 := by simp [out, cost_bind]
    rw [cost_bind, ho]
    omega

end
end BstLean.Part59.ConstantAux59x
