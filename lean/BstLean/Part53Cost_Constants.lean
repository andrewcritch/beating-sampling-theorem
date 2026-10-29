import BstLean.Part53Cost_Shared

namespace BstLean.Part53.CostAux

set_option backward.isDefEq.respectTransparency false

open BstLean.Cost
open BstLean.Part41 (heavyCount heavyConsts argHeavy)

noncomputable section

abbrev WeightKey (k : ℕ) := Fin (k + 1) × Fin (k + 1)

def heatWeight (n d : ℕ) {k : ℕ} (s : WeightKey k) : ℝ :=
  (aH n d / 2) ^ s.2.val / (s.2.val.factorial : ℝ) *
    (((s.1.val + 2 * s.2.val).factorial : ℝ) / (s.1.val.factorial : ℝ))

theorem nat_constants {ι κ : Type} [Fintype κ] (values : κ → ℕ) (β : ℕ)
    (hβ : 1 ≤ β) (hv : ∀ o, values o < 2 ^ β) :
    ∃ p : Prog ι κ, Clean p ∧ (∀ v o, p.eval v o = (values o : ℝ)) ∧
      p.cost ≤ 4 * β * Fintype.card κ := by
  classical
  let p0 : Prog ι κ := Prog.ofArgs (fun o => .cst (values o : ℚ))
  have hh : ∀ q ∈ heavyConsts p0, q.num.natAbs < 2 ^ β ∧ q.den < 2 ^ β := by
    intro q hq
    unfold heavyConsts at hq
    simp only [p0, Prog.ofArgs, List.flatMap_nil, List.nil_append,
      List.mem_filterMap] at hq
    obtain ⟨a, ha, hqa⟩ := hq
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
    dsimp only at hqa
    have hq' : (values o : ℚ) = q := by split_ifs at hqa; simp_all
    subst q
    constructor
    · simpa using hv o
    · simp only [Rat.den_natCast]
      have hp : 2 ≤ 2 ^ β := le_trans (by norm_num : 2 ≤ 2 ^ (1 : ℕ))
        (Nat.pow_le_pow_right (by omega) hβ)
      omega
  obtain ⟨p, h0, he, hc⟩ := BstLean.Part41.inline_consts p0 β hh
  refine ⟨p, clean_of_heavy h0, ?_, ?_⟩
  · intro v o
    rw [he]
    simp [p0, Arg.eval]
  · have hcount : heavyCount p0 ≤ Fintype.card κ := by
      simp only [heavyCount, p0, Prog.ofArgs, List.map_nil, List.sum_nil, zero_add]
      calc
        ∑ o, argHeavy (.cst (values o : ℚ) : Arg ι) ≤ ∑ _o : κ, 1 := by
          apply Finset.sum_le_sum
          intro o ho
          simp only [argHeavy]
          split_ifs <;> omega
        _ = Fintype.card κ := by simp
    have hp0 : p0.cost = 0 := rfl
    rw [hp0, zero_add] at hc
    exact hc.trans (Nat.mul_le_mul_left _ hcount)

theorem integer_constants (S : ℕ) (ι : Type) :
    ∃ p : Prog ι (Fin (S + 1)), Clean p ∧
      (∀ v j, p.eval v j = (j.val : ℝ)) ∧ p.cost ≤ 4 * (S + 1) ^ 2 := by
  obtain ⟨p, hp, he, hc⟩ := nat_constants (ι := ι) (fun j : Fin (S + 1) => j.val)
    (S + 1) (by omega) (fun j => lt_of_lt_of_le j.isLt (Nat.lt_two_pow_self.le))
  refine ⟨p, hp, he, ?_⟩
  simpa [pow_two, Nat.mul_assoc] using hc

theorem dimension_constant (D : ℕ) (ι : Type) :
    ∃ p : Prog ι Unit, Clean p ∧ (∀ v, p.eval v () = (D : ℝ)) ∧
      p.cost ≤ 4 * (Nat.log 2 D + 1) := by
  obtain ⟨p, hp, he, hc⟩ := nat_constants (ι := ι) (fun _ : Unit => D)
    (Nat.log 2 D + 1) (by omega) (fun _ => Nat.lt_pow_succ_log_self (by omega) D)
  exact ⟨p, hp, fun v => he v (), by simpa using hc⟩

private def factArgs {S : ℕ} (j : Fin (S + 1)) : List (Arg (Fin (S + 1))) :=
  (List.finRange j.val).map (fun r => .inp ⟨r.val + 1, by have := r.isLt; have := j.isLt; omega⟩)

def factorialProg (S : ℕ) : Prog (Fin (S + 1)) (Fin (S + 1)) :=
  Prog.par (fun j => prodProg (factArgs j)) (List.finRange (S + 1))

theorem factorialProg_clean (S : ℕ) : Clean (factorialProg S) := by
  apply clean_par
  intro j
  apply prodProg_clean
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  rfl

theorem factorialProg_eval (S : ℕ) (j : Fin (S + 1)) :
    (factorialProg S).eval (fun r => (r.val : ℝ)) j = (j.val.factorial : ℝ) := by
  rw [factorialProg, eval_par_mem _ _ _ _ (List.mem_finRange j), prodProg_eval]
  simp only [factArgs, List.map_map, Function.comp_def, Arg.eval]
  rw [← Fin.prod_univ_def]
  norm_cast
  exact (Fin.prod_univ_eq_prod_range (fun r : ℕ => r + 1) j.val).trans
    (Finset.prod_range_add_one_eq_factorial _)

theorem factorialProg_cost (S : ℕ) : (factorialProg S).cost ≤ (S + 1) * S := by
  rw [factorialProg, cost_par]
  calc
    _ ≤ ((List.finRange (S + 1)).map (fun _ => S)).sum := by
      apply List.sum_le_sum
      intro j hj
      simp only [prodProg_cost, factArgs, List.length_map, List.length_finRange]
      have := j.isLt
      omega
    _ = (S + 1) * S := by simp [Nat.mul_comm]

abbrev CompKey (k : ℕ) := Σ c : Fin (k + 1), Composition c.val

theorem card_compKey (k : ℕ) : Fintype.card (CompKey k) ≤ (k + 1) * 2 ^ k := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _c : Fin (k + 1), 2 ^ k := by
      apply Finset.sum_le_sum
      intro c hc
      rw [composition_card]
      apply Nat.pow_le_pow_right (by omega)
      have := c.isLt
      omega
    _ = (k + 1) * 2 ^ k := by simp

def compWeight {k : ℕ} (s : CompKey k) : ℝ :=
  (s.1.val.factorial : ℝ) / (s.2.blocks.map (fun j => (j.factorial : ℝ))).prod

end
end BstLean.Part53.CostAux
