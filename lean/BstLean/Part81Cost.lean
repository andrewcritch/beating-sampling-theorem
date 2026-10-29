import BstLean.Part81Bridge
import BstLean.Part59CostCmp

/-!
# Part 81, cost: the cost comparison with a threshold on `n` that does not depend on `d`

`Pn n d = 𝒟(n,d) = n · C(n+d,d)` and `C(n+d,d) ≥ n + d` for `n, d ≥ 1`, so `Pn n d ≥ n² + n·d`.
Hence `costG59 n d 2 < 2 · Pp n d 2` from `n ≥ 6` on, for every `d ≥ 1`.
-/

namespace BstLean.Part81

open BstLean.Cost
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono Pn heavyCount)
open BstLean.Part59

/-- `C(n+d,d) ≥ n + d` for `n, d ≥ 1`. -/
lemma add_le_choose81 (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) : n + d ≤ (n + d).choose d := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ d hd ih =>
    have h1 : (n + (d + 1)).choose (d + 1) = (n + d).choose d + (n + d).choose (d + 1) := by
      rw [← Nat.add_assoc, Nat.choose_succ_succ]
    have h2 : 0 < (n + d).choose (d + 1) := Nat.choose_pos (by omega)
    omega

/-- **Growth in `d`**: `Pn n d ≥ n² + n·d` for `n, d ≥ 1`. -/
lemma Pn_ge_sq_add81 (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (n : ℝ) ^ 2 + (n : ℝ) * d ≤ Pn n d := by
  have hc : ((n : ℝ) + d) ≤ ((n + d).choose d : ℝ) := by
    exact_mod_cast add_le_choose81 n d hn hd
  unfold Pn
  rw [BstLean.Part36.DD_eq]
  have := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) n)
  nlinarith

/-- `costG59 < 2P′` at `d_f = 2`, for every `d ≥ 1` and every `n ≥ 6`. -/
theorem costG59_lt_twoPp_unif (n d : ℕ) (hd : 1 ≤ d) (hn : 6 ≤ n) :
    costG59 n d 2 < 2 * Pp n d 2 := by
  have hP := Pn_ge_sq_add81 n d (by omega) hd
  have hC := choose_ge_one59 n 2
  have hlog : (Nat.log 2 n : ℝ) ≤ n := by exact_mod_cast Nat.log_le_self 2 n
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnd : (6 : ℝ) * d ≤ (n : ℝ) * d := mul_le_mul_of_nonneg_right hn' hd0
  unfold costG59 Pp costF
  norm_num
  nlinarith

/-- **The program**, with a threshold on `n` that does not depend on `d`. -/
theorem prog81_unif (n d : ℕ) (hd : 1 ≤ d) (hn : 6 ≤ n) (ε : ℝ) :
    ∃ pg : Prog (In59 n d 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d 2 → ℝ, pg.eval v () = g0Q n d 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d 2 ε ∧
      ∀ (c : Mono n 2 → ℝ) (M : CoefIdxD n d → ℝ),
        pg.eval (inp59 c M) () = g0Q n d 2 c M := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n d 2 hn1 hd (by norm_num)
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 2 ε pg.cost hcost
    ((costG59_lt_twoPp_unif n d hd hn).trans_le (twoPp_le_baselineF n d 2 ε)), ?_⟩
  intro c M
  rw [hspec, (cv59_inp 2 c M).1, (cv59_inp 2 c M).2]

end BstLean.Part81

#print axioms BstLean.Part81.Pn_ge_sq_add81
#print axioms BstLean.Part81.costG59_lt_twoPp_unif
#print axioms BstLean.Part81.prog81_unif
