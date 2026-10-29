import BstLean.Part59Defs
import BstLean.Part36Index

/-!
# Part 59, wave 1: the cost comparison (Cor C) — proved

Specification: `delegations/answers/p59-spec-opus.md` §3.12. Source: `omDL2-opus-prover.md` §2, Cor C,
with `chDL2-opus.md` D1 (the threshold needs `n ≥ 2k`; here `n ≥ 3k + 6d + 20`).

* `Pn_ge_sq59`: `n² ≤ P` for `d ≥ 1`.
* `costG59_lt_twoPp`: `costG59 < 2P′` for `n ≥ 3k + 6d + 20`.
* `costG59_lt`: `costG59 < baselineF n d k ε` for every `ε` (indeed `< 2P′ ≤ baselineF`).
* `costG59_lt_oneSample`: `costG59 < 2P + C_f` (reading R2: one charged sample).

Proved here, with no `sorry`. Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part59

open BstLean.Part36 (DD)
open BstLean.Part41 (Pn)

lemma Pn_ge_sq59 (n d : ℕ) (hd : 1 ≤ d) : (n : ℝ) ^ 2 ≤ Pn n d := by
  have hc := Nat.choose_le_choose n (show n + 1 ≤ n + d by omega)
  rw [Nat.choose_symm_add (a := n) (b := 1), Nat.choose_one_right,
    Nat.choose_symm_add (a := n) (b := d)] at hc
  have hc' : (n : ℝ) ≤ ((n + d).choose d : ℝ) := by
    exact_mod_cast (show n ≤ (n + d).choose d by omega)
  unfold Pn
  rw [BstLean.Part36.DD_eq, pow_two]
  exact mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg n)

lemma choose_ge_one59 (n k : ℕ) : (1 : ℝ) ≤ ((n + k).choose k : ℝ) := by
  exact_mod_cast Nat.choose_pos (show k ≤ n + k by omega)

/-- `costG59 < 2P′` once `n ≥ 3k + 6d + 20`. -/
theorem costG59_lt_twoPp (n d k : ℕ) (hd : 1 ≤ d) (hn : 3 * k + 6 * d + 20 ≤ n) :
    costG59 n d k < 2 * Pp n d k := by
  have hP := Pn_ge_sq59 n d hd
  have hC := choose_ge_one59 n k
  have hlog : (Nat.log 2 n : ℝ) ≤ n := by exact_mod_cast Nat.log_le_self 2 n
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hn' : (3 * k + 6 * d + 20 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold costG59 Pp costF
  have h3 : 3 * (n : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ 3 * n * k :=
    mul_le_mul_of_nonneg_left hk1 (by positivity)
  nlinarith

/-- Reading R2 of the source (one sample costs `2P + C_f`): `costG59 < 2P + C_f` once
`n ≥ 3k + 6d + 20`. This is the harder reading (`2P + C_f ≤ 2P′`). -/
theorem costG59_lt_oneSample (n d k : ℕ) (hd : 1 ≤ d) (hn : 3 * k + 6 * d + 20 ≤ n) :
    costG59 n d k < 2 * Pn n d + costF n k := by
  have hP := Pn_ge_sq59 n d hd
  have hlog : (Nat.log 2 n : ℝ) ≤ n := by exact_mod_cast Nat.log_le_self 2 n
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hn' : (3 * k + 6 * d + 20 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold costG59 costF
  have h3 : 3 * (n : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ 3 * n * k :=
    mul_le_mul_of_nonneg_left hk1 (by positivity)
  nlinarith

/-- `2P′ ≤ baselineF`. -/
lemma twoPp_le_baselineF (n d k : ℕ) (ε : ℝ) : 2 * Pp n d k ≤ baselineF n d k ε :=
  le_max_left _ _

/-- **Cor C.** For every `ε`, from `n ≥ 3k + 6d + 20` on, `costG59 < baselineF n d k ε`. -/
theorem costG59_lt (d k : ℕ) (hd : 1 ≤ d) (ε : ℝ) :
    ∃ nc : ℕ, ∀ n : ℕ, nc ≤ n → costG59 n d k < baselineF n d k ε :=
  ⟨3 * k + 6 * d + 20, fun n hn =>
    (costG59_lt_twoPp n d k hd hn).trans_le (twoPp_le_baselineF n d k ε)⟩

end BstLean.Part59
