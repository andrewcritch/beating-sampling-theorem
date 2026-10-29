import BstLean.Part89MainS
import BstLean.Part89ArithS
import BstLean.Part89QMain
import BstLean.Part89ArithQ

/-!
# Part 89, headline theorems: Theorem 1 (the line program), strict cost, sharper thresholds

* `part89_lineS_gen`: every `2 ≤ d_f = k ≤ d = d_M`, `n ≥ N89s d k = 110 (k+2) (d+1)! 9^{dk}`.
* `part89_lineS_33`, `part89_lineS_33_num`: `(3,3)` from `N89s 3 3 ≤ 5.2 · 10¹²`.
* `part89_line_q`: `d_f = 2`, every `d_M = d ≥ 2`, `n ≥ NQ d = 110000 (d+1)² (d+1)!`
  (no factor `9^{dk}`; the variance bound is averaged over the anchors).
`Concl89 d k B n` (`Part89Main.lean`) is the conclusion of `Part86.part86_lineS_gen` in dimension
`n` with the constant `B` of the moment program.
-/

namespace BstLean.Part89

open scoped ENNReal
open MeasureTheory
open BstLean.Part86

/-- The failure bound for every `n ≥ N89s d k`. -/
theorem failHyp89s (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) : FailFrom d k (N89s d k) := by
  intro n hn v hv t ht0 htn f0 T hT
  have h7 := N89s_ge d k
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hN, hb0, hb⟩ := arith89s d k m hk hkd hn
  exact failS_of m d k hk (by omega) _ _ _ _ _ hN hb hb0 v hv t ht0 htn f0 T hT

/-- The failure bound at `d_f = 2` for every `n ≥ NQ d`. -/
theorem failHypQ (d : ℕ) (hd : 2 ≤ d) : FailFrom d 2 (NQ d) := by
  intro n hn v hv t ht0 htn f0 T hT
  have h7 := NQ_ge d
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hN, hb⟩ := arithQ d m hd hn
  exact failQ_of m d hd _ _ _ _ _ _ _ _ hN hb v hv t ht0 htn f0 T hT

/-- **Theorem 1 at every degree pair `2 ≤ k = d_f ≤ d = d_M`**, `C = 1`, `ε = 1/2`, failure
`≤ 1/100`, strict cost, for every `n ≥ N89s d k = 110 (k+2) (d+1)! 9^{dk}` with `n ≥ 40 B`
(`B` the constant of the moment program of Part 74). -/
theorem part89_lineS_gen (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    ∃ B : ℕ, ∀ n : ℕ, N89s d k ≤ n → 40 * B ≤ n → Concl89 d k B n := by
  obtain ⟨B, hB⟩ := BstLean.Part74.momProgGen74 k d
  refine ⟨B, fun n hn hnB => ?_⟩
  have h7 := N89s_ge d k
  exact line_of d k B (N89s d k) hB (failHyp89s d k hk hkd)
    (fun n hn hB pmc pgc hpm hpg => cost89s d k n B hk hkd hn hB pmc pgc hpm hpg) n hn hnB
    (by omega)

/-- **Theorem 1 at `(d_M, d_f) = (3, 3)`** for every `n ≥ N89s 3 3 = 110 · 5 · 24 · 9⁹`. -/
theorem part89_lineS_33 : ∀ n : ℕ, N89s 3 3 ≤ n → Concl89 3 3 1200035 n := by
  intro n hn
  have h7 := N89s_ge 3 3
  exact line_of 3 3 1200035 (N89s 3 3) BstLean.Part74.progHyp33
    (failHyp89s 3 3 (by norm_num) le_rfl)
    (fun n hn hB pmc pgc hpm hpg =>
      cost89s 3 3 n 1200035 (by norm_num) le_rfl hn hB pmc pgc hpm hpg) n hn
    (le_trans N89s_33_ge hn) (by omega)

/-- **Theorem 1 at `(3, 3)` for every `n ≥ 5.2 · 10¹²`.** -/
theorem part89_lineS_33_num : ∀ n : ℕ, 52 * 10 ^ 11 ≤ n → Concl89 3 3 1200035 n :=
  fun n hn => part89_lineS_33 n (le_trans N89s_33_le hn)

/-- **Theorem 1 at `d_f = 2`, every `d_M = d ≥ 2`**, `C = 1`, `ε = 1/2`, failure `≤ 1/100`, strict
cost, for every `n ≥ NQ d = 110000 (d+1)² (d+1)!` with `n ≥ 40 B`. -/
theorem part89_line_q (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : ℕ, ∀ n : ℕ, NQ d ≤ n → 40 * B ≤ n → Concl89 d 2 B n := by
  obtain ⟨B, hB⟩ := BstLean.Part74.momProgGen74 2 d
  refine ⟨B, fun n hn hnB => ?_⟩
  have h7 := NQ_ge d
  exact line_of d 2 B (NQ d) hB (failHypQ d hd)
    (fun n hn hB pmc pgc hpm hpg => costQ d n B hd hn hB pmc pgc hpm hpg) n hn hnB
    (by omega)

end BstLean.Part89

#print axioms BstLean.Part89.part89_lineS_gen
#print axioms BstLean.Part89.part89_lineS_33
#print axioms BstLean.Part89.part89_lineS_33_num
#print axioms BstLean.Part89.part89_line_q
