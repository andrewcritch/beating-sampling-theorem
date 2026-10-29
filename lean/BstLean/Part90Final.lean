import BstLean.Part90Num
import BstLean.Part90Grad
import BstLean.Part90Mom
import BstLean.Part89Final

/-!
# Part 90, headline theorem: Theorem 1 (the line program) at `(d_M, d_f) = (3, 3)`, strict cost,
for every `n ≥ N90 = 1.5 · 10⁸`

* `oscR_inst`: the slice oscillation bound (`OscR`) from `sliceMom` and `instOsc`.
* `failHyp90`: the failure bound on the coefficient sphere for every `n ≥ N90`.
* `part90_line_33`: `∀ n, N90 ≤ n → Concl89 3 3 1200035 n`.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part90

open scoped ENNReal
open MeasureTheory
open BstLean.Part86 BstLean.Part89
open BstLean.Part36 (DD)
open BstLean.Part41 (Mono Pn NN baseline)
open BstLean.Part56 (KRK costLine56)
open BstLean.Part80 (e80 K80_le)

private lemma card_mono90 (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.multichoose n i) (d + 1)]
  rw [Nat.sum_range_multichoose, ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

private lemma pow_le_fact_choose90 (n k : ℕ) : (n + 1) ^ k ≤ k.factorial * (n + k).choose k := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.pow_succ_le_ascFactorial (n + 1) k

/-- The cost clause from the three size conditions (the proof of `cost89`). -/
private lemma costGen90 (d k n B : ℕ) (hd1 : 1 ≤ d) (hkd : k ≤ d)
    (hbig : 8 * ((k + 2) ^ 3 * (d + 1) ^ k * k.factorial) ≤ n)
    (hd3 : 3 * (d + 1) ≤ n) (h4000 : 4000 ≤ n) (hB : 40 * B ≤ n)
    (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1))
    (hpg : (pgc : ℝ) ≤ costLine56 n d k) :
    (pmc : ℝ) + pgc < baseline n d (1 / 2) := by
  set C : ℕ := (n + d).choose d with hC
  have hNN : NN n d = (C : ℝ) := by unfold NN; rw [card_mono90]
  have hPn : Pn n d = (n : ℝ) * C := by unfold Pn; rw [BstLean.Part36.DD_eq]
  have hCn : n + 1 ≤ C := BstLean.Part74.choose_ge74 n d hd1
  have hpow : (n + 1) ^ k ≤ k.factorial * C := by
    refine (pow_le_fact_choose90 n k).trans (Nat.mul_le_mul_left _ ?_)
    rw [hC, ← Nat.choose_symm_add (a := n) (b := k), ← Nat.choose_symm_add (a := n) (b := d)]
    exact Nat.choose_le_choose n (by omega)
  have hK := K80_le n
  have hbase : 91 / 100 * Pn n d / (1 / 2) ^ 2 ≤ baseline n d (1 / 2) := le_max_right _ _
  have hcl : (pgc : ℝ) ≤ 2 * Pn n d + ((d : ℝ) + 1) * NN n d +
      4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k := by
    refine hpg.trans (le_of_eq ?_); unfold costLine56; rfl
  rw [hPn] at hbase hcl
  rw [hNN] at hcl
  set N : ℝ := (n : ℝ)
  set Cr : ℝ := (C : ℝ)
  have hN0 : (4000 : ℝ) ≤ N := by
    show (4000 : ℝ) ≤ (n : ℝ)
    exact_mod_cast h4000
  have hCr : N + 1 ≤ Cr := by
    show (n : ℝ) + 1 ≤ (C : ℝ)
    exact_mod_cast hCn
  have hBr : 40 * (B : ℝ) ≤ N := by
    show 40 * (B : ℝ) ≤ (n : ℝ)
    exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hd3r : 3 * ((d : ℝ) + 1) ≤ N := by
    show 3 * ((d : ℝ) + 1) ≤ (n : ℝ)
    exact_mod_cast hd3
  have hT : 4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (N + 1) ^ k ≤ N * Cr / 2 := by
    have h1 : ((n : ℝ) + 1) ^ k ≤ (k.factorial : ℝ) * Cr := by
      show ((n : ℝ) + 1) ^ k ≤ (k.factorial : ℝ) * (C : ℝ)
      exact_mod_cast hpow
    have h2 : 8 * (((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (k.factorial : ℝ)) ≤ N := by
      show 8 * (((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (k.factorial : ℝ)) ≤ (n : ℝ)
      exact_mod_cast hbig
    have h0 : (0 : ℝ) ≤ ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k := by positivity
    have h3 : ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (N + 1) ^ k ≤
        ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((k.factorial : ℝ) * Cr) :=
      mul_le_mul_of_nonneg_left h1 h0
    have hCr0 : (0 : ℝ) ≤ Cr := by linarith
    have h4 : 8 * (((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (k.factorial : ℝ)) * Cr ≤ N * Cr :=
      mul_le_mul_of_nonneg_right h2 hCr0
    nlinarith
  have hD : ((d : ℝ) + 1) * Cr ≤ N * Cr / 3 := by
    have hCr0 : (0 : ℝ) ≤ Cr := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hd3r hCr0]
  have hM : (B : ℝ) * (N + (KRK 1 n e80 : ℝ) + 1) ≤ N * Cr / 2 := by
    have h1 : (B : ℝ) * (N + (KRK 1 n e80 : ℝ) + 1) ≤ B * (17 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    have h2 : (B : ℝ) * 34 ≤ Cr := by linarith
    have h3 : (B : ℝ) * 34 * N ≤ Cr * N := mul_le_mul_of_nonneg_right h2 (by linarith)
    nlinarith
  have hpos : 0 < N * Cr := by nlinarith
  have e : 91 / 100 * (N * Cr) / (1 / 2) ^ 2 = 364 / 100 * (N * Cr) := by norm_num; ring
  rw [e] at hbase
  linarith


set_option maxRecDepth 20000 in
/-- The slice oscillation bound for `n = m + 1 ≥ N90`, with `Mk = 6000`. -/
theorem oscR_inst (m : ℕ) (hn : N90 ≤ m + 1) :
    OscR m 6000 (4211 / 500) (3 / 5) (77 / 1000) (1141 / 1000) := by
  unfold N90 at hn
  have hNr : (150000000 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hmN : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hmN] at hNr
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hMom := sliceMom m (by omega)
  have hinv : 1 / (m : ℝ) ≤ 1 / 100000000 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs1 : (12247 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [show (12247 : ℝ) = Real.sqrt (12247 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hs0 : 0 < Real.sqrt (m : ℝ) := by linarith
  have h1 : 2 * (397 / 100 : ℝ) * Real.sqrt (9 / 8 * ((m : ℝ) + 1) / m) ≤ 4211 / 500 := by
    have hx : 9 / 8 * ((m : ℝ) + 1) / m ≤ (10607 / 10000 : ℝ) ^ 2 := by
      have e : 9 / 8 * ((m : ℝ) + 1) / m = 9 / 8 + 9 / 8 * (1 / (m : ℝ)) := by field_simp
      have h : (10607 / 10000 : ℝ) ^ 2 = 112508449 / 100000000 := by norm_num
      rw [e, h]; linarith
    have := (Real.sqrt_le_sqrt hx).trans (le_of_eq (Real.sqrt_sq (by norm_num)))
    linarith
  have h2 : 3 * (27 / 5 : ℝ) ^ 2 * Real.sqrt (103 / 100 * 6000 * (9 / 8) * ((m : ℝ) + 1)) / m ≤
      3 / 5 := by
    have hx : 103 / 100 * 6000 * (9 / 8) * ((m : ℝ) + 1) ≤ (685 / 100000 * (m : ℝ)) ^ 2 := by
      have hmm : (150000000 - 1 : ℝ) * (m : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hm0.le
      have e2 : (685 / 100000 * (m : ℝ)) ^ 2 = 469225 / 10000000000 * ((m : ℝ) * (m : ℝ)) := by
        ring
      rw [e2]
      linarith
    have := (Real.sqrt_le_sqrt hx).trans (le_of_eq (Real.sqrt_sq (by positivity)))
    rw [div_le_iff₀ hm0]
    linarith
  have h4 : 3 * (397 / 100 : ℝ) * Real.sqrt (103 / 100 * 6000) / Real.sqrt (m : ℝ) ≤
      77 / 1000 := by
    have hx : (103 / 100 * 6000 : ℝ) ≤ (7862 / 100 : ℝ) ^ 2 := by norm_num
    have := (Real.sqrt_le_sqrt hx).trans (le_of_eq (Real.sqrt_sq (by norm_num)))
    rw [div_le_iff₀ hs0]
    linarith
  have h3 : 9 * (19 / 50 : ℝ) ^ 2 * ((m : ℝ) + 1) / m ≤ (1141 / 1000 : ℝ) ^ 2 := by
    rw [div_le_iff₀ hm0]; norm_num; linarith
  intro t v hv E hE ℓ H hHs T hTs A c hA2 hA3 hT2 hT3
  exact instOsc m (by omega) (397 / 100) (27 / 5) (19 / 50) (by norm_num) (by norm_num)
    (by norm_num) hMom t v hv E hE ℓ H hHs T hTs 6000 (4211 / 500) (3 / 5) (77 / 1000)
    (1141 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    h1 h2 h4 h3 A c hA2 hA3 hT2 hT3

/-- The failure bound at `(3, 3)` for every `n ≥ N90`. -/
theorem failHyp90 : FailFrom 3 3 N90 := by
  intro n hn v hv t ht0 htn f0 T hT
  have h7 : 150000000 ≤ n := hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hN, hb⟩ := arith3 m hn
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  exact fail3_of m (1 / 20000) (1 / 200) (7 / 125) (1 / (600 * ((m + 1 : ℕ) : ℝ))) (1 / 500)
    (456 / 100) (2604 / 100) (4211 / 500) (3 / 5) (77 / 1000) (1141 / 1000) (81 / 50) 11 (1 / 10)
    (720 * (1 / Real.sqrt (m : ℝ))) 6000 hN (by omega) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (mul_pos (by norm_num) (one_div_pos.mpr (Real.sqrt_pos.mpr hm0))) (by norm_num)
    gradL4 (oscR_inst m hn) (by norm_num) hb v hv t ht0 htn f0 T hT

/-- The strict cost clause at `(3, 3)` for `n ≥ N90`. -/
theorem cost90 (n : ℕ) (hn : N90 ≤ n) (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ ((1200035 : ℕ) : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1))
    (hpg : (pgc : ℝ) ≤ costLine56 n 3 3) :
    (pmc : ℝ) + pgc < baseline n 3 (1 / 2) := by
  have h7 : 150000000 ≤ n := hn
  exact costGen90 3 3 n 1200035 (by norm_num) le_rfl (by norm_num [Nat.factorial]; omega)
    (by omega) (by omega) (by omega) pmc pgc hpm hpg

/-- **Theorem 1 (the line program) at `(d_M, d_f) = (3, 3)`**, `C = 1`, `ε = 1/2`, failure
`≤ 1/100`, strict cost, for every `n ≥ N90 = 150 000 000`. -/
theorem part90_line_33 : ∀ n : ℕ, N90 ≤ n → Concl89 3 3 1200035 n := by
  intro n hn
  have h7 : 150000000 ≤ n := hn
  exact line_of 3 3 1200035 N90 BstLean.Part74.progHyp33 failHyp90
    (fun n hn _ pmc pgc hpm hpg => cost90 n hn pmc pgc hpm hpg) n hn (by omega) (by omega)

/-- The same with the threshold written out. -/
theorem part90_line_33_num : ∀ n : ℕ, 150000000 ≤ n → Concl89 3 3 1200035 n :=
  fun n hn => part90_line_33 n hn

end BstLean.Part90

#print axioms BstLean.Part90.oscR_inst
#print axioms BstLean.Part90.failHyp90
#print axioms BstLean.Part90.part90_line_33
#print axioms BstLean.Part90.part90_line_33_num
