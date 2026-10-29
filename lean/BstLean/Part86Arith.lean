import BstLean.Part86Defs
import BstLean.Part80Cost
import BstLean.Part74FinalG

/-!
# Part 86, arithmetic: the threshold `N86` and the cost clause

* `CLn_pos`, `CLn_two`, `CLn_three`, `N86_33_le`, `N86_22_le`: values of the constants.
* `arith86`: for `n ≥ N86 d k` every numeric condition of the assembly holds and the failure bound
  is at most `1/100`.
* `cost86`: the strict cost clause for `n ≥ N86 d k`, `n ≥ 40 B`.
-/

namespace BstLean.Part86

open BstLean.Part36 (DD)
open BstLean.Part41 (Mono Pn NN baseline)
open BstLean.Part56 (KRK costLine56)
open BstLean.Part80 (e80 K80_le)

/-! ## A. Constants -/

theorem CLn_pos (d : ℕ) (hd : 1 ≤ d) : 1 ≤ CLn d := by
  unfold CLn
  have h1 : 1 ≤ d * (d + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  have h2 : 1 ≤ ∑ b ∈ Finset.Icc 1 d, (d.choose b) ^ 2 * (2 * b - 1).doubleFactorial := by
    have hmem : 1 ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨le_refl _, hd⟩
    have := Finset.single_le_sum (f := fun b => (d.choose b) ^ 2 * (2 * b - 1).doubleFactorial)
      (fun _ _ => Nat.zero_le _) hmem
    refine le_trans ?_ this
    simp only [Nat.choose_one_right]
    have : (2 * 1 - 1).doubleFactorial = 1 := by decide
    rw [this]
    nlinarith
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

theorem CLn_two : CLn 2 = 21 := by decide

theorem CLn_three : CLn 3 = 306 := by decide

theorem N86_33_le : N86 3 3 ≤ 5 * 10 ^ 17 := by
  unfold N86; rw [CLn_three]; norm_num

theorem N86_22_le : N86 2 2 ≤ 3 * 10 ^ 11 := by
  unfold N86; rw [CLn_two]; norm_num

/-! ## Natural-number facts about the threshold -/

private lemma pow_dk (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    81 ≤ 9 ^ (d * k) ∧ k ^ 4 ≤ 9 ^ (d * k) ∧ d ≤ 9 ^ (d * k) ∧ 9 ^ k ≤ 9 ^ (d * k) ∧
      2 ^ d ≤ 9 ^ (d * k) := by
  have h4 : 2 * k ≤ d * k := Nat.mul_le_mul_right k (by omega)
  have hkk : k ≤ d * k := by nlinarith
  have hdk : d ≤ d * k := by nlinarith
  have h9 : ∀ a b : ℕ, a ≤ b → 9 ^ a ≤ 9 ^ b := fun a b h => Nat.pow_le_pow_right (by norm_num) h
  have h29 : ∀ a : ℕ, 2 ^ a ≤ 9 ^ a := fun a => Nat.pow_le_pow_left (by norm_num) a
  refine ⟨?_, ?_, ?_, h9 _ _ hkk, (h29 d).trans (h9 _ _ hdk)⟩
  · calc 81 = 9 ^ 2 := by norm_num
      _ ≤ 9 ^ (d * k) := h9 _ _ (by nlinarith)
  · calc k ^ 4 ≤ (2 ^ k) ^ 4 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 4
      _ = 16 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ 81 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = 9 ^ (2 * k) := by rw [pow_mul]; norm_num
      _ ≤ 9 ^ (d * k) := h9 _ _ h4
  · exact (Nat.lt_two_pow_self).le.trans ((h29 d).trans (h9 _ _ hdk))

private lemma N86_ge (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    70000 * (25 * 9 ^ (d * k)) ≤ N86 d k := by
  unfold N86
  have hc := CLn_pos d (by omega)
  have hq : 25 ≤ (2 * k + 1) ^ 2 := by nlinarith
  calc 70000 * (25 * 9 ^ (d * k)) ≤ 70000 * ((2 * k + 1) ^ 2 * CLn d * 9 ^ (d * k)) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_right
        nlinarith
    _ = _ := by ring

/-! ## B. The numeric conditions -/

theorem arith86 (d k n : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hn : N86 d k ≤ n) :
    100 ≤ n ∧ 4 * k ^ 4 ≤ n ∧ d ≤ n ∧
    0 ≤ CL86 d / ((n : ℝ) - 1) ∧
    CL86 d / ((n : ℝ) - 1) * (8 * 9 ^ (d * k)) ≤ 1 / 2 ∧
    (9 : ℝ) ^ k * (CL86 d / ((n : ℝ) - 1)) ≤ 8 * 9 ^ (d * k) ∧
    CL86 d / ((n : ℝ) - 1) ≤ 1 / 10 ∧
    remezBound n k (n * (CL86 d / ((n : ℝ) - 1)) + 2)
        (6 * n * (CL86 d / ((n : ℝ) - 1)) * (8 * 9 ^ (d * k))) + 100 / (n : ℝ) ≤ 1 / 100 := by
  obtain ⟨h81, hk4, hd9, h9k, -⟩ := pow_dk d k hk hkd
  have hge := (N86_ge d k hk hkd).trans hn
  have hn100 : 100 ≤ n := by omega
  refine ⟨hn100, by omega, by omega, ?_⟩
  -- real quantities
  set N : ℝ := (n : ℝ) with hNdef
  set c : ℝ := CL86 d with hcdef
  set p : ℝ := (9 : ℝ) ^ (d * k) with hpdef
  set kr : ℝ := (k : ℝ) with hkr
  have hc1 : (1 : ℝ) ≤ c := by
    simp only [hcdef, CL86]; exact_mod_cast CLn_pos d (by omega)
  have hp81 : (81 : ℝ) ≤ p := by simp only [hpdef]; exact_mod_cast h81
  have hk2 : (2 : ℝ) ≤ kr := by simp only [hkr]; exact_mod_cast hk
  have hNX : 70000 * ((2 * kr + 1) ^ 2 * c * p) ≤ N := by
    have : ((N86 d k : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr hn
    refine le_trans (le_of_eq ?_) this
    simp only [N86, hcdef, CL86, hpdef, hkr]; push_cast; ring
  set q : ℝ := (2 * kr + 1) ^ 2 with hqdef
  have hq25 : (25 : ℝ) ≤ q := by simp only [hqdef]; nlinarith
  have hcp : 81 ≤ c * p := by nlinarith
  have hX : 2025 ≤ q * c * p := by
    have : 25 * 81 ≤ q * (c * p) := mul_le_mul hq25 hcp (by norm_num) (by linarith)
    nlinarith
  have hXqcp : c * p ≤ q * c * p / 25 := by
    have : 25 * (c * p) ≤ q * (c * p) := mul_le_mul_of_nonneg_right hq25 (by linarith)
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (100 : ℝ) ≤ N - 1 := by linarith
  set L : ℝ := c / (N - 1) with hLdef
  have hL0 : 0 ≤ L := div_nonneg (by linarith) (by linarith)
  have hLmul : L * (N - 1) = c := by
    simp only [hLdef]; field_simp
  have hLc : L ≤ c / 100 := by nlinarith
  have hNL : N * L ≤ 101 / 100 * c := by nlinarith
  have hpc : p ≤ c * p := by nlinarith
  have hL10 : L ≤ 1 / 10 := by
    have h : L * N ≤ 1 / 10 * N := by nlinarith
    exact le_of_mul_le_mul_right h hN0
  refine ⟨hL0, ?_, ?_, hL10, ?_⟩
  · have h : L * (8 * p) * N ≤ 1 / 2 * N := by
      have : L * (8 * p) * N = (N * L) * (8 * p) := by ring
      rw [this]
      have : (N * L) * (8 * p) ≤ 101 / 100 * c * (8 * p) :=
        mul_le_mul_of_nonneg_right hNL (by linarith)
      nlinarith
    exact le_of_mul_le_mul_right h hN0
  · have h9 : (9 : ℝ) ^ k ≤ p := by simp only [hpdef]; exact_mod_cast h9k
    have h90 : (0 : ℝ) ≤ 9 ^ k := by positivity
    have : (9 : ℝ) ^ k * L ≤ p * (1 / 10) := mul_le_mul h9 hL10 hL0 (by linarith)
    linarith
  · unfold remezBound
    have hkq : (kr + 1) ^ 2 ≤ q := by simp only [hqdef]; nlinarith
    have hc1' : N * L + 2 ≤ 301 / 100 * c := by linarith
    have hc10 : 0 ≤ N * L + 2 := by nlinarith
    have hA : (kr + 1) ^ 2 * (N * L + 2) ≤ q * (301 / 100 * c) :=
      mul_le_mul hkq hc1' hc10 (by linarith)
    have hqc : q * c ≤ q * c * p / 81 := by
      have : 81 * (q * c) ≤ p * (q * c) := mul_le_mul_of_nonneg_right hp81 (by nlinarith)
      linarith
    have hB : 6 * N * L * (8 * p) ≤ 4848 / 100 * (c * p) := by
      have : (N * L) * p ≤ 101 / 100 * c * p := mul_le_mul_of_nonneg_right hNL (by linarith)
      nlinarith
    have hB' : q * (6 * N * L * (8 * p)) ≤ q * (4848 / 100 * (c * p)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have e : 5 / 2 * (kr + 1) ^ 2 * 25 * (N * L + 2) / N +
        5 / 2 * (2 * kr + 1) ^ 2 * 5 * (6 * N * L * (8 * p)) / N + 100 / N =
        (125 / 2 * ((kr + 1) ^ 2 * (N * L + 2)) + 25 / 2 * (q * (6 * N * L * (8 * p))) + 100) / N := by
      simp only [hqdef]; field_simp; ring
    rw [e, div_le_iff₀ hN0]
    nlinarith

/-! ## C. The cost clause -/

private lemma card_mono86 (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.multichoose n i) (d + 1)]
  rw [Nat.sum_range_multichoose, ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

private lemma add_two_le_pow (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

private lemma pow_le_fact_choose (n k : ℕ) : (n + 1) ^ k ≤ k.factorial * (n + k).choose k := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.pow_succ_le_ascFactorial (n + 1) k

theorem cost86 (d k n B : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hn : N86 d k ≤ n) (hB : 40 * B ≤ n)
    (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1))
    (hpg : (pgc : ℝ) ≤ costLine56 n d k) :
    (pmc : ℝ) + pgc < baseline n d (1 / 2) := by
  obtain ⟨h81, hk4, hd9, h9k, h2d⟩ := pow_dk d k hk hkd
  have hge := (N86_ge d k hk hkd).trans hn
  -- the natural number of monomials
  set C : ℕ := (n + d).choose d with hC
  have hNN : NN n d = (C : ℝ) := by unfold NN; rw [card_mono86]
  have hPn : Pn n d = (n : ℝ) * C := by unfold Pn; rw [BstLean.Part36.DD_eq]
  have hCn : n + 1 ≤ C := BstLean.Part74.choose_ge74 n d (by omega)
  -- (n+1)^k ≤ k! C
  have hpow : (n + 1) ^ k ≤ k.factorial * C := by
    refine (pow_le_fact_choose n k).trans (Nat.mul_le_mul_left _ ?_)
    rw [hC, ← Nat.choose_symm_add (a := n) (b := k), ← Nat.choose_symm_add (a := n) (b := d)]
    exact Nat.choose_le_choose n (by omega)
  -- 8 (k+2)^3 (d+1)^k k! ≤ n
  have hbig : 8 * ((k + 2) ^ 3 * (d + 1) ^ k * k.factorial) ≤ n := by
    have hkk : k * k ≤ d * k := Nat.mul_le_mul_right k hkd
    have h2p : ∀ a b : ℕ, a ≤ b → 2 ^ a ≤ 2 ^ b := fun a b h => Nat.pow_le_pow_right (by norm_num) h
    have a1 : (d + 1) ^ k ≤ 2 ^ (d * k) := by
      calc (d + 1) ^ k ≤ (2 ^ d) ^ k := Nat.pow_le_pow_left Nat.lt_two_pow_self k
        _ = 2 ^ (d * k) := by rw [pow_mul]
    have a2 : k.factorial ≤ 2 ^ (d * k) := by
      calc k.factorial ≤ k ^ k := Nat.factorial_le_pow k
        _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le k
        _ = 2 ^ (k * k) := by rw [pow_mul]
        _ ≤ 2 ^ (d * k) := h2p _ _ hkk
    have a3 : k + 2 ≤ 2 ^ (d * k) := by
      have h1 : k + 2 ≤ 2 ^ k := add_two_le_pow k hk
      exact h1.trans (h2p _ _ (by nlinarith))
    have a4 : (k + 2) ^ 2 ≤ (2 * k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have a5 : (k + 2) ^ 3 * (d + 1) ^ k * k.factorial ≤
        (2 * k + 1) ^ 2 * (2 ^ (d * k) * 2 ^ (d * k) * 2 ^ (d * k)) := by
      calc (k + 2) ^ 3 * (d + 1) ^ k * k.factorial
          = (k + 2) ^ 2 * ((k + 2) * (d + 1) ^ k * k.factorial) := by ring
        _ ≤ (2 * k + 1) ^ 2 * (2 ^ (d * k) * 2 ^ (d * k) * 2 ^ (d * k)) :=
          Nat.mul_le_mul a4 (Nat.mul_le_mul (Nat.mul_le_mul a3 a1) a2)
    have a6 : 2 ^ (d * k) * 2 ^ (d * k) * 2 ^ (d * k) ≤ 9 ^ (d * k) := by
      calc 2 ^ (d * k) * 2 ^ (d * k) * 2 ^ (d * k) = 8 ^ (d * k) := by
            rw [← mul_pow, ← mul_pow]; norm_num
        _ ≤ 9 ^ (d * k) := Nat.pow_le_pow_left (by norm_num) _
    have hc := CLn_pos d (by omega)
    calc 8 * ((k + 2) ^ 3 * (d + 1) ^ k * k.factorial)
        ≤ 8 * ((2 * k + 1) ^ 2 * 9 ^ (d * k)) :=
          Nat.mul_le_mul_left _ (a5.trans (Nat.mul_le_mul_left _ a6))
      _ ≤ 70000 * ((2 * k + 1) ^ 2 * CLn d * 9 ^ (d * k)) := by
          have : (2 * k + 1) ^ 2 * 9 ^ (d * k) ≤ (2 * k + 1) ^ 2 * CLn d * 9 ^ (d * k) := by
            apply Nat.mul_le_mul_right; nlinarith
          omega
      _ = N86 d k := by unfold N86; ring
      _ ≤ n := hn
  have hd3 : 3 * (d + 1) ≤ n := by
    have : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
    omega
  -- reals
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
    have : 4000 ≤ n := by omega
    show (4000 : ℝ) ≤ (n : ℝ)
    exact_mod_cast this
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
  -- the trace term
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

end BstLean.Part86

#print axioms BstLean.Part86.arith86
#print axioms BstLean.Part86.cost86
#print axioms BstLean.Part86.N86_33_le
