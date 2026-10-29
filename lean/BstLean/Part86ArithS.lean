import BstLean.Part86Arith

/-!
# Part 86, arithmetic, second pass: the threshold `N86s` with the constant `CLs d = 1.01 (d+1)!`

* `N86s_ge`, `N86s_33_le`, `N86s_33_ge`, `N86s_22_le`: values.
* `arith86s`: the numeric conditions of the assembly for `n ≥ N86s d k`.
* `cost86s`: the strict cost clause for `n ≥ N86s d k`, `n ≥ 40 B`.
-/

namespace BstLean.Part86

open BstLean.Part36 (DD)
open BstLean.Part41 (Mono Pn NN baseline)
open BstLean.Part56 (KRK costLine56)
open BstLean.Part80 (e80 K80_le)

/-- The threshold of the second pass: `71000 (2k+1)² (d+1)! 9^{dk}`. -/
def N86s (d k : ℕ) : ℕ := 71000 * (2 * k + 1) ^ 2 * (d + 1).factorial * 9 ^ (d * k)

/-- The constant of the slice feature operator bound, second pass: `1.01 (d+1)!`. -/
noncomputable def CLs (d : ℕ) : ℝ := 101 / 100 * ((d + 1).factorial : ℝ)

theorem N86s_ge (d k : ℕ) : 71000 ≤ N86s d k := by
  unfold N86s
  have h1 : 1 ≤ (2 * k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (d + 1).factorial := Nat.factorial_pos _
  have h3 : 1 ≤ 9 ^ (d * k) := Nat.one_le_pow _ _ (by norm_num)
  calc 71000 = 71000 * 1 * 1 * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2) h3

theorem N86s_33_le : N86s 3 3 ≤ 33 * 10 ^ 15 := by
  unfold N86s; norm_num [Nat.factorial]

theorem N86s_33_ge : 40 * 1200035 ≤ N86s 3 3 := by
  unfold N86s; norm_num [Nat.factorial]

theorem N86s_22_le : N86s 2 2 ≤ 7 * 10 ^ 10 := by
  unfold N86s; norm_num [Nat.factorial]

private lemma pow_dkS (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
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

private lemma fact_ge6 (d : ℕ) (hd : 2 ≤ d) : 6 ≤ (d + 1).factorial := by
  calc 6 = (3 : ℕ).factorial := by decide
    _ ≤ (d + 1).factorial := Nat.factorial_le (by omega)

private lemma N86s_geq (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    71000 * ((2 * k + 1) ^ 2 * 9 ^ (d * k)) ≤ N86s d k ∧ 71000 * (25 * 9 ^ (d * k)) ≤ N86s d k := by
  unfold N86s
  have hc := fact_ge6 d (by omega)
  have hq : 25 ≤ (2 * k + 1) ^ 2 := by nlinarith
  have h1 : 71000 * ((2 * k + 1) ^ 2 * 9 ^ (d * k)) ≤
      71000 * (2 * k + 1) ^ 2 * (d + 1).factorial * 9 ^ (d * k) := by
    calc 71000 * ((2 * k + 1) ^ 2 * 9 ^ (d * k))
        = 71000 * (2 * k + 1) ^ 2 * 1 * 9 ^ (d * k) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  refine ⟨h1, le_trans ?_ h1⟩
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq)

theorem arith86s (d k n : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hn : N86s d k ≤ n) :
    100 ≤ n ∧ 4 * k ^ 4 ≤ n ∧ d ≤ n ∧
    0 ≤ CLs d / ((n : ℝ) - 1) ∧
    CLs d / ((n : ℝ) - 1) * (8 * 9 ^ (d * k)) ≤ 1 / 2 ∧
    (9 : ℝ) ^ k * (CLs d / ((n : ℝ) - 1)) ≤ 8 * 9 ^ (d * k) ∧
    CLs d / ((n : ℝ) - 1) ≤ 1 / 10 ∧
    remezBound n k (n * (CLs d / ((n : ℝ) - 1)) + 2)
        (6 * n * (CLs d / ((n : ℝ) - 1)) * (8 * 9 ^ (d * k))) + 100 / (n : ℝ) ≤ 1 / 100 := by
  obtain ⟨h81, hk4, hd9, h9k, -⟩ := pow_dkS d k hk hkd
  have hge := ((N86s_geq d k hk hkd).2).trans hn
  have hn100 : 100 ≤ n := by omega
  refine ⟨hn100, by omega, by omega, ?_⟩
  set N : ℝ := (n : ℝ) with hNdef
  set c : ℝ := ((d + 1).factorial : ℝ) with hcdef
  set p : ℝ := (9 : ℝ) ^ (d * k) with hpdef
  set kr : ℝ := (k : ℝ) with hkr
  have hc6 : (6 : ℝ) ≤ c := by
    simp only [hcdef]; exact_mod_cast fact_ge6 d (by omega)
  have hp81 : (81 : ℝ) ≤ p := by simp only [hpdef]; exact_mod_cast h81
  have hk2 : (2 : ℝ) ≤ kr := by simp only [hkr]; exact_mod_cast hk
  have hNX : 71000 * ((2 * kr + 1) ^ 2 * c * p) ≤ N := by
    have : ((N86s d k : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr hn
    refine le_trans (le_of_eq ?_) this
    simp only [N86s, hcdef, hpdef, hkr]; push_cast; ring
  set q : ℝ := (2 * kr + 1) ^ 2 with hqdef
  have hq25 : (25 : ℝ) ≤ q := by simp only [hqdef]; nlinarith
  have hcp0 : 0 ≤ c * p := by nlinarith
  have hcp : c ≤ c * p / 81 := by nlinarith
  have hXqcp : c * p ≤ q * c * p / 25 := by
    have : 25 * (c * p) ≤ q * (c * p) := mul_le_mul_of_nonneg_right hq25 hcp0
    linarith
  have hqcp0 : 0 ≤ q * c * p := by nlinarith
  have hN0 : (0 : ℝ) < N := by
    have : (71000 : ℝ) * 0 ≤ 71000 * (q * c * p) := by nlinarith
    nlinarith
  have hN1 : (10000 : ℝ) ≤ N - 1 := by
    have : (10001 : ℕ) ≤ n := by omega
    have : (10001 : ℝ) ≤ N := by simp only [hNdef]; exact_mod_cast this
    linarith
  have hCL : CLs d = 101 / 100 * c := rfl
  rw [hCL]
  set L : ℝ := 101 / 100 * c / (N - 1) with hLdef
  have hL0 : 0 ≤ L := div_nonneg (by linarith) (by linarith)
  have hLmul : L * (N - 1) = 101 / 100 * c := by
    simp only [hLdef]; field_simp
  have hLc : L ≤ 101 / 100 * c / 10000 := by nlinarith
  have hNL : N * L ≤ 10102 / 10000 * c := by nlinarith
  have hL10 : L ≤ 1 / 10 := by
    have h : L * N ≤ 1 / 10 * N := by nlinarith
    exact le_of_mul_le_mul_right h hN0
  have h9 : (9 : ℝ) ^ k ≤ p := by simp only [hpdef]; exact_mod_cast h9k
  have hkq : (kr + 1) ^ 2 ≤ q := by simp only [hqdef]; nlinarith
  clear_value L q p c N kr
  refine ⟨hL0, ?_, ?_, hL10, ?_⟩
  · have h : L * (8 * p) * N ≤ 1 / 2 * N := by
      have : L * (8 * p) * N = (N * L) * (8 * p) := by ring
      rw [this]
      have : (N * L) * (8 * p) ≤ 10102 / 10000 * c * (8 * p) :=
        mul_le_mul_of_nonneg_right hNL (by linarith)
      nlinarith
    exact le_of_mul_le_mul_right h hN0
  · have : (9 : ℝ) ^ k * L ≤ p * (1 / 10) := mul_le_mul h9 hL10 hL0 (by linarith)
    linarith
  · unfold remezBound
    rw [← hkr, ← hNdef, ← hqdef]
    have hc1' : N * L + 2 ≤ 135 / 100 * c := by linarith
    have hc10 : 0 ≤ N * L + 2 := by nlinarith
    have hA : (kr + 1) ^ 2 * (N * L + 2) ≤ q * (135 / 100 * c) :=
      mul_le_mul hkq hc1' hc10 (by linarith)
    have hqc : q * c ≤ q * c * p / 81 := by
      have : 81 * (q * c) ≤ p * (q * c) := mul_le_mul_of_nonneg_right hp81 (by nlinarith)
      linarith
    have hB : 6 * N * L * (8 * p) ≤ 4849 / 100 * (c * p) := by
      have : (N * L) * p ≤ 10102 / 10000 * c * p := mul_le_mul_of_nonneg_right hNL (by linarith)
      linarith
    have hB' : q * (6 * N * L * (8 * p)) ≤ q * (4849 / 100 * (c * p)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have hX : 12150 ≤ q * c * p := by
      have h1 : 6 * 81 ≤ c * p := mul_le_mul hc6 hp81 (by norm_num) (by linarith)
      have h2 : 25 * (6 * 81) ≤ q * (c * p) := mul_le_mul hq25 h1 (by norm_num) (by linarith)
      linarith
    have e : ∀ A Bq : ℝ, 5 / 2 * A * 25 * (N * L + 2) / N +
        5 / 2 * q * 5 * Bq / N + 100 / N =
        (125 / 2 * (A * (N * L + 2)) + 25 / 2 * (q * Bq) + 100) / N := by
      intro A Bq; field_simp; ring
    rw [e, div_le_iff₀ hN0]
    linarith

private lemma card_monoS (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.multichoose n i) (d + 1)]
  rw [Nat.sum_range_multichoose, ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

private lemma add_two_le_powS (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

private lemma pow_le_fact_chooseS (n k : ℕ) : (n + 1) ^ k ≤ k.factorial * (n + k).choose k := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.pow_succ_le_ascFactorial (n + 1) k

theorem cost86s (d k n B : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hn : N86s d k ≤ n) (hB : 40 * B ≤ n)
    (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1))
    (hpg : (pgc : ℝ) ≤ costLine56 n d k) :
    (pmc : ℝ) + pgc < baseline n d (1 / 2) := by
  obtain ⟨h81, hk4, hd9, h9k, h2d⟩ := pow_dkS d k hk hkd
  obtain ⟨hgq, hge25⟩ := N86s_geq d k hk hkd
  have hge := hge25.trans hn
  set C : ℕ := (n + d).choose d with hC
  have hNN : NN n d = (C : ℝ) := by unfold NN; rw [card_monoS]
  have hPn : Pn n d = (n : ℝ) * C := by unfold Pn; rw [BstLean.Part36.DD_eq]
  have hCn : n + 1 ≤ C := BstLean.Part74.choose_ge74 n d (by omega)
  have hpow : (n + 1) ^ k ≤ k.factorial * C := by
    refine (pow_le_fact_chooseS n k).trans (Nat.mul_le_mul_left _ ?_)
    rw [hC, ← Nat.choose_symm_add (a := n) (b := k), ← Nat.choose_symm_add (a := n) (b := d)]
    exact Nat.choose_le_choose n (by omega)
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
    have a3 : k + 2 ≤ 2 ^ (d * k) := (add_two_le_powS k hk).trans (h2p _ _ (by nlinarith))
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
    calc 8 * ((k + 2) ^ 3 * (d + 1) ^ k * k.factorial)
        ≤ 8 * ((2 * k + 1) ^ 2 * 9 ^ (d * k)) :=
          Nat.mul_le_mul_left _ (a5.trans (Nat.mul_le_mul_left _ a6))
      _ ≤ 71000 * ((2 * k + 1) ^ 2 * 9 ^ (d * k)) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ n := hgq.trans hn
  have hd3 : 3 * (d + 1) ≤ n := by
    have : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
    omega
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

#print axioms BstLean.Part86.arith86s
#print axioms BstLean.Part86.cost86s
#print axioms BstLean.Part86.N86s_33_le
