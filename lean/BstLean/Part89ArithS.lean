import BstLean.Part89MainS
import BstLean.Part89QDefs2
import BstLean.Part89Arith

/-!
# Part 89, arithmetic of the second pass: the threshold `N89s d k = 110 (k+2) (d+1)! 9^{dk}`

* `N89s_ge`, `N89s_33_le`, `N89s_33_ge`, `N89s_22_le`: values.
* `arith89s`: the numeric conditions `NumS` and the bound `boundS + 100/n ≤ 1/100` for
  `n = m + 1 ≥ N89s d k`, with `a = 1/100`, `b = 1/7`, `β = 1/(2kn)`, `ξ = 1/(4k)`, `ϑ = 1/100`.
* `cost89s`: the strict cost clause for `n ≥ N89s d k`, `n ≥ 40 B`.
-/

namespace BstLean.Part89

open BstLean.Part86
open BstLean.Part36 (DD)
open BstLean.Part41 (Mono Pn NN baseline)
open BstLean.Part56 (KRK costLine56)
open BstLean.Part80 (e80 K80_le)

theorem N89s_ge (d k : ℕ) : 110 ≤ N89s d k := by
  unfold N89s
  have h1 : 1 ≤ k + 2 := by omega
  have h2 : 1 ≤ (d + 1).factorial := Nat.factorial_pos _
  have h3 : 1 ≤ 9 ^ (d * k) := Nat.one_le_pow _ _ (by norm_num)
  calc 110 = 110 * 1 * 1 * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2) h3

theorem N89s_33_le : N89s 3 3 ≤ 52 * 10 ^ 11 := by
  unfold N89s; norm_num [Nat.factorial]

theorem N89s_33_ge : 40 * 1200035 ≤ N89s 3 3 := by
  unfold N89s; norm_num [Nat.factorial]

theorem N89s_22_le : N89s 2 2 ≤ 2 * 10 ^ 7 := by
  unfold N89s; norm_num [Nat.factorial]

/-! ### Powers -/

private lemma sq_le_four_pow (j : ℕ) : (j + 2) ^ 2 ≤ 4 * 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have e : 4 * 4 ^ (j + 1) = 4 * (4 * 4 ^ j) := by ring
    have h : (j + 1 + 2) ^ 2 ≤ 4 * (j + 2) ^ 2 := by
      have e1 : (j + 1 + 2) ^ 2 = j ^ 2 + 6 * j + 9 := by ring
      have e2 : 4 * (j + 2) ^ 2 = 4 * j ^ 2 + 16 * j + 16 := by ring
      rw [e1, e2]; omega
    rw [e]; omega

private lemma powS (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    6561 ≤ 9 ^ (d * k) ∧ k ^ 4 ≤ 9 ^ (d * k) ∧ d ≤ 9 ^ (d * k) ∧ 9 ^ k ≤ 9 ^ (d * k) ∧
      2 ^ d ≤ 9 ^ (d * k) ∧ 6561 * k ^ 2 ≤ 4 * 9 ^ (d * k) ∧ 6561 * k ^ 4 ≤ 16 * 9 ^ (d * k) := by
  have h4 : 2 * k ≤ d * k := Nat.mul_le_mul_right k (by omega)
  have hkk : k ≤ d * k := by nlinarith
  have hdk : d ≤ d * k := by nlinarith
  have h9 : ∀ a b : ℕ, a ≤ b → 9 ^ a ≤ 9 ^ b := fun a b h => Nat.pow_le_pow_right (by norm_num) h
  have h29 : ∀ a : ℕ, 2 ^ a ≤ 9 ^ a := fun a => Nat.pow_le_pow_left (by norm_num) a
  have h6561 : 6561 ≤ 9 ^ (d * k) := by
    calc 6561 = 9 ^ 4 := by norm_num
      _ ≤ 9 ^ (d * k) := h9 _ _ (by nlinarith)
  have hk2 : 6561 * k ^ 2 ≤ 4 * 9 ^ (d * k) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have a := sq_le_four_pow j
    have b : 4 ^ j ≤ 81 ^ j := Nat.pow_le_pow_left (by norm_num) j
    have e : 9 ^ (2 * (j + 2)) = 6561 * 81 ^ j := by
      rw [pow_mul, pow_add]; norm_num; ring
    have := h9 _ _ h4
    rw [e] at this
    nlinarith
  have hk4 : 6561 * k ^ 4 ≤ 16 * 9 ^ (d * k) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have a := sq_le_four_pow j
    have a2 : ((j + 2) ^ 2) ^ 2 ≤ (4 * 4 ^ j) ^ 2 := Nat.pow_le_pow_left a 2
    have e0 : (4 * 4 ^ j) ^ 2 = 16 * 16 ^ j := by
      rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
    have b : 16 ^ j ≤ 81 ^ j := Nat.pow_le_pow_left (by norm_num) j
    have e : 9 ^ (2 * (j + 2)) = 6561 * 81 ^ j := by
      rw [pow_mul, pow_add]; norm_num; ring
    have := h9 _ _ h4
    rw [e] at this
    have e4 : (j + 2) ^ 4 = ((j + 2) ^ 2) ^ 2 := by ring
    rw [e4]
    nlinarith
  refine ⟨h6561, ?_, ?_, h9 _ _ hkk, (h29 d).trans (h9 _ _ hdk), hk2, hk4⟩
  · have : 0 < k ^ 4 := by positivity
    omega
  · exact (Nat.lt_two_pow_self).le.trans ((h29 d).trans (h9 _ _ hdk))

private lemma fact_ge6S (d : ℕ) (hd : 2 ≤ d) : 6 ≤ (d + 1).factorial := by
  calc 6 = (3 : ℕ).factorial := by decide
    _ ≤ (d + 1).factorial := Nat.factorial_le (by omega)

private lemma N89s_geq (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    2640 * 9 ^ (d * k) ≤ N89s d k := by
  unfold N89s
  have hc := fact_ge6S d (by omega)
  calc 2640 * 9 ^ (d * k) = 110 * 4 * 6 * 9 ^ (d * k) := by norm_num
    _ ≤ 110 * (k + 2) * (d + 1).factorial * 9 ^ (d * k) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hc)

/-! ### The window quantities -/

private lemma pw_le (x : ℝ) (hx : 0 ≤ x) (M : ℕ) (h : 101 * ((M : ℝ) * x) ≤ 1) :
    (1 + x) ^ M ≤ 1 + 101 / 100 * ((M : ℝ) * x) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    push_cast at h ⊢
    have h' : 101 * ((M : ℝ) * x) ≤ 1 := by nlinarith
    have h0 := ih h'
    rw [pow_succ]
    have h1 : (1 + x) ^ M * (1 + x) ≤ (1 + 101 / 100 * ((M : ℝ) * x)) * (1 + x) :=
      mul_le_mul_of_nonneg_right h0 (by linarith)
    nlinarith [mul_nonneg hx (sub_nonneg.mpr h')]

private lemma win (k : ℕ) (hk : 2 ≤ k) (t u L : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hkt : (k : ℝ) * t ≤ 5001 / 10000 * u) (hku : (k : ℝ) * u ≤ 1 / 2000)
    (hL0 : 0 ≤ L) :
    0 ≤ e1S k t ∧ e1S k t ≤ 11354 / 10000 * ((k : ℝ) * u) ∧ 0 ≤ e2S k t L ∧
      e2S k t L ≤ 11354 / 10000 * ((k : ℝ) * u) + 2001 / 1000 * L := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set x : ℝ := (k : ℝ) * t with hx
  set w : ℝ := (k : ℝ) * u with hw
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) ht
  have hw0 : 0 ≤ w := mul_nonneg (by linarith) hu
  have hkx : (k : ℝ) * x ≤ 5001 / 10000 * w := by
    have := mul_le_mul_of_nonneg_left hkt (by linarith : (0 : ℝ) ≤ k)
    rw [hw]; linarith
  have h4t : 4 * t ≤ 5001 / 10000 * w := by
    have h1 : 2 * t ≤ x := by
      rw [hx]; exact mul_le_mul_of_nonneg_right hk2 ht
    have h2 : 2 * x ≤ (k : ℝ) * x := mul_le_mul_of_nonneg_right hk2 hx0
    linarith
  have hA2 : (1 + x) ^ (2 * k) ≤ 1 + 101 / 100 * (2 * ((k : ℝ) * x)) := by
    have := pw_le x hx0 (2 * k) (by push_cast; linarith)
    push_cast at this; linarith
  have hAk : (1 + x) ^ k ≤ 1 + 101 / 100 * ((k : ℝ) * x) := pw_le x hx0 k (by linarith)
  have hA21 : 1 ≤ (1 + x) ^ (2 * k) := one_le_pow₀ (by linarith)
  have hAk1 : 1 ≤ (1 + x) ^ k := one_le_pow₀ (by linarith)
  unfold e2S e1S a1S tauS
  rw [← hx]
  set A2 : ℝ := (1 + x) ^ (2 * k)
  set Ak : ℝ := (1 + x) ^ k
  set τ : ℝ := t * Ak with hτ
  have hτ0 : 0 ≤ τ := mul_nonneg ht (by linarith)
  have hτ1 : τ ≤ 12507 / 100000 * w := by
    have : τ ≤ t * (10003 / 10000) := mul_le_mul_of_nonneg_left (by linarith) ht
    linarith
  have hττ : τ ^ 2 ≤ 1 / 10000 * τ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hτ0
  have hττ0 : 0 ≤ τ ^ 2 := sq_nonneg τ
  have he1 : A2 - 1 + τ + τ ^ 2 ≤ 11354 / 10000 * w := by linarith
  have he10 : 0 ≤ A2 - 1 + τ + τ ^ 2 := by linarith
  have hLe : L * (2 + (A2 - 1 + τ + τ ^ 2)) ≤ L * (2001 / 1000) :=
    mul_le_mul_of_nonneg_left (by linarith) hL0
  have hLe0 : 0 ≤ L * (2 + (A2 - 1 + τ + τ ^ 2)) := mul_nonneg hL0 (by linarith)
  have e : τ * (1 + τ) = τ + τ ^ 2 := by ring
  rw [e]
  exact ⟨he10, he1, by linarith, by linarith⟩

private lemma cVW_le (k : ℕ) (hk : 2 ≤ k) (t u L Lp : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hkt : (k : ℝ) * t ≤ 5001 / 10000 * u) (hku : (k : ℝ) * u ≤ 1 / 2000)
    (hL0 : 0 ≤ L) (hLp : 0 ≤ Lp) :
    cVW k t L (104 / 100 * Lp) (1 / 100) ≤
      105161 / 100000 * Lp + 13035 / 100 * ((k : ℝ) * u) ^ 2 + 405010 * L ^ 2 := by
  obtain ⟨h10, h1, h20, h2⟩ := win k hk t u L ht hu hkt hku hL0
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold cVW
  set w : ℝ := (k : ℝ) * u
  have hw0 : 0 ≤ w := mul_nonneg (by linarith) hu
  set e1 := e1S k t
  set e2 := e2S k t L
  have hsq1 : (1 + e1) ^ 2 ≤ 100115 / 100000 := by nlinarith
  have hsq2 : e2 ^ 2 ≤ (11354 / 10000 * w + 2001 / 1000 * L) ^ 2 :=
    pow_le_pow_left₀ h20 h2 2
  have hsq3 : (11354 / 10000 * w + 2001 / 1000 * L) ^ 2 ≤
      12905 / 10000 * w ^ 2 + 4010 * L ^ 2 := by
    nlinarith [sq_nonneg (11354 / 10000 * w - 1000 * (2001 / 1000 * L)), sq_nonneg w, sq_nonneg L]
  have hA : (1 + 1 / 100) * (104 / 100 * Lp) * (1 + e1) ^ 2 ≤
      (1 + 1 / 100) * (104 / 100 * Lp) * (100115 / 100000) :=
    mul_le_mul_of_nonneg_left hsq1 (by positivity)
  have e : (1 + 1 / (1 / 100) : ℝ) = 101 := by norm_num
  rw [e]
  nlinarith [sq_nonneg w, sq_nonneg L]

/-! ### The core real inequality -/

set_option maxHeartbeats 1600000 in
private lemma coreS (n k : ℕ) (hk : 2 ≤ k) (L p c NW : ℝ)
    (hc6 : 6 ≤ c) (hp : 6561 ≤ p) (hNX : 110 * (((k : ℝ) + 2) * c * p) ≤ (n : ℝ))
    (hk2p : 6561 * (k : ℝ) ^ 2 ≤ 4 * p) (hk4p : 6561 * (k : ℝ) ^ 4 ≤ 16 * p)
    (hLmul : L * ((n : ℝ) - 1) = 101 / 100 * c) (hNW : (n : ℝ) ^ 3 / 3 ≤ NW) :
    0 ≤ L ∧ L ≤ 1 / 1000000 ∧ L * p ≤ 1 / 100 ∧
    2 / (NW * (99 / 100 * (1 / (4 * (k : ℝ))) * (1 / (2 * (k : ℝ) * (n : ℝ)))) ^ 2) < 1 ∧
    0 ≤ semiBound89 n k NW ((n : ℝ) * L + 2)
        ((n : ℝ) * cVW k (tS n (1 / (2 * (k : ℝ) * (n : ℝ)))) L (104 / 100 * (L * p)) (1 / 100))
        L (1 / 100) (1 / 7) (1 / (2 * (k : ℝ) * (n : ℝ))) (1 / (4 * (k : ℝ))) ∧
    semiBound89 n k NW ((n : ℝ) * L + 2)
        ((n : ℝ) * cVW k (tS n (1 / (2 * (k : ℝ) * (n : ℝ)))) L (104 / 100 * (L * p)) (1 / 100))
        L (1 / 100) (1 / 7) (1 / (2 * (k : ℝ) * (n : ℝ))) (1 / (4 * (k : ℝ))) +
      100 / (n : ℝ) ≤ 1 / 100 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set kr : ℝ := (k : ℝ) with hkr
  set N : ℝ := (n : ℝ) with hNdef
  have hkc : 24 ≤ (kr + 2) * c := by
    have : (4 : ℝ) * 6 ≤ (kr + 2) * c := mul_le_mul (by linarith) hc6 (by norm_num) (by linarith)
    linarith
  have hkcp : 24 * p ≤ (kr + 2) * c * p := mul_le_mul_of_nonneg_right hkc (by linarith)
  have hNp : 2640 * p ≤ N := by linarith
  have hN7 : 17321040 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hL0 : 0 ≤ L := by
    have : 0 ≤ L * (N - 1) := by rw [hLmul]; linarith
    exact nonneg_of_mul_nonneg_left this hN1
  -- `L p (k+2) ≤ 0.00919`
  have hLpk : L * p * (kr + 2) ≤ 919 / 100000 := by
    have e : L * p * (kr + 2) * (N - 1) = L * (N - 1) * (p * (kr + 2)) := by ring
    have h : L * p * (kr + 2) * (N - 1) ≤ 919 / 100000 * (N - 1) := by
      rw [e, hLmul]; nlinarith
    exact le_of_mul_le_mul_right h hN1
  have hLp0 : 0 ≤ L * p := mul_nonneg hL0 (by linarith)
  have hLp4 : 4 * (L * p) ≤ L * p * (kr + 2) := by nlinarith
  have hLk0 : 0 ≤ L * (kr + 2) := mul_nonneg hL0 (by linarith)
  have hLk : L * (kr + 2) ≤ 1401 / 1000000000 := by
    have : 6561 * (L * (kr + 2)) ≤ p * (L * (kr + 2)) := mul_le_mul_of_nonneg_right hp hLk0
    nlinarith
  have hL6 : L ≤ 1 / 1000000 := by nlinarith
  have hLp100 : L * p ≤ 1 / 100 := by linarith
  have hNL : N * L ≤ 10101 / 10000 * c := by nlinarith
  refine ⟨hL0, hL6, hLp100, ?_⟩
  -- the square root
  set s : ℝ := Real.sqrt N with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hN0
  have hs : s * s = N := Real.mul_self_sqrt hN0.le
  set u : ℝ := 1 / s with hudef
  have hu0 : 0 < u := by positivity
  have hus : u * s = 1 := by rw [hudef]; field_simp
  have huN : u ^ 2 * N = 1 := by
    rw [← hs]; nlinarith
  set β : ℝ := 1 / (2 * kr * N) with hβdef
  have hβ0 : 0 < β := by positivity
  have hβN : β * (2 * kr * N) = 1 := by rw [hβdef]; field_simp
  have hβ4 : β ≤ 1 / 100000 := by
    rw [hβdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set ξ : ℝ := 1 / (4 * kr) with hξdef
  have hξ0 : 0 < ξ := by positivity
  have hξk : ξ * (4 * kr) = 1 := by rw [hξdef]; field_simp
  have hξ8 : ξ ≤ 1 / 8 := by
    rw [hξdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hξsq : ξ ^ 2 ≤ 1 / 64 := by nlinarith
  -- the window
  have ht0 : 0 ≤ tS n β := by
    unfold tS
    exact div_nonneg (mul_nonneg hβ0.le (Real.sqrt_nonneg _)) (by linarith)
  have hkt : kr * tS n β ≤ 5001 / 10000 * u := by
    unfold tS
    rw [← hNdef, ← hsdef]
    have e1 : kr * β * s = u / 2 := by
      have : kr * β * s * (2 * s) = 1 := by
        have : kr * β * s * (2 * s) = β * (2 * kr * (s * s)) := by ring
        rw [this, hs, hβN]
      have h2 : u / 2 * (2 * s) = 1 := by linarith
      have h3 : (0 : ℝ) < 2 * s := by linarith
      exact mul_right_cancel₀ h3.ne' (this.trans h2.symm)
    have e2 : kr * (β * s / (1 - β)) = u / 2 / (1 - β) := by
      rw [← e1]; ring
    rw [e2, div_le_iff₀ (by linarith)]
    nlinarith
  have hw2N : (kr * u) ^ 2 * N = kr ^ 2 := by
    have : (kr * u) ^ 2 * N = kr ^ 2 * (u ^ 2 * N) := by ring
    rw [this, huN, mul_one]
  have hw0 : 0 ≤ kr * u := mul_nonneg (by linarith) hu0.le
  have hw2 : (kr * u) ^ 2 ≤ 1 / 4000000 := by
    have h : (kr * u) ^ 2 * N ≤ 1 / 4000000 * N := by
      rw [hw2N]; linarith
    exact le_of_mul_le_mul_right h hN0
  have hku : kr * u ≤ 1 / 2000 := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  have hW := cVW_le k hk (tS n β) u L (L * p) ht0 hu0.le hkt hku hL0 hLp0
  have hW0 : 0 ≤ cVW k (tS n β) L (104 / 100 * (L * p)) (1 / 100) :=
    cVW_nonneg _ _ _ _ _ (by linarith) (by norm_num)
  set W : ℝ := cVW k (tS n β) L (104 / 100 * (L * p)) (1 / 100) with hWdef
  -- `ν`
  set q : ℝ := 99 / 100 * ξ * β with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q * (8 * kr ^ 2 * N) = 99 / 100 := by
    have : q * (8 * kr ^ 2 * N) = 99 / 100 * (ξ * (4 * kr)) * (β * (2 * kr * N)) := by
      rw [hqdef]; ring
    rw [this, hξk, hβN]; ring
  have hkr4 : 0 < kr ^ 4 := by positivity
  have hz : N ^ 3 / 3 * q ^ 2 * kr ^ 4 * 192 = 9801 / 10000 * N := by
    have : N ^ 3 / 3 * q ^ 2 * kr ^ 4 * 192 = N * (q * (8 * kr ^ 2 * N)) ^ 2 := by ring
    rw [this, hq]; ring
  have hzge : 334 ≤ N ^ 3 / 3 * q ^ 2 := by
    have h : 334 * kr ^ 4 ≤ N ^ 3 / 3 * q ^ 2 * kr ^ 4 := by nlinarith
    exact le_of_mul_le_mul_right h hkr4
  have hNWq : 334 ≤ NW * q ^ 2 :=
    hzge.trans (mul_le_mul_of_nonneg_right hNW (sq_nonneg q))
  have hν : 2 / (NW * q ^ 2) ≤ 6 / 1000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  refine ⟨by linarith, ?_⟩
  -- the two terms
  have hSE := SE_two_k_le k hk β hβ0.le (by linarith)
  have hSE0 : 0 ≤ BstLean.Part88.SE (2 * k) β ξ := by
    unfold BstLean.Part88.SE
    exact le_trans (le_trans zero_le_one (BstLean.Part88.SS_ge_one _ ξ)) (le_max_left _ _)
  rw [← hkr, ← hξdef] at hSE
  unfold semiBound89
  rw [← hkr, ← hNdef, ← hqdef]
  set SEv : ℝ := BstLean.Part88.SE (2 * k) β ξ with hSEdef
  set ν : ℝ := 2 / (NW * q ^ 2) with hνdef
  have hd1 : 73469 / 100000 * N ≤ (1 - 1 / 7 : ℝ) ^ 2 * (1 - L) ^ 2 * N := by
    have h1 : 1 - 2 * L ≤ (1 - L) ^ 2 := by nlinarith only [sq_nonneg L]
    have : (73469 : ℝ) / 100000 ≤ (1 - 1 / 7 : ℝ) ^ 2 * (1 - L) ^ 2 := by
      have h2 : (1 - 1 / 7 : ℝ) ^ 2 * (999998 / 1000000) ≤ (1 - 1 / 7 : ℝ) ^ 2 * (1 - L) ^ 2 :=
        mul_le_mul_of_nonneg_left (by linarith only [h1, hL6]) (by norm_num)
      norm_num at h2 ⊢; linarith only [h2]
    exact mul_le_mul_of_nonneg_right this hN0.le
  have hd2 : (97846 : ℝ) / 100000 ≤ (1 - ξ ^ 2) * (1 - ν) := by
    have : (63 / 64 : ℝ) * (994 / 1000) ≤ (1 - ξ ^ 2) * (1 - ν) :=
      mul_le_mul (by linarith only [hξsq]) (by linarith only [hν]) (by norm_num)
        (by linarith only [hξsq])
    norm_num at this ⊢; linarith only [this]
  have hX0 : 0 ≤ SEv * (N * W) := mul_nonneg hSE0 (mul_nonneg hN0.le hW0)
  set Wb : ℝ := 105161 / 100000 * (L * p) + 13035 / 100 * (kr * u) ^ 2 + 405010 * L ^ 2 with hWb
  have hWb0 : 0 ≤ Wb := hW0.trans hW
  have hXY : SEv * (N * W) ≤ (61 / 100 * kr + 111 / 100) * (N * Wb) :=
    mul_le_mul hSE (mul_le_mul_of_nonneg_left hW hN0.le) (mul_nonneg hN0.le hW0) (by linarith)
  have hY0 : 0 ≤ (61 / 100 * kr + 111 / 100) * (N * Wb) :=
    mul_nonneg (by linarith) (mul_nonneg hN0.le hWb0)
  have hT2 : SEv * (N * W) / ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * N) / ((1 - ξ ^ 2) * (1 - ν)) ≤
      13912 / 10000 * ((61 / 100 * kr + 111 / 100) * Wb) := by
    have h1 : SEv * (N * W) / ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * N) ≤
        (61 / 100 * kr + 111 / 100) * (N * Wb) / (73469 / 100000 * N) :=
      div_le_div₀ hY0 hXY (by positivity) hd1
    have h10 : 0 ≤ (61 / 100 * kr + 111 / 100) * (N * Wb) / (73469 / 100000 * N) :=
      div_nonneg hY0 (by positivity)
    have h2 : SEv * (N * W) / ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * N) / ((1 - ξ ^ 2) * (1 - ν)) ≤
        (61 / 100 * kr + 111 / 100) * (N * Wb) / (73469 / 100000 * N) / (97846 / 100000) :=
      div_le_div₀ h10 h1 (by norm_num) hd2
    refine h2.trans (le_of_eq_of_le
      (show _ = (100000 / 73469 * (100000 / 97846) : ℝ) * ((61 / 100 * kr + 111 / 100) * Wb) by
        field_simp) ?_)
    exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (by linarith) hWb0)
  have hT20 : 0 ≤ SEv * (N * W) / ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * N) /
      ((1 - ξ ^ 2) * (1 - ν)) :=
    div_nonneg (div_nonneg hX0 (by positivity)) (by linarith)
  have hc10 : 0 ≤ N * L + 2 := by linarith [mul_nonneg hN0.le hL0]
  have hT10 : 0 ≤ 5 / 2 * (kr + 1) ^ 2 * (N * L + 2) / (1 / 100 * N) := by positivity
  refine ⟨by linarith, ?_⟩
  -- first term
  have hT1 : 5 / 2 * (kr + 1) ^ 2 * (N * L + 2) / (1 / 100 * N) ≤ 10473 / 10000000 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (kr + 1) ^ 2 * (N * L + 2) ≤ 9 / 4 * kr ^ 2 * (13435 / 10000 * c) :=
      mul_le_mul (by nlinarith) (by linarith) hc10 (by positivity)
    have h2 : 6561 * kr ^ 2 * c ≤ 4 * p * c := mul_le_mul_of_nonneg_right hk2p (by linarith)
    have h3 : 4 * (c * p) ≤ (kr + 2) * c * p := by
      have : 4 * (c * p) ≤ (kr + 2) * (c * p) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) (by linarith))
      linarith only [this]
    have hcp0 : 0 ≤ c * p := mul_nonneg (by linarith) (by linarith)
    linarith only [h1, h2, h3, hNX, hcp0]
  have hf0 : 0 ≤ 61 / 100 * kr + 111 / 100 := by linarith
  have hf : 61 / 100 * kr + 111 / 100 ≤ 61 / 100 * (kr + 2) := by linarith
  have hT2a : (61 / 100 * kr + 111 / 100) * (L * p) ≤ 56059 / 10000000 := by
    have := mul_le_mul_of_nonneg_right hf hLp0
    linarith
  have hT2b : (61 / 100 * kr + 111 / 100) * (kr * u) ^ 2 ≤ 5635 / 10000000000 := by
    have h1 : (61 / 100 * kr + 111 / 100) * (kr * u) ^ 2 * N ≤ 5635 / 10000000000 * N := by
      have e : (61 / 100 * kr + 111 / 100) * (kr * u) ^ 2 * N =
          (61 / 100 * kr + 111 / 100) * kr ^ 2 := by rw [mul_assoc, hw2N]
      rw [e]
      have h2 : (61 / 100 * kr + 111 / 100) * kr ^ 2 ≤ 61 / 100 * (kr + 2) * kr ^ 2 :=
        mul_le_mul_of_nonneg_right hf (sq_nonneg kr)
      have h3 : (kr + 2) * (6561 * kr ^ 2) ≤ (kr + 2) * (4 * p) :=
        mul_le_mul_of_nonneg_left hk2p (by linarith)
      have h4 : 6 * ((kr + 2) * p) ≤ (kr + 2) * c * p := by
        have : (kr + 2) * p * 6 ≤ (kr + 2) * p * c :=
          mul_le_mul_of_nonneg_left hc6 (mul_nonneg (by linarith) (by linarith))
        linarith
      have hkp0 : 0 ≤ (kr + 2) * p := mul_nonneg (by linarith) (by linarith)
      linarith only [h2, h3, h4, hNX, hkp0]
    exact le_of_mul_le_mul_right h1 hN0
  have hT2c : (61 / 100 * kr + 111 / 100) * L ^ 2 ≤ 855 / 1000000000000000 := by
    have h1 : (61 / 100 * kr + 111 / 100) * L ≤ 61 / 100 * (kr + 2) * L :=
      mul_le_mul_of_nonneg_right hf hL0
    have h2 : (61 / 100 * kr + 111 / 100) * L * L ≤ 61 / 100 * (1401 / 1000000000) * (1 / 1000000) :=
      mul_le_mul (by linarith) hL6 hL0 (by norm_num)
    have e : (61 / 100 * kr + 111 / 100) * L ^ 2 = (61 / 100 * kr + 111 / 100) * L * L := by ring
    rw [e]; refine h2.trans (by norm_num)
  have hT3 : 100 / N ≤ 6 / 1000000 := by
    rw [div_le_iff₀ hN0]; linarith
  have eW : (61 / 100 * kr + 111 / 100) * Wb =
      105161 / 100000 * ((61 / 100 * kr + 111 / 100) * (L * p)) +
        13035 / 100 * ((61 / 100 * kr + 111 / 100) * (kr * u) ^ 2) +
        405010 * ((61 / 100 * kr + 111 / 100) * L ^ 2) := by
    rw [hWb]; ring
  rw [eW] at hT2
  linarith

/-! ### The numeric conditions -/

set_option maxHeartbeats 800000 in
theorem arith89s (d k m : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hn : N89s d k ≤ m + 1) :
    NumS m d k (1 / 100) (1 / 7) (1 / (2 * (k : ℝ) * ((m + 1 : ℕ) : ℝ))) (1 / (4 * (k : ℝ)))
      (1 / 100) ∧
    0 ≤ boundS (m + 1) d k (CLs d / (m : ℝ)) (1 / 100) (1 / 7)
        (1 / (2 * (k : ℝ) * ((m + 1 : ℕ) : ℝ))) (1 / (4 * (k : ℝ))) (1 / 100) ∧
    boundS (m + 1) d k (CLs d / (m : ℝ)) (1 / 100) (1 / 7)
        (1 / (2 * (k : ℝ) * ((m + 1 : ℕ) : ℝ))) (1 / (4 * (k : ℝ))) (1 / 100) +
      100 / ((m + 1 : ℕ) : ℝ) ≤ 1 / 100 := by
  obtain ⟨h6561, hk4, hd9, h9k, -, hk2p, hk4p⟩ := powS d k hk hkd
  have hge := (N89s_geq d k hk hkd).trans hn
  have h100 : 100 ≤ m + 1 := by omega
  have h5000 : 5000 ≤ m := by omega
  have h4k : 4 * k ^ 4 ≤ m + 1 := by omega
  have hdn : d ≤ m + 1 := by omega
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hc6 : (6 : ℝ) ≤ ((d + 1).factorial : ℝ) := by exact_mod_cast fact_ge6S d (by omega)
  have hp : (6561 : ℝ) ≤ (9 : ℝ) ^ (d * k) := by exact_mod_cast h6561
  have hNX : 110 * (((k : ℝ) + 2) * ((d + 1).factorial : ℝ) * (9 : ℝ) ^ (d * k)) ≤
      ((m + 1 : ℕ) : ℝ) := by
    have : ((N89s d k : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hn
    refine le_trans (le_of_eq ?_) this
    simp only [N89s]; push_cast; ring
  have hk2p' : 6561 * (k : ℝ) ^ 2 ≤ 4 * (9 : ℝ) ^ (d * k) := by exact_mod_cast hk2p
  have hk4p' : 6561 * (k : ℝ) ^ 4 ≤ 16 * (9 : ℝ) ^ (d * k) := by exact_mod_cast hk4p
  have hm : (m : ℝ) = ((m + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hLmul : CLs d / (m : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) = 101 / 100 * ((d + 1).factorial : ℝ) := by
    rw [← hm]; unfold CLs; field_simp
  have hNW := DWr_ge_cube (m + 1) d (by omega) hdn h100
  obtain ⟨hL0, hL6, hLp, hν, hb0, hb⟩ := coreS (m + 1) k hk (CLs d / (m : ℝ)) ((9 : ℝ) ^ (d * k))
    ((d + 1).factorial : ℝ) (DWr (m + 1) (JR (m + 1) d)) hc6 hp hNX hk2p' hk4p' hLmul hNW
  have hN0 : (100 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h100
  have hβ0 : 0 < 1 / (2 * (k : ℝ) * ((m + 1 : ℕ) : ℝ)) := by positivity
  have hβ4 : 1 / (2 * (k : ℝ) * ((m + 1 : ℕ) : ℝ)) ≤ 1 / 400 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hξ0 : 0 < 1 / (4 * (k : ℝ)) := by positivity
  have hξ8 : 1 / (4 * (k : ℝ)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨⟨h100, h5000, h4k, hdn, hLp, ?_, by linarith, by norm_num, by norm_num, by norm_num,
    by linarith, hβ0, by linarith, hξ0, by linarith, ?_, by norm_num, hν⟩, hb0, hb⟩
  · have h9 : (9 : ℝ) ^ k ≤ (9 : ℝ) ^ (d * k) := by exact_mod_cast h9k
    have : (9 : ℝ) ^ k * (CLs d / (m : ℝ)) ≤ (9 : ℝ) ^ (d * k) * (1 / 1000000) :=
      mul_le_mul h9 hL6 hL0 (by linarith)
    linarith
  · have : 1 / (4 * (k : ℝ)) * (1 / (2 * (k : ℝ) * ((m + 1 : ℕ) : ℝ))) ≤ 1 / 8 * (1 / 400) :=
      mul_le_mul hξ8 hβ4 hβ0.le (by norm_num)
    linarith

/-! ### The cost clause -/

private lemma card_monoS2 (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.multichoose n i) (d + 1)]
  rw [Nat.sum_range_multichoose, ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

private lemma add_two_le_powS2 (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

private lemma pow_le_fact_chooseS2 (n k : ℕ) : (n + 1) ^ k ≤ k.factorial * (n + k).choose k := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.pow_succ_le_ascFactorial (n + 1) k

theorem cost89s (d k n B : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hn : N89s d k ≤ n) (hB : 40 * B ≤ n)
    (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1))
    (hpg : (pgc : ℝ) ≤ costLine56 n d k) :
    (pmc : ℝ) + pgc < baseline n d (1 / 2) := by
  obtain ⟨h6561, hk4, hd9, h9k, h2d, -, -⟩ := powS d k hk hkd
  have hge := (N89s_geq d k hk hkd).trans hn
  set C : ℕ := (n + d).choose d with hC
  have hNN : NN n d = (C : ℝ) := by unfold NN; rw [card_monoS2]
  have hPn : Pn n d = (n : ℝ) * C := by unfold Pn; rw [BstLean.Part36.DD_eq]
  have hCn : n + 1 ≤ C := BstLean.Part74.choose_ge74 n d (by omega)
  have hpow : (n + 1) ^ k ≤ k.factorial * C := by
    refine (pow_le_fact_chooseS2 n k).trans (Nat.mul_le_mul_left _ ?_)
    rw [hC, ← Nat.choose_symm_add (a := n) (b := k), ← Nat.choose_symm_add (a := n) (b := d)]
    exact Nat.choose_le_choose n (by omega)
  have hbig : 8 * ((k + 2) ^ 3 * (d + 1) ^ k * k.factorial) ≤ n := by
    have hkk : k ≤ d * k := by nlinarith
    have h2p : ∀ a b : ℕ, a ≤ b → 2 ^ a ≤ 2 ^ b := fun a b h => Nat.pow_le_pow_right (by norm_num) h
    have a1 : (d + 1) ^ k ≤ 2 ^ (d * k) := by
      calc (d + 1) ^ k ≤ (2 ^ d) ^ k := Nat.pow_le_pow_left Nat.lt_two_pow_self k
        _ = 2 ^ (d * k) := by rw [pow_mul]
    have a2 : k.factorial ≤ (d + 1).factorial := Nat.factorial_le (by omega)
    have a3 : k + 2 ≤ 2 ^ (d * k) := (add_two_le_powS2 k hk).trans (h2p _ _ hkk)
    have a4 : (k + 2) ^ 2 ≤ 2 ^ (d * k) * 2 ^ (d * k) := by
      rw [sq]; exact Nat.mul_le_mul a3 a3
    have a6 : 2 ^ (d * k) * 2 ^ (d * k) * 2 ^ (d * k) ≤ 9 ^ (d * k) := by
      calc 2 ^ (d * k) * 2 ^ (d * k) * 2 ^ (d * k) = 8 ^ (d * k) := by
            rw [← mul_pow, ← mul_pow]; norm_num
        _ ≤ 9 ^ (d * k) := Nat.pow_le_pow_left (by norm_num) _
    have a5 : (k + 2) ^ 2 * (d + 1) ^ k ≤ 9 ^ (d * k) :=
      (Nat.mul_le_mul a4 a1).trans a6
    calc 8 * ((k + 2) ^ 3 * (d + 1) ^ k * k.factorial)
        = 8 * ((k + 2) * k.factorial * ((k + 2) ^ 2 * (d + 1) ^ k)) := by ring
      _ ≤ 8 * ((k + 2) * (d + 1).factorial * 9 ^ (d * k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ a2) a5)
      _ = 8 * (k + 2) * (d + 1).factorial * 9 ^ (d * k) := by ring
      _ ≤ 110 * (k + 2) * (d + 1).factorial * 9 ^ (d * k) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
      _ ≤ n := hn
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

end BstLean.Part89

#print axioms BstLean.Part89.arith89s
#print axioms BstLean.Part89.cost89s
#print axioms BstLean.Part89.N89s_ge
#print axioms BstLean.Part89.N89s_33_le
#print axioms BstLean.Part89.N89s_33_ge
#print axioms BstLean.Part89.N89s_22_le
