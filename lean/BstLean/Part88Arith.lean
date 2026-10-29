import BstLean.Part88Core
import BstLean.Part88Trig
import BstLean.Part88Gauss
import BstLean.Part88Even

/-!
# Part 88: the arithmetic of the threshold

Fixed choices: window `w = 31/20`, moment order `J = 12k + 6`, `B = 3 + 70 J / n`,
`β = 1/(2kn)` (in the variable `lam²`), `ξ = 1/(4k)`. Free parameters: `η` (an upper bound for `2 k τ`), `θ`, `ε`, `κ`.
Hypotheses on `n`: `n ≥ 90000`, `n ≥ 200 d`, `(217/25) k² ≤ η √n`.

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part88

open BstLean.Part81 (eD)
open BstLean.Part84

/-- `B = 3 + 70 (12k+6)/n`. -/
noncomputable def BJ (n k : ℕ) : ℝ := 3 + 70 * ((12 * k + 6 : ℕ) : ℝ) / n

/-- The value of `τ`. -/
noncomputable def tau88 (n d k : ℕ) : ℝ := tauF n d k (31 / 20) (BJ n k)

noncomputable def beta88 (n k : ℕ) : ℝ := 1 / (2 * (k : ℝ) * n)

noncomputable def xi88 (k : ℕ) : ℝ := 1 / (4 * (k : ℝ))

/-! ## The explicit bounds -/

noncomputable def C1b (η : ℝ) : ℝ := 488 / 25 / (1 - η)

/-- The constant of `Var_W X` with the chaos split:
`KX = CF · min(27·3^k, 9^k)/e_d + 768 · 9^k/n`, `CF = 101/100`. -/
noncomputable def KX88 (n d k : ℕ) : ℝ :=
  101 / 100 * min (27 * (3 : ℝ) ^ k) ((9 : ℝ) ^ k) / eD d + 768 * (9 : ℝ) ^ k / n

/-- The explicit bound for `KX88`. -/
noncomputable def KXb (k : ℕ) (η : ℝ) : ℝ :=
  101 / 150 * min (27 * (3 : ℝ) ^ k) ((9 : ℝ) ^ k) + 51 / 5 * η ^ 2 * (9 : ℝ) ^ k / (k : ℝ) ^ 4

noncomputable def CVb (k : ℕ) (η ϑ : ℝ) : ℝ :=
  ((1 + ϑ) * KXb k η * (1 + η ^ 2 / 4) ^ 2 +
    (1 + 1 / ϑ) * (51 / 10) * η ^ 2 / (k : ℝ) ^ 4 * (9 : ℝ) ^ k) / (1 - η) ^ 2

noncomputable def Eb (η : ℝ) : ℝ := η + 3 / 10 * η ^ 2

noncomputable def rhob (k : ℕ) (η : ℝ) : ℝ :=
  (501 / 500 / (1 - η / 8) + 9 * η / (2 * (k : ℝ) ^ 3)) / (1 - η)

/-- The off-centre term of the Christoffel constants at `ξ = 1/(4k)`. -/
noncomputable def penS (k : ℕ) : ℝ :=
  5 / 384 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3)) / (k : ℝ) ^ 2

/-- The explicit bound for `n · pSE`. -/
noncomputable def PSb (k : ℕ) (η ϑ θ ε κ : ℝ) : ℝ :=
  (60001 / 60000 * ((k : ℝ) / 4 + 1 + penS k) * C1b η / (ε ^ 2 * κ) +
    60001 / 60000 * ((k : ℝ) / 2 + 1 + penS k) *
      ((1 + θ) * CVb k η ϑ + (1 + 1 / θ) * ((k : ℝ) ^ 2 * rhob k η ^ 2)) /
      (1 - Eb η - κ) ^ 2) /
    ((1 - 1 / (16 * (k : ℝ) ^ 2)) * (1 - 7 / 2 * η ^ 2))

/-! ## Basic consequences of the hypotheses -/

structure Hyp88 (n d k : ℕ) (η : ℝ) : Prop where
  hk : 1 ≤ k
  hd : 2 ≤ d
  hn : 90000 ≤ n
  hnd : 200 * d ≤ n
  hη0 : 0 < η
  hη : η ≤ 1 / 10
  hηn : 217 / 25 * (k : ℝ) ^ 2 ≤ η * Real.sqrt n

namespace Hyp88

variable {n d k : ℕ} {η : ℝ}

theorem k1 (h : Hyp88 n d k η) : (1 : ℝ) ≤ k := by exact_mod_cast h.hk

theorem n9 (h : Hyp88 n d k η) : (90000 : ℝ) ≤ n := by exact_mod_cast h.hn

theorem s300 (h : Hyp88 n d k η) : (300 : ℝ) ≤ Real.sqrt n := by
  apply Real.le_sqrt_of_sq_le
  have := h.n9; linarith

theorem ssq (_h : Hyp88 n d k η) : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)

/-- `(217/25) k² ≤ η √n` in the form `k²/√n ≤ (25/217) η`. -/
theorem ks (h : Hyp88 n d k η) : (k : ℝ) ^ 2 / Real.sqrt n ≤ 25 / 217 * η := by
  have hs := h.s300
  rw [div_le_iff₀ (by linarith)]
  have := h.hηn
  linarith

/-- `k⁴/n ≤ (25/217)² η²`. -/
theorem kn (h : Hyp88 n d k η) : (k : ℝ) ^ 4 / n ≤ (25 / 217) ^ 2 * η ^ 2 := by
  have h1 := h.ks
  have h0 : 0 ≤ (k : ℝ) ^ 2 / Real.sqrt n := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  have e : ((k : ℝ) ^ 2 / Real.sqrt n) ^ 2 = (k : ℝ) ^ 4 / n := by
    rw [div_pow, h.ssq]; ring
  rw [e] at h2
  calc (k : ℝ) ^ 4 / n ≤ (25 / 217 * η) ^ 2 := h2
    _ = (25 / 217) ^ 2 * η ^ 2 := by ring

/-- `1/n ≤ (25/217)² η²`. -/
theorem inv_n (h : Hyp88 n d k η) : 1 / (n : ℝ) ≤ (25 / 217) ^ 2 * η ^ 2 := by
  have hk := h.k1
  have hn := h.n9
  have h4 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk
  refine le_trans ?_ h.kn
  exact div_le_div_of_nonneg_right h4 (by linarith)

/-- `7534 k⁴ ≤ n`. -/
theorem n_k4 (h : Hyp88 n d k η) : 7534 * (k : ℝ) ^ 4 ≤ n := by
  have h1 := h.kn
  have hn := h.n9
  have hη := h.hη
  have hη0 := h.hη0
  have h2 : (25 / 217 : ℝ) ^ 2 * η ^ 2 ≤ 1 / 7534 := by nlinarith
  have h3 := h1.trans h2
  rw [div_le_iff₀ (by linarith)] at h3
  linarith

/-- `50400 k ≤ n`. -/
theorem n_k (h : Hyp88 n d k η) : 50400 * (k : ℝ) ≤ n := by
  have hn := h.n9
  have h4 := h.n_k4
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have : k = 1 := by have := h.hk; omega
    subst this; simp only [Nat.cast_one, mul_one]; linarith
  · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : (8 : ℝ) ≤ (k : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk2 3
      linarith
    have : (k : ℝ) ^ 4 = (k : ℝ) ^ 3 * k := by ring
    nlinarith

theorem momCond (h : Hyp88 n d k η) : 11 * (12 * k + 6) ^ 2 ≤ n := by
  have h4 := h.n_k
  have hk := h.k1
  have h9 := h.n9
  have h44 := h.n_k4
  have hk4 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
    have : (k : ℝ) ^ 4 = (k : ℝ) ^ 2 * (k : ℝ) ^ 2 := by ring
    nlinarith [sq_nonneg ((k : ℝ)), one_le_pow₀ hk (n := 2)]
  have : (11 * (12 * (k : ℝ) + 6) ^ 2) ≤ n := by nlinarith
  exact_mod_cast this

theorem BJ_bounds (h : Hyp88 n d k η) : 3 ≤ BJ n k ∧ BJ n k ≤ 121 / 40 := by
  have hn := h.n9
  have h4 := h.n_k
  have hk := h.k1
  unfold BJ
  have hn0 : (0 : ℝ) < n := by linarith
  constructor
  · have : 0 ≤ 70 * ((12 * k + 6 : ℕ) : ℝ) / n := by positivity
    linarith
  · have : 70 * ((12 * k + 6 : ℕ) : ℝ) / n ≤ 1 / 40 := by
      rw [div_le_iff₀ hn0]; push_cast; nlinarith
    linarith

end Hyp88

/-! ## The value of `τ` -/

namespace Hyp88

variable {n d k : ℕ} {η : ℝ}

/-- `τ ≤ (217/50) k / √n`. -/
theorem tau_le (h : Hyp88 n d k η) :
    0 ≤ tau88 n d k ∧ tau88 n d k ≤ 217 / 50 * k / Real.sqrt n := by
  have hn := h.n9
  have hs := h.s300
  have hk := h.k1
  obtain ⟨hB3, hB⟩ := h.BJ_bounds
  have he : 3 / 2 ≤ eD d := BstLean.Part81.three_halves_le_eD d h.hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt n := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdn : (d : ℝ) / (2 * n) ≤ 1 / 400 := by
    rw [div_le_iff₀ (by linarith)]
    have : (200 * (d : ℝ)) ≤ n := by exact_mod_cast h.hnd
    linarith
  have hwn : (31 / 20 : ℝ) / n ≤ 31 / 1800000 := by
    rw [div_le_iff₀ hn0]; linarith
  have hwn0 : (0 : ℝ) ≤ (31 / 20 : ℝ) / n := by positivity
  have hie : 1 / eD d ≤ 2 / 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hie0 : 0 ≤ 1 / eD d := by
    have : (0 : ℝ) < eD d := by linarith
    positivity
  have his : 1 / Real.sqrt n ≤ 1 / 300 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]; linarith
  have his0 : 0 ≤ 1 / Real.sqrt n := by positivity
  have hB0 : (0 : ℝ) ≤ BJ n k := by linarith
  have hBs : BJ n k / (4 * Real.sqrt n) ≤ 121 / 48000 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hBs0 : 0 ≤ BJ n k / (4 * Real.sqrt n) := by positivity
  have hdB : (d : ℝ) / (2 * n) * BJ n k ≤ 1 / 400 * (121 / 40) :=
    mul_le_mul hdn hB hB0 (by norm_num)
  have hdB0 : 0 ≤ (d : ℝ) / (2 * n) * BJ n k := by positivity
  set X : ℝ := (1 + (31 / 20 : ℝ) / n) * (1 / eD d) *
      (2719 / 2000 * BJ n k * (1 + 1 / Real.sqrt n + BJ n k / (4 * Real.sqrt n)) *
        (1 + (d : ℝ) / (2 * n) * BJ n k)) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hXle : X ≤ 2779 / 1000 := by
    have h1 : (1 + (31 / 20 : ℝ) / n) * (1 / eD d) ≤ (1 + 31 / 1800000) * (2 / 3) :=
      mul_le_mul (by linarith) hie hie0 (by norm_num)
    have h2 : 2719 / 2000 * BJ n k * (1 + 1 / Real.sqrt n + BJ n k / (4 * Real.sqrt n)) ≤
        2719 / 2000 * (121 / 40) * (1 + 1 / 300 + 121 / 48000) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    have h3 : 2719 / 2000 * BJ n k * (1 + 1 / Real.sqrt n + BJ n k / (4 * Real.sqrt n)) *
        (1 + (d : ℝ) / (2 * n) * BJ n k) ≤
        2719 / 2000 * (121 / 40) * (1 + 1 / 300 + 121 / 48000) * (1 + 1 / 400 * (121 / 40)) :=
      mul_le_mul h2 (by linarith) (by positivity) (by norm_num)
    have h4 := mul_le_mul h1 h3 (by positivity) (by norm_num)
    rw [hX]
    refine h4.trans ?_
    norm_num
  have hden : (0 : ℝ) < 1 - (31 / 20 : ℝ) / n := by linarith
  have etau : tau88 n d k =
      k * (31 / 20 + X) / (Real.sqrt n * (1 - (31 / 20 : ℝ) / n)) := by
    unfold tau88 tauF; rw [hX]
  have hk0 : (0 : ℝ) ≤ k := by linarith
  rw [etau]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) hs0]
    have h5 : (31 / 20 + X) ≤ 217 / 50 * (1 - (31 / 20 : ℝ) / n) := by linarith
    calc (k : ℝ) * (31 / 20 + X) * Real.sqrt n
        ≤ k * (217 / 50 * (1 - (31 / 20 : ℝ) / n)) * Real.sqrt n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hk0) hs0.le
      _ = 217 / 50 * k * (Real.sqrt n * (1 - (31 / 20 : ℝ) / n)) := by ring

/-- `2 k τ ≤ η`. -/
theorem tau_eta (h : Hyp88 n d k η) : 2 * (k : ℝ) * tau88 n d k ≤ η := by
  have h1 := h.tau_le.2
  have h2 := h.ks
  have hk := h.k1
  have e : 2 * (k : ℝ) * (217 / 50 * k / Real.sqrt n) = 217 / 25 * ((k : ℝ) ^ 2 / Real.sqrt n) := by
    ring
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * (k : ℝ))
  rw [e] at this
  linarith

/-- `n (τ/k)² ≤ 471/25`. -/
theorem tau_sq (h : Hyp88 n d k η) : (n : ℝ) * (tau88 n d k / k) ^ 2 ≤ 471 / 25 := by
  obtain ⟨h0, h1⟩ := h.tau_le
  have hk := h.k1
  have hs := h.s300
  have hk0 : (0 : ℝ) < k := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt n := by linarith
  have h2 : tau88 n d k / k ≤ 217 / 50 / Real.sqrt n := by
    rw [div_le_iff₀ hk0]
    calc tau88 n d k ≤ 217 / 50 * k / Real.sqrt n := h1
      _ = 217 / 50 / Real.sqrt n * k := by ring
  have h3 := pow_le_pow_left₀ (by positivity) h2 2
  have e : (217 / 50 / Real.sqrt n) ^ 2 = (217 / 50) ^ 2 / n := by
    rw [div_pow, h.ssq]
  rw [e] at h3
  have hn0 : (0 : ℝ) < n := by have := h.n9; linarith
  calc (n : ℝ) * (tau88 n d k / k) ^ 2 ≤ n * ((217 / 50) ^ 2 / n) :=
        mul_le_mul_of_nonneg_left h3 hn0.le
    _ = (217 / 50) ^ 2 := by field_simp
    _ ≤ 471 / 25 := by norm_num

/-- `(τ/k)² ≤ η²/4`. -/
theorem tauk_sq (h : Hyp88 n d k η) : (tau88 n d k / k) ^ 2 ≤ η ^ 2 / 4 := by
  have h0 := h.tau_le.1
  have h1 := h.tau_eta
  have hk := h.k1
  have hk0 : (0 : ℝ) < k := by linarith
  have h2 : tau88 n d k / k ≤ η / 2 := by
    rw [div_le_iff₀ hk0]
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1), h.hη0]
  have h3 := pow_le_pow_left₀ (by positivity) h2 2
  calc (tau88 n d k / k) ^ 2 ≤ (η / 2) ^ 2 := h3
    _ = η ^ 2 / 4 := by ring

/-- `(1+τ)^(2k) ≤ 1/(1-η)`. -/
theorem pow_le (h : Hyp88 n d k η) : (1 + tau88 n d k) ^ (2 * k) ≤ 1 / (1 - η) := by
  have h0 := h.tau_le.1
  have h1 := h.tau_eta
  have hb := bern84 (tau88 n d k) h0 k
  have hη := h.hη
  have hp : 0 < (1 + tau88 n d k) ^ (2 * k) := by positivity
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem one_le_pow (h : Hyp88 n d k η) (m : ℕ) : 1 ≤ (1 + tau88 n d k) ^ m :=
  one_le_pow₀ (by linarith [h.tau_le.1])

theorem powk_le (h : Hyp88 n d k η) : (1 + tau88 n d k) ^ k ≤ 1 / (1 - η) :=
  (pow_le_pow_right₀ (by linarith [h.tau_le.1]) (by omega)).trans h.pow_le

end Hyp88

/-! ## The constants of the Gaussian model -/

namespace Hyp88

variable {n d k : ℕ} {η : ℝ}

theorem P_bounds (h : Hyp88 n d k η) : 1 ≤ 1 / (1 - η) ∧ 1 / (1 - η) ≤ 10 / 9 := by
  have h0 := h.hη0
  have h1 := h.hη
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith

theorem c1_le (h : Hyp88 n d k η) :
    0 ≤ c1G n d k (101 / 100) (tau88 n d k) ∧
    c1G n d k (101 / 100) (tau88 n d k) ≤ C1b η := by
  have he : 3 / 2 ≤ eD d := BstLean.Part81.three_halves_le_eD d h.hd
  have he0 : (0 : ℝ) < eD d := by linarith
  have ht0 := h.tau_le.1
  have h1 := h.tau_sq
  have h2 := h.pow_le
  have h3 := h.powk_le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨hP1, hP2⟩ := h.P_bounds
  unfold c1G C1b
  set P : ℝ := 1 / (1 - η) with hP
  have hA0 : 0 ≤ (n : ℝ) * (tau88 n d k / k) ^ 2 := by positivity
  have a1 : (n : ℝ) * ((tau88 n d k / k) ^ 2 * (1 + tau88 n d k) ^ k) ≤ 471 / 25 * P := by
    calc (n : ℝ) * ((tau88 n d k / k) ^ 2 * (1 + tau88 n d k) ^ k)
        = ((n : ℝ) * (tau88 n d k / k) ^ 2) * (1 + tau88 n d k) ^ k := by ring
      _ ≤ 471 / 25 * P := mul_le_mul h1 h3 (by positivity) (by norm_num)
  have a2 : 101 / 100 * (1 + tau88 n d k) ^ (2 * k) / eD d ≤ 101 / 150 * P := by
    rw [div_le_iff₀ he0]
    have : 101 / 100 * (1 + tau88 n d k) ^ (2 * k) ≤ 101 / 100 * P :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    nlinarith
  constructor
  · positivity
  · have : 488 / 25 / (1 - η) = 488 / 25 * P := by rw [hP]; ring
    rw [this]; linarith

theorem cE_le (h : Hyp88 n d k η) :
    0 ≤ cEG k (tau88 n d k) ∧ cEG k (tau88 n d k) ≤ 1 / (1 - η) := by
  have ht0 := h.tau_le.1
  unfold cEG
  exact ⟨by positivity, h.pow_le⟩

theorem KX_le (h : Hyp88 n d k η) : 0 ≤ KX88 n d k ∧ KX88 n d k ≤ KXb k η := by
  have he : 3 / 2 ≤ eD d := BstLean.Part81.three_halves_le_eD d h.hd
  have he0 : (0 : ℝ) < eD d := by linarith
  have hn0 : (0 : ℝ) < n := by have := h.n9; linarith
  have hk := h.k1
  have hk0 : (0 : ℝ) < k := by linarith
  have h5 := h.kn
  have hm0 : 0 ≤ min (27 * (3 : ℝ) ^ k) ((9 : ℝ) ^ k) := le_min (by positivity) (by positivity)
  unfold KX88 KXb
  constructor
  · positivity
  · have a1 : 101 / 100 * min (27 * (3 : ℝ) ^ k) ((9 : ℝ) ^ k) / eD d ≤
        101 / 150 * min (27 * (3 : ℝ) ^ k) ((9 : ℝ) ^ k) := by
      rw [div_le_iff₀ he0]; nlinarith
    have hin : 1 / (n : ℝ) ≤ (25 / 217) ^ 2 * η ^ 2 / (k : ℝ) ^ 4 := by
      rw [le_div_iff₀ (by positivity)]
      calc 1 / (n : ℝ) * (k : ℝ) ^ 4 = (k : ℝ) ^ 4 / n := by ring
        _ ≤ (25 / 217) ^ 2 * η ^ 2 := h5
    have a2 : 768 * (9 : ℝ) ^ k / n ≤ 51 / 5 * η ^ 2 * (9 : ℝ) ^ k / (k : ℝ) ^ 4 := by
      have e1 : 768 * (9 : ℝ) ^ k / n = 768 * (9 : ℝ) ^ k * (1 / n) := by ring
      have e2 : 51 / 5 * η ^ 2 * (9 : ℝ) ^ k / (k : ℝ) ^ 4 =
          51 / 5 * ((9 : ℝ) ^ k * (η ^ 2 / (k : ℝ) ^ 4)) := by ring
      rw [e1, e2]
      have hm := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ 768 * (9 : ℝ) ^ k)
      refine hm.trans ?_
      have e3 : 768 * (9 : ℝ) ^ k * ((25 / 217) ^ 2 * η ^ 2 / (k : ℝ) ^ 4) =
          768 * (25 / 217) ^ 2 * ((9 : ℝ) ^ k * (η ^ 2 / (k : ℝ) ^ 4)) := by ring
      rw [e3]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith

theorem cV_le (h : Hyp88 n d k η) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    0 ≤ cVX n d k (101 / 100) ((9 : ℝ) ^ k) (KX88 n d k) (tau88 n d k) ϑ ∧
    cVX n d k (101 / 100) ((9 : ℝ) ^ k) (KX88 n d k) (tau88 n d k) ϑ ≤ CVb k η ϑ := by
  have ht0 := h.tau_le.1
  have h2 := h.pow_le
  have h3 := h.powk_le
  have h4 := h.tauk_sq
  have h5 := h.kn
  have hk := h.k1
  have hk0 : (0 : ℝ) < k := by linarith
  obtain ⟨hc0, hc1⟩ := h.c1_le
  obtain ⟨hP1, hP2⟩ := h.P_bounds
  obtain ⟨hKX0, hKX1⟩ := h.KX_le
  have hη0 := h.hη0
  have hn0 : (0 : ℝ) < n := by have := h.n9; linarith
  have hϑ1 : 0 < 1 + 1 / ϑ := by positivity
  unfold cVX
  constructor
  · positivity
  · unfold CVb
    unfold C1b at hc1
    set P : ℝ := 1 / (1 - η) with hP
    have hc1' : c1G n d k (101 / 100) (tau88 n d k) ≤ 488 / 25 * P := by
      have : 488 / 25 / (1 - η) = 488 / 25 * P := by rw [hP]; ring
      linarith
    have hΦ : ((1 + tau88 n d k) ^ (2 * k) +
        (tau88 n d k / k) ^ 2 * (1 + tau88 n d k) ^ k) ^ 2 ≤ (P * (1 + η ^ 2 / 4)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      have : (tau88 n d k / k) ^ 2 * (1 + tau88 n d k) ^ k ≤ η ^ 2 / 4 * P :=
        mul_le_mul h4 h3 (by positivity) (by positivity)
      linarith
    have b1 : (1 + ϑ) * KX88 n d k * ((1 + tau88 n d k) ^ (2 * k) +
        (tau88 n d k / k) ^ 2 * (1 + tau88 n d k) ^ k) ^ 2 ≤
        (1 + ϑ) * KXb k η * (P * (1 + η ^ 2 / 4)) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hKX1 (by linarith)) hΦ (by positivity)
        (mul_nonneg (by linarith) (le_trans hKX0 hKX1))
    have hsq : c1G n d k (101 / 100) (tau88 n d k) ^ 2 ≤ (488 / 25 * P) ^ 2 :=
      pow_le_pow_left₀ hc0 hc1' 2
    have hin : 1 / (n : ℝ) ≤ (25 / 217) ^ 2 * η ^ 2 / (k : ℝ) ^ 4 := by
      rw [le_div_iff₀ (by positivity)]
      calc 1 / (n : ℝ) * (k : ℝ) ^ 4 = (k : ℝ) ^ 4 / n := by ring
        _ ≤ (25 / 217) ^ 2 * η ^ 2 := h5
    have b2 : (1 + 1 / ϑ) * (9 : ℝ) ^ k * c1G n d k (101 / 100) (tau88 n d k) ^ 2 / n ≤
        (1 + 1 / ϑ) * (51 / 10) * η ^ 2 / (k : ℝ) ^ 4 * (9 : ℝ) ^ k * P ^ 2 := by
      have e : (1 + 1 / ϑ) * (9 : ℝ) ^ k * c1G n d k (101 / 100) (tau88 n d k) ^ 2 / n =
          (1 + 1 / ϑ) * (9 : ℝ) ^ k *
            (c1G n d k (101 / 100) (tau88 n d k) ^ 2 * (1 / n)) := by ring
      rw [e]
      have hm : c1G n d k (101 / 100) (tau88 n d k) ^ 2 * (1 / n) ≤
          (488 / 25 * P) ^ 2 * ((25 / 217) ^ 2 * η ^ 2 / (k : ℝ) ^ 4) :=
        mul_le_mul hsq hin (by positivity) (by positivity)
      have hm2 : (488 / 25 * P) ^ 2 * ((25 / 217) ^ 2 * η ^ 2 / (k : ℝ) ^ 4) ≤
          51 / 10 * η ^ 2 / (k : ℝ) ^ 4 * P ^ 2 := by
        have e2 : (488 / 25 * P) ^ 2 * ((25 / 217) ^ 2 * η ^ 2 / (k : ℝ) ^ 4) =
            (488 / 217) ^ 2 * (η ^ 2 / (k : ℝ) ^ 4 * P ^ 2) := by ring
        have e3 : 51 / 10 * η ^ 2 / (k : ℝ) ^ 4 * P ^ 2 =
            51 / 10 * (η ^ 2 / (k : ℝ) ^ 4 * P ^ 2) := by ring
        rw [e2, e3]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      calc (1 + 1 / ϑ) * (9 : ℝ) ^ k * (c1G n d k (101 / 100) (tau88 n d k) ^ 2 * (1 / n))
          ≤ (1 + 1 / ϑ) * (9 : ℝ) ^ k * (51 / 10 * η ^ 2 / (k : ℝ) ^ 4 * P ^ 2) :=
            mul_le_mul_of_nonneg_left (hm.trans hm2) (by positivity)
        _ = (1 + 1 / ϑ) * (51 / 10) * η ^ 2 / (k : ℝ) ^ 4 * (9 : ℝ) ^ k * P ^ 2 := by ring
    have e : ((1 + ϑ) * KXb k η * (1 + η ^ 2 / 4) ^ 2 +
        (1 + 1 / ϑ) * (51 / 10) * η ^ 2 / (k : ℝ) ^ 4 * (9 : ℝ) ^ k) / (1 - η) ^ 2 =
        (1 + ϑ) * KXb k η * (P * (1 + η ^ 2 / 4)) ^ 2 +
          (1 + 1 / ϑ) * (51 / 10) * η ^ 2 / (k : ℝ) ^ 4 * (9 : ℝ) ^ k * P ^ 2 := by
      have hne : (1 - η) ≠ 0 := by have := h.hη; linarith
      rw [hP]; field_simp
    rw [e]; linarith

theorem efl_le (h : Hyp88 n d k η) :
    eflG n d k (101 / 100) (tau88 n d k) ≤ Eb η := by
  obtain ⟨hc0, hc1⟩ := h.c1_le
  obtain ⟨hP1, hP2⟩ := h.P_bounds
  have h5 := h.inv_n
  have h1 := h.tau_eta
  have hη0 := h.hη0
  unfold eflG Eb
  unfold C1b at hc1
  have hc1' : c1G n d k (101 / 100) (tau88 n d k) ≤ 488 / 25 * (10 / 9) := by
    have : 488 / 25 / (1 - η) = 488 / 25 * (1 / (1 - η)) := by ring
    nlinarith
  have e : c1G n d k (101 / 100) (tau88 n d k) / n =
      c1G n d k (101 / 100) (tau88 n d k) * (1 / n) := by ring
  have hm : c1G n d k (101 / 100) (tau88 n d k) * (1 / n) ≤
      488 / 25 * (10 / 9) * ((25 / 217) ^ 2 * η ^ 2) :=
    mul_le_mul hc1' h5 (by positivity) (by positivity)
  rw [e]
  have hη2 : 0 ≤ η ^ 2 := by positivity
  nlinarith

end Hyp88

/-! ## The parameters of the sphere step -/

namespace Hyp88

variable {n d k : ℕ} {η : ℝ}

theorem beta_spec (h : Hyp88 n d k η) :
    0 < beta88 n k ∧ beta88 n k ≤ 1 / 180000 ∧ (k : ℝ) * beta88 n k = 1 / (2 * n) ∧
    beta88 n k ≤ 1 / (2 * n) := by
  have hk := h.k1
  have hn := h.n9
  have hk0 : (0 : ℝ) < k := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have e : (k : ℝ) * beta88 n k = 1 / (2 * n) := by
    unfold beta88; field_simp
  have hpos : 0 < beta88 n k := by unfold beta88; positivity
  have hle : beta88 n k ≤ 1 / (2 * n) := by
    rw [← e]; nlinarith
  refine ⟨hpos, hle.trans ?_, e, hle⟩
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem xi_spec (h : Hyp88 n d k η) :
    0 < xi88 k ∧ xi88 k ≤ 1 / 4 ∧ xi88 k ^ 2 = 1 / (16 * (k : ℝ) ^ 2) ∧
    xi88 k * beta88 n k = 1 / (8 * (k : ℝ) ^ 2 * n) := by
  have hk := h.k1
  have hn := h.n9
  have hk0 : (0 : ℝ) < k := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by unfold xi88; positivity, ?_, ?_, ?_⟩
  · unfold xi88; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · unfold xi88; field_simp; ring
  · unfold xi88 beta88; field_simp; ring

theorem win (h : Hyp88 n d k η) :
    (1 + 1 / (n : ℝ)) * (1 + beta88 n k) ≤ 1 + (31 / 20 : ℝ) / n ∧
    1 - (31 / 20 : ℝ) / n ≤ (1 - 1 / (n : ℝ)) * (1 - beta88 n k) := by
  obtain ⟨hb0, hb1, -, hb2⟩ := h.beta_spec
  have hn := h.n9
  have hn0 : (0 : ℝ) < n := by linarith
  set a : ℝ := 1 / (n : ℝ) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 / 90000 := by
    rw [ha, div_le_div_iff₀ hn0 (by norm_num)]; linarith
  have hb : beta88 n k ≤ a / 2 := by
    have : 1 / (2 * (n : ℝ)) = a / 2 := by rw [ha]; ring
    linarith
  have e : (31 / 20 : ℝ) / n = 31 / 20 * a := by rw [ha]; ring
  rw [e]
  set b : ℝ := beta88 n k
  constructor
  · have h2 : (1 + a) * (1 + b) ≤ (1 + a) * (1 + a / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [mul_pos ha0 ha0]
  · have h2 : (1 - a) * (1 - a / 2) ≤ (1 - a) * (1 - b) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [mul_pos ha0 ha0]

/-- `k · tBE ≤ (501/1000)/√n`. -/
theorem ktB (h : Hyp88 n d k η) :
    0 ≤ (k : ℝ) * tBE n (beta88 n k) ∧
    (k : ℝ) * tBE n (beta88 n k) ≤ 501 / 1000 / Real.sqrt n := by
  obtain ⟨hb0, hb1, hkb, -⟩ := h.beta_spec
  have hk := h.k1
  have hs := h.s300
  have hs0 : (0 : ℝ) < Real.sqrt n := by linarith
  have hn0 : (0 : ℝ) < n := by have := h.n9; linarith
  set b : ℝ := beta88 n k
  have hden : (0 : ℝ) < 1 - b := by linarith
  have e : (k : ℝ) * tBE n b = 1 / (2 * (1 - b)) * (1 / Real.sqrt n) := by
    have e2 : Real.sqrt n / n = 1 / Real.sqrt n := by
      rw [div_eq_div_iff hn0.ne' hs0.ne']
      have := h.ssq
      nlinarith
    unfold tBE
    calc (k : ℝ) * (b * Real.sqrt n / (1 - b))
        = ((k : ℝ) * b) * Real.sqrt n / (1 - b) := by ring
      _ = 1 / (2 * n) * Real.sqrt n / (1 - b) := by rw [hkb]
      _ = 1 / (2 * (1 - b)) * (Real.sqrt n / n) := by field_simp
      _ = 1 / (2 * (1 - b)) * (1 / Real.sqrt n) := by rw [e2]
  have hc : 1 / (2 * (1 - b)) ≤ 501 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [e]
  constructor
  · positivity
  · calc 1 / (2 * (1 - b)) * (1 / Real.sqrt n)
        ≤ 501 / 1000 * (1 / Real.sqrt n) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 501 / 1000 / Real.sqrt n := by ring

/-- `k/√n ≤ (25/217) η`. -/
theorem ks1 (h : Hyp88 n d k η) : (k : ℝ) / Real.sqrt n ≤ 25 / 217 * η := by
  have hk := h.k1
  have hs := h.s300
  refine le_trans ?_ h.ks
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

/-- The drift: `n · DrFE² ≤ k² ρ²`. -/
theorem drift (h : Hyp88 n d k η) :
    (n : ℝ) * DrFE n k (c1G n d k (101 / 100) (tau88 n d k)) (cEG k (tau88 n d k))
      (beta88 n k) ^ 2 ≤ (k : ℝ) ^ 2 * rhob k η ^ 2 := by
  obtain ⟨hv0, hv1⟩ := h.ktB
  obtain ⟨hc0, hc1⟩ := h.c1_le
  obtain ⟨hE0, hE1⟩ := h.cE_le
  obtain ⟨hP1, hP2⟩ := h.P_bounds
  have hk := h.k1
  have hk0 : (0 : ℝ) < k := by linarith
  have hs := h.s300
  have hs0 : (0 : ℝ) < Real.sqrt n := by linarith
  have hn0 : (0 : ℝ) < n := by have := h.n9; linarith
  have hη0 := h.hη0
  have hη := h.hη
  have hks := h.ks1
  have hks2 := h.ks
  set v : ℝ := (k : ℝ) * tBE n (beta88 n k) with hv
  set c1 : ℝ := c1G n d k (101 / 100) (tau88 n d k) with hc1d
  set cE : ℝ := cEG k (tau88 n d k) with hcEd
  set P : ℝ := 1 / (1 - η) with hP
  set s : ℝ := Real.sqrt n with hsd
  have hss : s ^ 2 = n := h.ssq
  unfold C1b at hc1
  have hc1' : c1 ≤ 488 / 25 * P := by
    have : 488 / 25 / (1 - η) = 488 / 25 * P := by rw [hP]; ring
    linarith
  set x : ℝ := 2 * (k : ℝ) * v with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 501 / 500 * (k / s) := by
    rw [hx]
    have : 2 * (k : ℝ) * v ≤ 2 * k * (501 / 1000 / s) :=
      mul_le_mul_of_nonneg_left hv1 (by linarith)
    refine this.trans (le_of_eq ?_); ring
  have hx2 : x ≤ η / 8 := by nlinarith
  have hb := bern84 v hv0 k
  set Q : ℝ := (1 + v) ^ (2 * k) with hQ
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by linarith)
  have h8 : (0 : ℝ) < 1 - η / 8 := by linarith
  have hQm : Q - 1 ≤ 501 / 500 * (k / s) / (1 - η / 8) := by
    rw [le_div_iff₀ h8]
    have hb' : (1 - x) * Q ≤ 1 := by rw [hx]; exact hb
    have h1 : (Q - 1) * (1 - x) ≤ x := by nlinarith
    have h2 : (Q - 1) * (1 - η / 8) ≤ (Q - 1) * (1 - x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hDr0 : 0 ≤ DrFE n k c1 cE (beta88 n k) := by
    unfold DrFE
    have : 0 ≤ ((1 + (k : ℝ) * tBE n (beta88 n k)) ^ (2 * k) - 1) * cE :=
      mul_nonneg (by linarith) hE0
    have h2 : 0 ≤ 2 * c1 / n := by positivity
    linarith
  have hkey : s * DrFE n k c1 cE (beta88 n k) ≤ k * rhob k η := by
    unfold DrFE
    have t1 : ((1 + (k : ℝ) * tBE n (beta88 n k)) ^ (2 * k) - 1) * cE ≤
        501 / 500 * (k / s) / (1 - η / 8) * P :=
      mul_le_mul hQm hE1 hE0 (by positivity)
    have t2 : 2 * c1 / n ≤ 2 * (488 / 25 * P) / n :=
      div_le_div_of_nonneg_right (by linarith) hn0.le
    have e1 : s * (501 / 500 * (k / s) / (1 - η / 8) * P) =
        k * (501 / 500 / (1 - η / 8)) * P := by field_simp
    have e2 : s * (2 * (488 / 25 * P) / n) = 976 / 25 / s * P := by
      rw [← hss]; field_simp; norm_num
    have t3 : 976 / 25 / s ≤ k * (9 * η / (2 * (k : ℝ) ^ 3)) := by
      have e3 : (k : ℝ) * (9 * η / (2 * (k : ℝ) ^ 3)) = 9 * η / (2 * (k : ℝ) ^ 2) := by
        field_simp
      rw [e3, div_le_div_iff₀ hs0 (by positivity)]
      have := h.hηn
      nlinarith
    have hP0 : 0 ≤ P := by linarith
    calc s * (((1 + (k : ℝ) * tBE n (beta88 n k)) ^ (2 * k) - 1) * cE + 2 * c1 / n)
        ≤ s * (501 / 500 * (k / s) / (1 - η / 8) * P + 2 * (488 / 25 * P) / n) :=
          mul_le_mul_of_nonneg_left (by linarith) hs0.le
      _ = k * (501 / 500 / (1 - η / 8)) * P + 976 / 25 / s * P := by rw [mul_add, e1, e2]
      _ ≤ k * (501 / 500 / (1 - η / 8)) * P + k * (9 * η / (2 * (k : ℝ) ^ 3)) * P := by
          have := mul_le_mul_of_nonneg_right t3 hP0
          linarith
      _ = k * rhob k η := by unfold rhob; rw [hP]; ring
  have := pow_le_pow_left₀ (by positivity) hkey 2
  calc (n : ℝ) * DrFE n k c1 cE (beta88 n k) ^ 2
      = (s * DrFE n k c1 cE (beta88 n k)) ^ 2 := by rw [mul_pow, hss]
    _ ≤ (k * rhob k η) ^ 2 := this
    _ = (k : ℝ) ^ 2 * rhob k η ^ 2 := by ring

/-- `ν ≤ (7/2) η²`. -/
theorem nu_le (h : Hyp88 n d k η) :
    0 ≤ nuBE n d (beta88 n k) (xi88 k) ∧ nuBE n d (beta88 n k) (xi88 k) ≤ 7 / 2 * η ^ 2 := by
  obtain ⟨-, -, -, hxb⟩ := h.xi_spec
  have hk := h.k1
  have hk0 : (0 : ℝ) < k := by linarith
  have hn0 : (0 : ℝ) < n := by have := h.n9; linarith
  have hD := DW_ge_cube n d h.hd
  have hD0 : 0 < DW n d := lt_of_lt_of_le (by positivity) hD
  have hkn := h.kn
  unfold nuBE
  have e : (99 / 100 * xi88 k * beta88 n k) = 99 / (800 * (k : ℝ) ^ 2 * n) := by
    rw [mul_assoc, hxb]; field_simp; ring
  rw [e]
  constructor
  · positivity
  · have hlow : (n : ℝ) ^ 3 / 2 * (99 / (800 * (k : ℝ) ^ 2 * n)) ^ 2 ≤
        DW n d * (99 / (800 * (k : ℝ) ^ 2 * n)) ^ 2 :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    have e2 : (n : ℝ) ^ 3 / 2 * (99 / (800 * (k : ℝ) ^ 2 * n)) ^ 2 =
        9801 * n / (1280000 * (k : ℝ) ^ 4) := by
      field_simp; ring
    rw [e2] at hlow
    have hpos : (0 : ℝ) < 9801 * n / (1280000 * (k : ℝ) ^ 4) := by positivity
    calc 2 / (DW n d * (99 / (800 * (k : ℝ) ^ 2 * n)) ^ 2)
        ≤ 2 / (9801 * n / (1280000 * (k : ℝ) ^ 4)) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hlow
      _ = 2560000 / 9801 * ((k : ℝ) ^ 4 / n) := by field_simp; ring
      _ ≤ 2560000 / 9801 * ((25 / 217) ^ 2 * η ^ 2) :=
          mul_le_mul_of_nonneg_left hkn (by norm_num)
      _ ≤ 7 / 2 * η ^ 2 := by nlinarith [sq_nonneg η]

end Hyp88

/-- `Sodd D ≤ (D+1)(D+2)(D+3)/6`. -/
theorem Sodd_le (D : ℕ) : Sodd D ≤ ((D : ℝ) + 1) * ((D : ℝ) + 2) * ((D : ℝ) + 3) / 6 := by
  have h1 := Sodd_mono (show D ≤ 2 * ((D + 1) / 2) by omega)
  rw [Sodd_two_mul] at h1
  have hm : (((D + 1) / 2 : ℕ) : ℝ) ≤ ((D : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := D + 1) (n := 2)
    push_cast at this; linarith
  have hm0 : (0 : ℝ) ≤ (((D + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  set m : ℝ := (((D + 1) / 2 : ℕ) : ℝ)
  have h2 : 2 / 3 * m * (m + 1) * (2 * m + 1) ≤
      2 / 3 * (((D : ℝ) + 1) / 2) * (((D : ℝ) + 1) / 2 + 1) * (2 * (((D : ℝ) + 1) / 2) + 1) := by
    have a1 : m * (m + 1) ≤ (((D : ℝ) + 1) / 2) * (((D : ℝ) + 1) / 2 + 1) :=
      mul_le_mul hm (by linarith) (by linarith) (by linarith)
    have a2 : m * (m + 1) * (2 * m + 1) ≤
        (((D : ℝ) + 1) / 2) * (((D : ℝ) + 1) / 2 + 1) * (2 * (((D : ℝ) + 1) / 2) + 1) :=
      mul_le_mul a1 (by linarith) (by linarith) (by positivity)
    nlinarith
  have e : 2 / 3 * (((D : ℝ) + 1) / 2) * (((D : ℝ) + 1) / 2 + 1) * (2 * (((D : ℝ) + 1) / 2) + 1) =
      ((D : ℝ) + 1) * ((D : ℝ) + 2) * ((D : ℝ) + 3) / 6 := by ring
  linarith

namespace Hyp88

variable {n d k : ℕ} {η : ℝ}

/-- The Christoffel constants of the even/odd transfer. -/
theorem SE_le (h : Hyp88 n d k η) :
    0 ≤ SE k (beta88 n k) (xi88 k) ∧
    SE k (beta88 n k) (xi88 k) ≤ 60001 / 60000 * ((k : ℝ) / 4 + 1 + penS k) ∧
    0 ≤ SE (2 * k) (beta88 n k) (xi88 k) ∧
    SE (2 * k) (beta88 n k) (xi88 k) ≤ 60001 / 60000 * ((k : ℝ) / 2 + 1 + penS k) := by
  obtain ⟨-, -, hx2, -⟩ := h.xi_spec
  obtain ⟨hb0, hb1, -, -⟩ := h.beta_spec
  have hk := h.k1
  have hk0 : (0 : ℝ) < k := by linarith
  have hSk := Sodd_le k
  have hpen : 5 / 4 * xi88 k ^ 2 * Sodd k ≤ penS k := by
    rw [hx2]; unfold penS
    have e : 5 / 384 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3)) / (k : ℝ) ^ 2 =
        5 / 4 * (1 / (16 * (k : ℝ) ^ 2)) *
          (((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) / 6) := by
      field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hSk (by positivity)
  have hx20 : 0 ≤ 5 / 4 * xi88 k ^ 2 := by positivity
  have hpenD : ∀ D : ℕ, D ≤ k → 5 / 4 * xi88 k ^ 2 * Sodd D ≤ penS k := fun D hD =>
    (mul_le_mul_of_nonneg_left (Sodd_mono hD) hx20).trans hpen
  have hpen0 : ∀ D : ℕ, 0 ≤ 5 / 4 * xi88 k ^ 2 * Sodd D := fun D =>
    mul_nonneg hx20 (Sodd_nonneg D)
  have c1 : (((k / 2 / 2 : ℕ) : ℝ)) ≤ (k : ℝ) / 4 := by
    have a := Nat.cast_div_le (α := ℝ) (m := k / 2) (n := 2)
    have b := Nat.cast_div_le (α := ℝ) (m := k) (n := 2)
    push_cast at a b; linarith
  have c2 : ((((k - 1) / 2 / 2 : ℕ) : ℝ)) ≤ (k : ℝ) / 4 := by
    have a := Nat.cast_div_le (α := ℝ) (m := (k - 1) / 2) (n := 2)
    have b := Nat.cast_div_le (α := ℝ) (m := k - 1) (n := 2)
    have c : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    push_cast at a b; linarith
  have c3 : (((2 * k / 2 / 2 : ℕ) : ℝ)) ≤ (k : ℝ) / 2 := by
    rw [Nat.mul_div_cancel_left k (by norm_num)]
    have b := Nat.cast_div_le (α := ℝ) (m := k) (n := 2)
    push_cast at b; linarith
  have c4 : ((((2 * k - 1) / 2 / 2 : ℕ) : ℝ)) ≤ (k : ℝ) / 2 := by
    have e : (2 * k - 1) / 2 = k - 1 := by have := h.hk; omega
    rw [e]
    have b := Nat.cast_div_le (α := ℝ) (m := k - 1) (n := 2)
    have c : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    push_cast at b; linarith
  have d1 : k / 2 ≤ k := Nat.div_le_self _ _
  have d2 : (k - 1) / 2 ≤ k := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have d3 : 2 * k / 2 ≤ k := by rw [Nat.mul_div_cancel_left k (by norm_num)]
  have d4 : (2 * k - 1) / 2 ≤ k := by have := h.hk; omega
  have hb3 : 1 + 3 * beta88 n k ≤ 60001 / 60000 := by linarith
  have hb30 : 0 ≤ 1 + 3 * beta88 n k := by linarith
  have key : ∀ (D : ℕ) (X : ℝ), (((D / 2 : ℕ) : ℝ)) ≤ X → D ≤ k →
      0 ≤ SS D (xi88 k) ∧ SS D (xi88 k) ≤ X + 1 + penS k := by
    intro D X hX hD
    unfold SS
    have := hpenD D hD
    have := hpen0 D
    have : (0 : ℝ) ≤ ((D / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor <;> linarith
  obtain ⟨a0, a1⟩ := key (k / 2) _ c1 d1
  obtain ⟨b0, b1⟩ := key ((k - 1) / 2) _ c2 d2
  obtain ⟨e0, e1⟩ := key (2 * k / 2) _ c3 d3
  obtain ⟨f0, f1⟩ := key ((2 * k - 1) / 2) _ c4 d4
  have hpS0 : 0 ≤ penS k := le_trans (hpen0 k) hpen
  unfold SE
  refine ⟨le_max_of_le_left a0, max_le ?_ ?_, le_max_of_le_left e0, max_le ?_ ?_⟩
  · nlinarith
  · exact mul_le_mul hb3 b1 b0 (by norm_num)
  · nlinarith
  · exact mul_le_mul hb3 f1 f0 (by norm_num)

theorem Eb_le (h : Hyp88 n d k η) : 0 ≤ Eb η ∧ Eb η ≤ 103 / 1000 := by
  have h0 := h.hη0
  have h1 := h.hη
  unfold Eb
  constructor
  · positivity
  · nlinarith

/-- **The sphere-step bound is at most `PSb / n`.** -/
theorem pS_le (h : Hyp88 n d k η) (ϑ θ ε κ : ℝ) (hϑ : 0 < ϑ) (hθ : 0 < θ) (hε : 0 < ε)
    (hκ0 : 0 < κ) (hκ : κ ≤ 1 / 2) :
    pSE n d k (c1G n d k (101 / 100) (tau88 n d k))
      (cVX n d k (101 / 100) ((9 : ℝ) ^ k) (KX88 n d k) (tau88 n d k) ϑ)
      (eflG n d k (101 / 100) (tau88 n d k)) (cEG k (tau88 n d k))
      (beta88 n k) (xi88 k) θ ε κ ≤ PSb k η ϑ θ ε κ / n := by
  obtain ⟨hc0, hc1⟩ := h.c1_le
  obtain ⟨hV0, hV1⟩ := h.cV_le ϑ hϑ
  have hefl := h.efl_le
  obtain ⟨hEb0, hEb1⟩ := h.Eb_le
  have hdr := h.drift
  obtain ⟨hnu0, hnu1⟩ := h.nu_le
  obtain ⟨hS10, hS11, hS20, hS21⟩ := h.SE_le
  obtain ⟨-, -, hx2, -⟩ := h.xi_spec
  have hk := h.k1
  have hk0 : (0 : ℝ) < k := by linarith
  have hn0 : (0 : ℝ) < n := by have := h.n9; linarith
  have hη0 := h.hη0
  have hη := h.hη
  unfold pSE PSb cVeE
  set c1 : ℝ := c1G n d k (101 / 100) (tau88 n d k)
  set cV : ℝ := cVX n d k (101 / 100) ((9 : ℝ) ^ k) (KX88 n d k) (tau88 n d k) ϑ
  set efl : ℝ := eflG n d k (101 / 100) (tau88 n d k)
  set cE : ℝ := cEG k (tau88 n d k)
  set Dr2 : ℝ := (n : ℝ) * DrFE n k c1 cE (beta88 n k) ^ 2
  have hDr20 : 0 ≤ Dr2 := by positivity
  set ν : ℝ := nuBE n d (beta88 n k) (xi88 k)
  set S1 : ℝ := SE k (beta88 n k) (xi88 k)
  set S2 : ℝ := SE (2 * k) (beta88 n k) (xi88 k)
  rw [hx2]
  have hC1b0 : 0 ≤ C1b η := le_trans hc0 hc1
  have hεκ : 0 < ε ^ 2 * κ := by positivity
  have T1 : S1 * c1 / (n * (ε ^ 2 * κ)) ≤
      (60001 / 60000 * ((k : ℝ) / 4 + 1 + penS k) * C1b η / (ε ^ 2 * κ)) / n := by
    rw [div_div, mul_comm (ε ^ 2 * κ) (n : ℝ)]
    exact div_le_div_of_nonneg_right (mul_le_mul hS11 hc1 hc0 (le_trans hS10 hS11))
      (by positivity)
  have hθi : 0 < 1 + 1 / θ := by positivity
  have hcVe : (1 + θ) * cV + (1 + 1 / θ) * Dr2 ≤
      (1 + θ) * CVb k η ϑ + (1 + 1 / θ) * ((k : ℝ) ^ 2 * rhob k η ^ 2) := by
    have a := mul_le_mul_of_nonneg_left hV1 (by linarith : (0 : ℝ) ≤ 1 + θ)
    have b := mul_le_mul_of_nonneg_left hdr hθi.le
    linarith
  have hcVe0 : 0 ≤ (1 + θ) * cV + (1 + 1 / θ) * Dr2 := by positivity
  have hden1 : 0 < 1 - Eb η - κ := by linarith
  have hden2 : 1 - Eb η - κ ≤ 1 - efl - κ := by linarith
  have hsq : (1 - Eb η - κ) ^ 2 ≤ (1 - efl - κ) ^ 2 := pow_le_pow_left₀ hden1.le hden2 2
  have T2 : S2 * ((1 + θ) * cV + (1 + 1 / θ) * Dr2) / (n * (1 - efl - κ) ^ 2) ≤
      (60001 / 60000 * ((k : ℝ) / 2 + 1 + penS k) *
        ((1 + θ) * CVb k η ϑ + (1 + 1 / θ) * ((k : ℝ) ^ 2 * rhob k η ^ 2)) /
        (1 - Eb η - κ) ^ 2) / n := by
    rw [div_div, mul_comm ((1 - Eb η - κ) ^ 2) (n : ℝ)]
    exact div_le_div₀ (mul_nonneg (le_trans hS20 hS21) (le_trans hcVe0 hcVe))
      (mul_le_mul hS21 hcVe hcVe0 (le_trans hS20 hS21))
      (by positivity) (mul_le_mul_of_nonneg_left hsq hn0.le)
  have hT10 : 0 ≤ S1 * c1 / (n * (ε ^ 2 * κ)) := by positivity
  have hT20 : 0 ≤ S2 * ((1 + θ) * cV + (1 + 1 / θ) * Dr2) / (n * (1 - efl - κ) ^ 2) := by
    have : 0 < 1 - efl - κ := by linarith
    positivity
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk
  have hxi : (0 : ℝ) < 1 - 1 / (16 * (k : ℝ) ^ 2) := by
    have : 1 / (16 * (k : ℝ) ^ 2) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hνb : (0 : ℝ) < 1 - 7 / 2 * η ^ 2 := by nlinarith
  have hden : (1 - 1 / (16 * (k : ℝ) ^ 2)) * (1 - 7 / 2 * η ^ 2) ≤
      (1 - 1 / (16 * (k : ℝ) ^ 2)) * (1 - ν) :=
    mul_le_mul_of_nonneg_left (by linarith) hxi.le
  have hnum := add_le_add T1 T2
  rw [← add_div] at hnum
  rw [div_right_comm]
  exact div_le_div₀ (le_trans (add_nonneg hT10 hT20) hnum) hnum (by positivity) hden

/-- The side conditions of the sphere step. -/
theorem side (h : Hyp88 n d k η) (κ : ℝ) (hκ : κ ≤ 1 / 2) :
    eflG n d k (101 / 100) (tau88 n d k) + κ < 1 ∧ beta88 n k ≤ 1 / 4 ∧ xi88 k ≤ 1 / 2 ∧
    xi88 k * beta88 n k ≤ 1 / 100 ∧ nuBE n d (beta88 n k) (xi88 k) < 1 ∧
    (31 / 20 : ℝ) / n ≤ 1 / 10 := by
  have hefl := h.efl_le
  obtain ⟨hEb0, hEb1⟩ := h.Eb_le
  obtain ⟨hb0, hb1, -, -⟩ := h.beta_spec
  obtain ⟨hx0, hx1, -, -⟩ := h.xi_spec
  obtain ⟨hnu0, hnu1⟩ := h.nu_le
  have hη0 := h.hη0
  have hη := h.hη
  have hn := h.n9
  refine ⟨by linarith, by linarith, by linarith, by nlinarith, by nlinarith, ?_⟩
  rw [div_le_iff₀ (by linarith)]; linarith

end Hyp88

end BstLean.Part88
