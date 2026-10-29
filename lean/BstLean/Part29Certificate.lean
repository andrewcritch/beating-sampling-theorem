import Mathlib

/-!
# Part 29, layer L1: the arithmetic certificate

`proofs/option-m/29-explicit-22-at-100.tex`. The quantities below are the closed forms that part 29's
theorem uses: the floor's failure bound `η'ₙ`, the variance factor `κₙ`, the program costs, and the
overlap ratios `a_E`, `a_U`. This file proves the inequalities that make every window close, at every
`n ≥ 100`, for the stated ranges of `δ`. It does not prove that these closed forms are the right ones
(that is layers L2–L4).
-/

namespace BstLean.Part29

open Real

/-- `η'ₙ` as part 28 writes it. -/
noncomputable def eta (n : ℝ) : ℝ :=
  (16 + 32 / 3 * (n - 4) + 16 / 3 * ((n - 4) * (n - 5) / 2)) / (n * (n - 1) * (n - 2) * (n - 3) / 24)

/-- The closed form of `η'ₙ` used in part 29's monotonicity remark. -/
theorem eta_closed (n : ℝ) (hn : 4 ≤ n) :
    eta n = 64 * (n ^ 2 - 5 * n + 10) / (n * (n - 1) * (n - 2) * (n - 3)) := by
  have h0 : n ≠ 0 := by linarith
  have h1 : n - 1 ≠ 0 := by linarith
  have h2 : n - 2 ≠ 0 := by linarith
  have h3 : n - 3 ≠ 0 := by linarith
  unfold eta
  field_simp
  ring

/-- `κₙ`, the variance factor of the parity floor. -/
noncomputable def kappa (n : ℝ) : ℝ := (n - 1) * (n - 2) * (n - 3) / ((n + 2) * (n + 4) * (n + 6))

/-- Per-sample cost of dense schoolbook sampling, `P = n(N-1) = n²(n+3)/2` (part 2). -/
noncomputable def P (n : ℝ) : ℝ := n ^ 2 * (n + 3) / 2
/-- Enlarged cost of the exact branch (codex, `omW100-codex-disprover.md`). -/
noncomputable def CE (n : ℝ) : ℝ := n ^ 2 * (n + 1) ^ 2 / 2 + n ^ 3 + 10 * n ^ 2 + 20 * n + 100
/-- Enlarged cost of the heat branch `ĝ''`. -/
noncomputable def CH (n : ℝ) : ℝ := n ^ 3 + 10 * n ^ 2 + 20 * n + 100
/-- Enlarged cost of the `O(n²)` branch U2. -/
noncomputable def CU (n : ℝ) : ℝ := 3 * n ^ 2 + 20 * n + 100
/-- `‖Λ‖_F²` for the Gram weights. -/
noncomputable def Lam (n : ℝ) : ℝ := n * (n + 7) / 8
/-- `‖Σ‖_F²`, the centred monomial covariance at `d_M = 2`. -/
noncomputable def sN (n : ℝ) : ℝ := 1 / n + (n * (n - 1) / 2 + 4 * (n - 1)) / (n ^ 2 * (n + 2) ^ 2)

/-- Overlap ratio of the exact and heat branches: the window closes when `q > a_E / c₀`. -/
noncomputable def aE (n : ℝ) : ℝ := 32 * Lam n * CE n / (n ^ 2 * (n + 2) ^ 2 * kappa n * P n)
/-- Overlap ratio of the heat and U2 branches: the window closes when `q > a_U / c₀`. -/
noncomputable def aU (n : ℝ) : ℝ := 8 * sN n * CH n / (kappa n * P n)

section
variable (t : ℕ)

private lemma pos100 : (0 : ℝ) < 100 + t := by positivity

theorem eta_le : eta (100 + t) ≤ 13 / 2000 := by
  rw [eta_closed _ (by have := (Nat.cast_nonneg t : (0:ℝ) ≤ t); linarith)]
  have hd : (0 : ℝ) < (100 + t) * (100 + t - 1) * (100 + t - 2) * (100 + t - 3) := by
    have := (Nat.cast_nonneg t : (0:ℝ) ≤ t)
    apply mul_pos (mul_pos (mul_pos _ _) _) _ <;> linarith
  rw [div_le_div_iff₀ hd (by norm_num)]
  ring_nf
  nlinarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t), pow_nonneg (Nat.cast_nonneg t : (0:ℝ) ≤ t) 2,
    pow_nonneg (Nat.cast_nonneg t : (0:ℝ) ≤ t) 3, pow_nonneg (Nat.cast_nonneg t : (0:ℝ) ≤ t) 4]

theorem kappa_ge : 4 / 5 ≤ kappa (100 + t) := by
  have := (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  unfold kappa
  rw [le_div_iff₀ (by positivity)]
  ring_nf
  nlinarith [pow_nonneg this 2, pow_nonneg this 3]

theorem CU_lt_P : CU (100 + t) < P (100 + t) := by
  have := (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  unfold CU P
  ring_nf
  nlinarith [pow_nonneg this 2, pow_nonneg this 3]

end


section overlaps
variable (t : ℕ)

/-- The polynomial form of `a_E < 11/200` at `n = 100 + t`. -/
theorem aE_poly :
    let n : ℝ := 100 + t
    6400 * Lam n * CE n * ((n + 2) * (n + 4) * (n + 6)) <
      11 * (n ^ 2 * (n + 2) ^ 2 * ((n - 1) * (n - 2) * (n - 3)) * P n) := by
  intro n
  have key : 11 * (n ^ 2 * (n + 2) ^ 2 * ((n - 1) * (n - 2) * (n - 3)) * P n)
      - 6400 * Lam n * CE n * ((n + 2) * (n + 4) * (n + 6)) = 53123032240752000000 + 11406041503865920000 * (t:ℝ)^1 + 775169235034864000 * (t:ℝ)^2 + 27337881412483200 * (t:ℝ)^3 + 589720540052604 * (t:ℝ)^4 + 8350249346598 * (t:ℝ)^5 + 79699327491 * (t:ℝ)^6 + (1020927857/2) * (t:ℝ)^7 + (4221335/2) * (t:ℝ)^8 + (10211/2) * (t:ℝ)^9 + (11/2) * (t:ℝ)^10 := by
    simp only [n, Lam, CE, P]; ring
  have : (0:ℝ) < 53123032240752000000 + 11406041503865920000 * (t:ℝ)^1 + 775169235034864000 * (t:ℝ)^2 + 27337881412483200 * (t:ℝ)^3 + 589720540052604 * (t:ℝ)^4 + 8350249346598 * (t:ℝ)^5 + 79699327491 * (t:ℝ)^6 + (1020927857/2) * (t:ℝ)^7 + (4221335/2) * (t:ℝ)^8 + (10211/2) * (t:ℝ)^9 + (11/2) * (t:ℝ)^10 := by positivity
  linarith

/-- The polynomial form of `a_U < 11/50` at `n = 100 + t` (after multiplying by `n²(n+2)²`). -/
theorem aU_poly :
    let n : ℝ := 100 + t
    400 * (sN n * (n ^ 2 * (n + 2) ^ 2)) * CH n * ((n + 2) * (n + 4) * (n + 6)) <
      11 * ((n - 1) * (n - 2) * (n - 3)) * P n * (n ^ 2 * (n + 2) ^ 2) := by
  intro n
  have hn : n ≠ 0 := by simp only [n]; positivity
  have hn2 : n + 2 ≠ 0 := by simp only [n]; positivity
  have hs : sN n * (n ^ 2 * (n + 2) ^ 2) = n * (n + 2) ^ 2 + n * (n - 1) / 2 + 4 * (n - 1) := by
    unfold sN; field_simp; ring
  rw [hs]
  have key : 11 * ((n - 1) * (n - 2) * (n - 3)) * P n * (n ^ 2 * (n + 2) ^ 2)
      - 400 * (n * (n + 2) ^ 2 + n * (n - 1) / 2 + 4 * (n - 1)) * CH n * ((n + 2) * (n + 4) * (n + 6))
      = 36290168650385280000 + 10089960149189376000 * (t:ℝ)^1 + 730152444562656000 * (t:ℝ)^2 + 26458013875078400 * (t:ℝ)^3 + 578972504207004 * (t:ℝ)^4 + 8266224078598 * (t:ℝ)^5 + 79288783491 * (t:ℝ)^6 + (1018635457/2) * (t:ℝ)^7 + (4218535/2) * (t:ℝ)^8 + (10211/2) * (t:ℝ)^9 + (11/2) * (t:ℝ)^10 := by
    simp only [n, CH, P]; ring
  have : (0:ℝ) < 36290168650385280000 + 10089960149189376000 * (t:ℝ)^1 + 730152444562656000 * (t:ℝ)^2 + 26458013875078400 * (t:ℝ)^3 + 578972504207004 * (t:ℝ)^4 + 8266224078598 * (t:ℝ)^5 + 79288783491 * (t:ℝ)^6 + (1018635457/2) * (t:ℝ)^7 + (4218535/2) * (t:ℝ)^8 + (10211/2) * (t:ℝ)^9 + (11/2) * (t:ℝ)^10 := by positivity
  linarith

end overlaps


section closure
variable (t : ℕ)

private lemma facts :
    let n : ℝ := 100 + t
    0 < n ∧ 0 < n - 1 ∧ 0 < n - 2 ∧ 0 < n - 3 ∧ 0 < n + 2 ∧ 0 < n + 4 ∧ 0 < n + 6 ∧ 0 < P n := by
  intro n
  have := (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [n, P] <;> first | positivity | linarith

theorem aE_lt : aE (100 + t) < 11 / 200 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hP⟩ := facts t
  have hp := aE_poly t
  simp only at hp
  set n : ℝ := 100 + t
  have hk : aE n = 32 * Lam n * CE n * ((n + 2) * (n + 4) * (n + 6)) /
      (n ^ 2 * (n + 2) ^ 2 * ((n - 1) * (n - 2) * (n - 3)) * P n) := by
    unfold aE kappa; field_simp
  rw [hk, div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem aU_lt : aU (100 + t) < 11 / 50 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hP⟩ := facts t
  have hp := aU_poly t
  simp only at hp
  set n : ℝ := 100 + t
  have hk : aU n = 8 * (sN n * (n ^ 2 * (n + 2) ^ 2)) * CH n * ((n + 2) * (n + 4) * (n + 6)) /
      (((n - 1) * (n - 2) * (n - 3)) * P n * (n ^ 2 * (n + 2) ^ 2)) := by
    unfold aU kappa; field_simp
  rw [hk, div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- **Part 29's windows close at every `n ≥ 100`**, under the sampling criterion `c₀ = 1/δ`,
for every `δ ∈ [1/100, 1/2]`: with `q = δ - η'ₙ`, both overlap conditions `q > a / c₀` hold. -/
theorem windows_close_c0_inv (δ : ℝ) (hδ : 1 / 100 ≤ δ) :
    aE (100 + t) * δ < δ - eta (100 + t) ∧ aU (100 + t) * δ < δ - eta (100 + t) := by
  have he := eta_le t; have hE := aE_lt t; have hU := aU_lt t
  constructor <;> nlinarith

/-- The same under `c₀ = 1`, for every `δ ∈ [1/4, 1/2]`. -/
theorem windows_close_c0_one (δ : ℝ) (hδ : 1 / 4 ≤ δ) :
    aE (100 + t) < δ - eta (100 + t) ∧ aU (100 + t) < δ - eta (100 + t) := by
  have he := eta_le t; have hE := aE_lt t; have hU := aU_lt t
  constructor <;> linarith

end closure

end BstLean.Part29
