import BstLean.Part56Defs

/-!
# Part 56, wave 1: the cost bound is below the reduced baseline

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56Cost`). Status: proved (no `sorry`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route: `(1 − ν) 0.91/ε_hi² = (0.91/ε_hi² + 2)/2 > 2`; `(d+1)N/P = (d+1)/n`; `P ≥ n · C(n+d−1, d) ≥ n^{d+1}/d!`
and `k ≤ d` give `(n+1)^k / P → 0`.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob Tens TSymm Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (LemmaR53 GaussPolar53)
open BstLean.Part48 (SBLevel)

/-- `P = n N`. -/
theorem Pn_eq56 (n d : ℕ) : Pn n d = n * NN n d := by
  simp [Pn, BstLean.Part36.DD, NN, Fintype.card_sigma, Fintype.card_prod, Finset.mul_sum, mul_comm]

/-- `N ≥ C(n+d−1, d) ≥ n^d/d!`. -/
theorem NN_ge56 (n d : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ d / (d.factorial : ℝ) ≤ NN n d := by
  have h1 : Fintype.card (Sym (Fin n) d) ≤ Fintype.card (Mono n d) := by
    have := Fintype.card_le_of_injective (fun s : Sym (Fin n) d => (⟨⟨d, by omega⟩, s⟩ : Mono n d))
      (by intro a b h; simpa using h)
    exact this
  have h2 : ((n + d - 1).choose d : ℝ) ≤ NN n d := by
    unfold NN
    rw [Sym.card_sym_eq_choose, Fintype.card_fin] at h1
    exact_mod_cast h1
  have h3 := Nat.pow_le_choose (α := ℝ) d (n + d - 1)
  have h4 : n + d - 1 + 1 - d = n := by omega
  rw [h4] at h3
  linarith

/-- `N ≥ 1`. -/
theorem NN_ge_one56 (n d : ℕ) : (1 : ℝ) ≤ NN n d := by
  unfold NN
  have : 0 < Fintype.card (Mono n d) := Fintype.card_pos
  exact_mod_cast this

/-- **The cost bound** for large `n`. -/
theorem costLine56_lt (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (εhi : ℝ) (h0 : 0 < εhi)
    (h : εhi ^ 2 < 91 / 200) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      costLine56 n d k < (1 - nuRK εhi) * (91 / 100) * Pn n d / εhi ^ 2 := by
  set e := εhi ^ 2 with he_def
  have he : 0 < e := by positivity
  set γ : ℝ := 91 / (200 * e) - 1 with hγdef
  have hγ : 0 < γ := by
    rw [hγdef, sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have hrhs : ∀ P : ℝ, (1 - nuRK εhi) * (91 / 100) * P / e = (2 + γ) * P := by
    intro P; unfold nuRK; rw [← he_def, hγdef]; field_simp; ring
  set B : ℝ := 4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k with hB
  set F : ℝ := (d.factorial : ℝ) with hF
  have hF0 : 0 < F := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨⌈2 * ((d : ℝ) + 1) / γ⌉₊ + ⌈2 * F * B * 2 ^ k / γ⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (2 * ((d : ℝ) + 1) / γ) < n := by
    have := Nat.le_ceil (2 * ((d : ℝ) + 1) / γ)
    have h' : ((⌈2 * ((d : ℝ) + 1) / γ⌉₊ + ⌈2 * F * B * 2 ^ k / γ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h'
    have : (0 : ℝ) ≤ ⌈2 * F * B * 2 ^ k / γ⌉₊ := Nat.cast_nonneg _
    linarith
  have hn2 : (2 * F * B * 2 ^ k / γ) < n := by
    have := Nat.le_ceil (2 * F * B * 2 ^ k / γ)
    have h' : ((⌈2 * ((d : ℝ) + 1) / γ⌉₊ + ⌈2 * F * B * 2 ^ k / γ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h'
    have : (0 : ℝ) ≤ ⌈2 * ((d : ℝ) + 1) / γ⌉₊ := Nat.cast_nonneg _
    linarith
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn1
  have hn1' : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by
      have h' : ((⌈2 * ((d : ℝ) + 1) / γ⌉₊ + ⌈2 * F * B * 2 ^ k / γ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h'
      have : (0 : ℝ) ≤ ⌈2 * ((d : ℝ) + 1) / γ⌉₊ := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ⌈2 * F * B * 2 ^ k / γ⌉₊ := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
  rw [hrhs, Pn_eq56]
  unfold costLine56
  rw [Pn_eq56]
  set N := NN n d
  have hN1 := NN_ge_one56 n d
  have hNd := NN_ge56 n d hn1'
  -- (a) (d+1) N ≤ (γ/2) n N
  have ha : ((d : ℝ) + 1) * N ≤ γ / 2 * n * N := by
    have : (d : ℝ) + 1 ≤ γ / 2 * n := by
      rw [div_lt_iff₀ hγ] at hn1; nlinarith
    nlinarith
  -- (b) B (n+1)^k < (γ/2) n N
  have hpow1 : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * (n : ℝ) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hpow2 : (n : ℝ) ^ k ≤ (n : ℝ) ^ d := pow_le_pow_right₀ hnr hkd
  have hNk : (n : ℝ) ^ k / F ≤ N := le_trans (div_le_div_of_nonneg_right hpow2 hF0.le) hNd
  have hb : B * ((n : ℝ) + 1) ^ k < γ / 2 * n * N := by
    have hnk : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    have step1 : B * ((n : ℝ) + 1) ^ k ≤ B * 2 ^ k * (n : ℝ) ^ k := by
      have := mul_le_mul_of_nonneg_left hpow1 hB0
      calc B * ((n : ℝ) + 1) ^ k ≤ B * (2 ^ k * (n : ℝ) ^ k) := this
        _ = B * 2 ^ k * (n : ℝ) ^ k := by ring
    have step2 : B * 2 ^ k * (n : ℝ) ^ k < γ / 2 * n * ((n : ℝ) ^ k / F) := by
      rw [div_lt_iff₀ hγ] at hn2
      have : γ / 2 * n * ((n : ℝ) ^ k / F) = (γ * n) * (n : ℝ) ^ k / (2 * F) := by
        field_simp
      rw [this, lt_div_iff₀ (by positivity)]
      nlinarith
    have step3 : γ / 2 * n * ((n : ℝ) ^ k / F) ≤ γ / 2 * n * N :=
      mul_le_mul_of_nonneg_left hNk (by positivity)
    linarith
  have : 4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k = B * ((n : ℝ) + 1) ^ k := by
    rw [hB]
  rw [this]
  nlinarith

end BstLean.Part56
