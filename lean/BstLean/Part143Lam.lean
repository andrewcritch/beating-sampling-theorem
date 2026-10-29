import BstLean.Part140Frame

/-!
# Part 143 (helper `lam16`), step 1: the frame bound of the computed centre for `n ≥ 16384`

`frameHat143`: for every `n ≥ 16384` and `θ ∈ goodHat n`, `E_u ⟨ê(u), w⟩² ≤ (L143/n)·|w|²` with
`L143 = 137/100` (Part 140 has `183/100` for every `n ≥ 4096`). The proof is the proof of
`frameHat140` with `frameB_num` called at `n₀ = 16384`: `r₀ = 2⁻²¹`, `k₀ = 16323/5000000`,
`k₆ = 53489/5000000`, `ε₁ = 13/1250`, `ε₂ = 47/5000`, `s = 46207/100000`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (BM sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part140

/-- The frame constant of the computed centre for `n ≥ 16384`. -/
noncomputable def L143 : ℝ := 137 / 100

lemma L143_nonneg : 0 ≤ L143 := by unfold L143; norm_num

/-- **The frame bound for the computed centre, `n ≥ 16384`**: `E_u ⟨ê(u), w⟩² ≤ (1.37/n)·|w|²`. -/
theorem frameHat143 {n : ℕ} (hn16 : 16384 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ goodHat n) (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      L143 / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn : 4096 ≤ n := by omega
  unfold L143
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have := uniformSphere_isProbability (2 * n) hN
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  obtain ⟨hBl, -⟩ := Bh_hat hn hθ
  obtain ⟨b, hb0, hb1, hmodel⟩ := kk_three
  -- the three hypotheses on the centre
  have hξ : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 ≤
      (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * ((3 / 8) / (n : ℝ)) := by
    have hd : dist2 (2 * n) (mW n) θ ≤
        2 / ((2 * n : ℕ) : ℝ) * (3 / 4 / ((2 * n : ℕ) : ℝ)) := hθ.1.2
    have e : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 =
        normSq (bhat θ - hbarW θ) := by
      rw [normSq_sub_comm]
      rfl
    rw [e]
    unfold dist2 at hd
    rw [hNcast] at hd ⊢
    have h1 : normSq (bhat θ - hbarW θ) ≤
        (mW n : ℝ) / 2 * (2 / (2 * (n : ℝ)) * (3 / 4 / (2 * (n : ℝ)))) := by
      have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
      have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ - hbarW θ)) =
          normSq (bhat θ - hbarW θ) := by field_simp
      linarith
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  have hX : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j -
        (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 ∂uniformSphere (2 * n) ≤
      ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 * ((1 / 400000) / (n : ℝ)) := by
    have hT : (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) := hθ.2
    have e : ∀ u : Fin (2 * n) → ℝ, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j -
        (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 =
        ((mW n : ℝ) / 2) ^ 2 *
          (That (2 * n) (mW n) u θ - 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 := by
      intro u
      have e1 : That (2 * n) (mW n) u θ =
          2 / (mW n : ℝ) * ∑ j, hid2 θ.1 θ.2 u j * bhat θ j := rfl
      rw [e1]
      field_simp
    simp_rw [e]
    rw [integral_const_mul]
    change ((mW n : ℝ) / 2) ^ 2 * errT θ ≤ _
    have h1 : errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      linarith
    refine (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans (le_of_eq ?_)
    rw [hNcast]
    field_simp
  have hβb : (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ normSq (bhat θ) := by
    unfold Bh at hBl
    rw [hNcast] at hBl ⊢
    have := mul_le_mul_of_nonneg_left hBl (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
    have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ)) = normSq (bhat θ) := by
      field_simp
    have e3 : (mW n : ℝ) / 2 * (2 / (2 * (n : ℝ)) * (48 / 100)) =
        (mW n : ℝ) / (2 * (n : ℝ)) * (48 / 100) := by field_simp
    linarith
  have hsle : (46207 : ℝ) / 100000 ≤
      1 - 13 / 1250 - (kap1 (2 * n) + 47 / 5000) ^ 2 / (48 / 100) := by
    have h1 : (kap1 (2 * n) + 47 / 5000) ^ 2 ≤ (4938 / 10000 + 47 / 5000) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (kap1 (2 * n) + 47 / 5000) ^ 2 / (48 / 100) ≤
        (4938 / 10000 + 47 / 5000) ^ 2 / (48 / 100) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h3 : (4938 / 10000 + 47 / 5000 : ℝ) ^ 2 / (48 / 100) ≤ 527529 / 1000000 := by norm_num
    linarith
  exact frameB_num (n := n) (n0 := 16384) (by norm_num) hn16 (b := b) (c2 := 138 / 1000)
    (η := 1 / 1000) (K₃ := 2 / 5) (r0 := 1 / 2097152) (k0 := 16323 / 5000000)
    (k6 := 53489 / 5000000) (sp := 4 / 100) (ε₁ := 13 / 1250) (ε₂ := 47 / 5000)
    (s := 46207 / 100000)
    (p₂ := 4 / 10000) (D0 := 8676017 / 100000000) (C := 137 / 100) (ξ₀ := 3 / 8)
    (a := kap1 (2 * n)) (dT := 1 / 400000) (β := 48 / 100)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) hsle (by norm_num) hθ.1.1 hξ hX hβb w

end BstLean.Part143

open BstLean.Part143 in
#print axioms frameHat143
