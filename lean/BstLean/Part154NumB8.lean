import BstLean.Part154NumB

/-!
# Part 154: the numbers of the centre bounds for `n ≥ 8192`, `0.457 ≤ θ ≤ 0.555`,
`M_P = 1.2578`

The bounds of `ξ_c` and `b_n` are hypotheses here.
-/

namespace BstLean.Part154

open Real
open BstLean.Part153 (wn N22bar N12bar N14bar N24bar x4n x4n_le x4n_nonneg)

private lemma sqrt_le_of {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  Real.sqrt_le_iff.mpr ⟨hy, h⟩

private lemma le_sqrt_of {x y : ℝ} (hx : 0 < x) (h : x ^ 2 ≤ y) : x ≤ √y :=
  (Real.le_sqrt' hx).mpr h

private lemma sqrt_n {n : ℕ} (hn : 8192 ≤ n) :
    (8192 : ℝ) ≤ n ∧ (90509 / 1000 : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) ^ 2 = n := by
  have h : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨h, ?_, Real.sq_sqrt (by linarith)⟩
  apply le_sqrt_of (by norm_num)
  norm_num; linarith

private lemma h989 : (1 - 11 / 1000 : ℝ) = 989 / 1000 := by norm_num

/-- `1 + 2δ_e − (1 − 1/π)(c_s/2)·0.457 ≤ 0.8203`. -/
theorem ebo_leB8 :
    1 + 2 * (11 / 1000 : ℝ) - (1 - 1 / π) * (csC / 2) * (457 / 1000) ≤ 8203 / 10000 := by
  unfold csC
  have h := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d4.le
  have h3 : (1 : ℝ) / 3.1415 ≤ 31832 / 100000 := by norm_num
  have hu : (68168 / 100000 : ℝ) ≤ 1 - 1 / π := by linarith
  have hu2 : (68168 / 100000 : ℝ) * (68168 / 100000) ≤ (1 - 1 / π) * (1 - 1 / π) :=
    mul_le_mul hu hu (by norm_num) (by linarith)
  nlinarith [hu2]

private lemma T_le {n : ℕ} (hn : 8192 ≤ n) :
    √(16 * 12 * (1 + 11 / 1000) / (n : ℝ)) ≤ 153933 / 1000000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  apply sqrt_le_of (by norm_num)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

private lemma wn_le {n : ℕ} (hn : 8192 ≤ n) : 0 ≤ wn n ∧ wn n ≤ 1044683 / 1000000 := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hinvs : 1 / √(n : ℝ) ≤ 1000 / 90509 := by
    have h := one_div_le_one_div_of_le (by norm_num) hs
    have h3 : (1 : ℝ) / (90509 / 1000) = 1000 / 90509 := by norm_num
    linarith
  unfold wn
  refine ⟨by positivity, ?_⟩
  have h2 : 2 / √(n : ℝ) ≤ 2000 / 90509 := by
    have : 2 / √(n : ℝ) = 2 * (1 / √(n : ℝ)) := by ring
    linarith
  have h20 : 0 ≤ 2 / √(n : ℝ) := by positivity
  calc (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2000 / 90509) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
    _ ≤ _ := by norm_num

/-- `N̄₂₂ ≤ 18.340/n`, `N̄₂₄ ≤ 24.779/n`. -/
theorem Nbar_leB8 {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ N22bar n 12 ∧ N22bar n 12 ≤ 18340 / 1000 / (n : ℝ) ∧
    0 ≤ N24bar n 12 ∧ N24bar n 12 ≤ 24779 / 1000 / (n : ℝ) := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have ht : 1 / (n : ℝ) ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hn'
  have h5 : √(5 : ℝ) ≤ 223607 / 100000 := sqrt_le_of (by norm_num) (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3464102 / 1000000 := sqrt_le_of (by norm_num) (by norm_num)
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have h120 := Real.sqrt_nonneg (12 : ℝ)
  have hx := x4n_le (n := n) (by omega)
  have hx0 := x4n_nonneg n
  obtain ⟨hw0, hw⟩ := wn_le hn
  have e12 : N12bar n 12 = (√5 + 2 * √12) * (1 / (n : ℝ)) := by unfold N12bar; ring
  have hN0 : 0 ≤ N12bar n 12 := by rw [e12]; positivity
  have hN : N12bar n 12 ≤ 9164274 / 1000000 * (1 / (n : ℝ)) := by
    rw [e12]; exact mul_le_mul_of_nonneg_right (by linarith) ht0
  have hN' : N12bar n 12 ≤ 9164274 / 1000000 * (1 / 8192) := by linarith
  have h22 : N22bar n 12 ≤ 18340 / 1000 / (n : ℝ) := by
    unfold N22bar
    calc N12bar n 12 * (2 + N12bar n 12)
        ≤ 9164274 / 1000000 * (1 / (n : ℝ)) * (2 + 9164274 / 1000000 * (1 / 8192)) :=
          mul_le_mul hN (by linarith) (by linarith) (by positivity)
      _ = 9164274 / 1000000 * (2 + 9164274 / 1000000 * (1 / 8192)) * (1 / (n : ℝ)) := by ring
      _ ≤ 18340 / 1000 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) ht0
      _ = _ := by ring
  have h220 : 0 ≤ N22bar n 12 := by unfold N22bar; positivity
  have e14 : N14bar n 12 = (x4n n + 2 * √12) * (1 / (n : ℝ)) := by unfold N14bar; ring
  have hM0 : 0 ≤ N14bar n 12 := by rw [e14]; positivity
  have hM : N14bar n 12 ≤ 99284 / 10000 * (1 / (n : ℝ)) := by
    rw [e14]; exact mul_le_mul_of_nonneg_right (by linarith) ht0
  have hM' : N14bar n 12 ≤ 122 / 100000 := by linarith
  have hq : √(2 * 12 * wn n) ≤ 50073 / 10000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hq0 := Real.sqrt_nonneg (2 * 12 * wn n)
  have hp : x4n n * (1 + N14bar n 12) ≤ 3 * (1 + 122 / 100000) :=
    mul_le_mul hx (by linarith) (by linarith) (by norm_num)
  have hp0 : 0 ≤ x4n n * (1 + N14bar n 12) := by positivity
  have e24 : N24bar n 12 = x4n n * (1 + N14bar n 12) * (1 / (n : ℝ)) + N14bar n 12 +
      2 * √(2 * 12 * wn n) * (1 / (n : ℝ)) := by unfold N24bar; ring
  have a1 : x4n n * (1 + N14bar n 12) * (1 / (n : ℝ)) ≤ 3 * (1 + 122 / 100000) * (1 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hp ht0
  have a3 : 2 * √(2 * 12 * wn n) * (1 / (n : ℝ)) ≤ 2 * (50073 / 10000) * (1 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) ht0
  have e : (24779 / 1000 : ℝ) / n = 24779 / 1000 * (1 / (n : ℝ)) := by ring
  refine ⟨h220, h22, ?_, ?_⟩
  · rw [e24]; positivity
  · rw [e24, e]; linarith

private lemma xiNr_le {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h1 : θ ≤ 555 / 1000) :
    xiNr n θ (12578 / 10000) ≤ 15378 / 1000000 := by
  obtain ⟨hn', hs, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hNN0, hNN', -, -⟩ := Nbar_leB8 hn
  have ht : 1 / (n : ℝ) ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hn'
  have hNN : N22bar n 12 ≤ 2239 / 1000000 := by
    have e : (18340 / 1000 : ℝ) / n = 18340 / 1000 * (1 / (n : ℝ)) := by ring
    rw [e] at hNN'; linarith
  have hq : √(12578 / 10000 * θ) ≤ 835512 / 1000000 :=
    sqrt_le_of (by norm_num) (by nlinarith)
  have hp : θ * (1 + N22bar n 12) ≤ 555 / 1000 * (1 + 2239 / 1000000) :=
    mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
  unfold xiNr
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `√ξ°_hp ≤ 0.7500`, with `ξ_c ≤ 0.3370` as a hypothesis. -/
theorem x1_leB8 {n : ℕ} (hn : 8192 ≤ n) {θ ξ : ℝ} (_h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000)
    (_hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3370 / 10000) :
    cD n 12 (11 / 1000) ξ + xiNr n θ (12578 / 10000) ≤ 7500 / 10000 := by
  have hT := T_le hn
  have hx := xiNr_le hn h1
  have hξs : √ξ ≤ 580518 / 1000000 := sqrt_le_of (by norm_num) (by nlinarith)
  unfold cD
  linarith

private lemma eMP_le' {n : ℕ} (hn : 8192 ≤ n) {ξ b : ℝ}
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3370 / 10000) (hb0 : 0 ≤ b) (hb : b ≤ 231 / 100000) :
    0 ≤ eMP n (11 / 1000) ξ b ∧ eMP n (11 / 1000) ξ b ≤ 21 / 10000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  unfold eMP
  rw [h989]
  refine ⟨by positivity, ?_⟩
  have hπb : π * b ≤ 3.1416 * (231 / 100000) := mul_le_mul hπ.le hb hb0 (by norm_num)
  have hπξ : π * ξ ≤ 3.1416 * (3370 / 10000) := mul_le_mul hπ.le hξ hξ0 (by norm_num)
  have e1 : √(π * b / (n * (989 / 1000))) ≤ 95 / 100000 := by
    apply sqrt_le_of (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    norm_num at hπb ⊢; nlinarith
  have e2 : π * ξ / (n * (989 / 1000)) ≤ 14 / 100000 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num at hπξ ⊢; nlinarith
  linarith

/-- `𝖾 ≤ 0.1` (in fact `≤ 0.0021`). -/
theorem eMP_leNumB8 {n : ℕ} (hn : 8192 ≤ n) {ξ b : ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3370 / 10000)
    (hb0 : 0 ≤ b) (hb : b ≤ 231 / 100000) : eMP n (11 / 1000) ξ b ≤ 1 / 10 := by
  have := (eMP_le' hn hξ0 hξ hb0 hb).2
  linarith

/-- `√ξ°_∥ ≤ 0.2280`, with `ξ_c ≤ 0.3370` and `b_n ≤ 0.00231` as hypotheses. -/
theorem x2_leB8 {n : ℕ} (hn : 8192 ≤ n) {θ ξ b : ℝ} (_h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000)
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3370 / 10000) (hb0 : 0 ≤ b) (hb : b ≤ 231 / 100000) :
    LamMP n 12 (11 / 1000) ξ b + xiNr n θ (12578 / 10000) ≤ 2280 / 10000 := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hx := xiNr_le hn h1
  have hp := plow_geB hn
  have hT := T_le hn
  have hT0 := Real.sqrt_nonneg (16 * 12 * (1 + 11 / 1000) / (n : ℝ))
  obtain ⟨he0, he⟩ := eMP_le' hn hξ0 hξ hb0 hb
  have hξs : √ξ ≤ 580518 / 1000000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hξs0 := Real.sqrt_nonneg ξ
  have hc0 : 0 ≤ cD n 12 (11 / 1000) ξ := by unfold cD; positivity
  have hc : cD n 12 (11 / 1000) ξ ≤ 73446 / 100000 := by unfold cD; linarith
  have hA : √b ≤ 48063 / 1000000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hA0 := Real.sqrt_nonneg b
  have hsp : √π ≤ 17725 / 10000 :=
    sqrt_le_of (by norm_num) (by nlinarith [Real.pi_lt_d4])
  have hsp0 := Real.sqrt_nonneg π
  have hR : (90 : ℝ) ≤ √((n : ℝ) * (1 - 11 / 1000)) := by
    apply le_sqrt_of (by norm_num)
    rw [h989]; nlinarith
  have hB0 : 0 ≤ ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000))) := by positivity
  have hB : ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000))) ≤ 332 / 100000 := by
    rw [div_le_iff₀ (by linarith)]
    have : ξ * √π ≤ 3370 / 10000 * (17725 / 10000) := mul_le_mul hξ hsp hsp0 (by norm_num)
    nlinarith
  have h8 : 8 / ((n : ℝ) * √(n : ℝ)) ≤ 11 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    have : (8192 : ℝ) * (90509 / 1000) ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul hn' hs (by norm_num) hn0.le
    nlinarith
  have hP0 : 0 ≤ PiBarMP n 12 (11 / 1000) ξ b := by unfold PiBarMP; positivity
  have hP : PiBarMP n 12 (11 / 1000) ξ b ≤ 20544 / 100000 := by
    unfold PiBarMP
    have : (√b + ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000)))) * (1 + eMP n (11 / 1000) ξ b) ≤
        (48063 / 1000000 + 332 / 100000) * (1 + 21 / 10000) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    linarith
  have hD : (10137 / 100 : ℝ) ≤ 2 * plow n (11 / 1000) * √(n : ℝ) := by
    have : (56 / 100 : ℝ) * (90509 / 1000) ≤ plow n (11 / 1000) * √(n : ℝ) :=
      mul_le_mul hp hs (by norm_num) (by linarith)
    nlinarith
  have hD0 : (0 : ℝ) < 2 * plow n (11 / 1000) * √(n : ℝ) := by linarith
  have hς0 : 0 ≤ cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ)) :=
    div_nonneg hc0 hD0.le
  have hς : cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ)) ≤ 725 / 100000 := by
    rw [div_le_iff₀ hD0]; nlinarith
  have hc2 : cD n 12 (11 / 1000) ξ ^ 2 / (2 * plow n (11 / 1000) * √(n : ℝ)) ≤ 533 / 100000 := by
    rw [div_le_iff₀ hD0]
    have : cD n 12 (11 / 1000) ξ ^ 2 ≤ (73446 / 100000) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    nlinarith
  have hL : (1 + cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ))) *
      PiBarMP n 12 (11 / 1000) ξ b ≤ (1 + 725 / 100000) * (20544 / 100000) :=
    mul_le_mul (by linarith) hP hP0 (by norm_num)
  unfold LamMP
  linarith

end BstLean.Part154
