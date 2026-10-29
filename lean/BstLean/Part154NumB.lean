import BstLean.Part154Event

/-!
# Part 154: the numbers of the centre bounds for `n ≥ 8192` (second half)

The statements `plow_geB`, `epsJ_leB`, `ebo_leB`, `x1_leB`, `x2_leB`; the bounds of `ξ_c` and `b_n`
are hypotheses here.
-/

namespace BstLean.Part154

open Real
open BstLean.Part150 (epsJ alphaJ betaJ alphaJ_nonneg betaJ_nonneg c1F_kappa4_le
  c2F_kappa4_le_4096)
open BstLean.Part153 (wn N22bar N12bar)

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

/-- `p_low ≥ 0.56`. -/
theorem plow_geB {n : ℕ} (hn : 8192 ≤ n) : 56 / 100 ≤ plow n (11 / 1000) := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  unfold plow
  have h1 : (56107 / 100000 : ℝ) ≤ √((1 - 11 / 1000) / π) := by
    apply le_sqrt_of (by norm_num)
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d4]
  have h2 : (1 - 13 / 8192 : ℝ) ≤ 1 - 13 / (n : ℝ) := by
    have : 13 / (n : ℝ) ≤ 13 / 8192 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  calc (56 / 100 : ℝ) ≤ 56107 / 100000 * (1 - 13 / 8192) := by norm_num
    _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (Real.sqrt_nonneg _)

/-- `1 + 2δ_e − (1 − 1/π)(c_s/2)·0.46 ≤ 0.819`. -/
theorem ebo_leB : 1 + 2 * (11 / 1000 : ℝ) - (1 - 1 / π) * (csC / 2) * (46 / 100) ≤ 819 / 1000 := by
  unfold csC
  have h : 1 / π ≤ 1 / 31415 * 10000 := by
    have := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d4.le
    norm_num at this ⊢; linarith
  have hu : (68168 / 100000 : ℝ) ≤ 1 - 1 / π := by
    norm_num at h ⊢; linarith
  have hu2 : (68168 / 100000 : ℝ) * (68168 / 100000) ≤ (1 - 1 / π) * (1 - 1 / π) :=
    mul_le_mul hu hu (by norm_num) (by linarith)
  nlinarith [hu2]

private lemma csC_ge : (129521 / 100000 : ℝ) ≤ csC := by
  unfold csC
  have h := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d6.le
  norm_num at h ⊢; linarith

private lemma T_le {n : ℕ} (hn : 8192 ≤ n) :
    √(16 * 12 * (1 + 11 / 1000) / (n : ℝ)) ≤ 153933 / 1000000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  apply sqrt_le_of (by norm_num)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

private lemma xiNr_le {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (_h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    xiNr n θ (12578 / 10000) ≤ 15106 / 1000000 := by
  obtain ⟨hn', hs, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h5 : √(5 : ℝ) ≤ 22361 / 10000 := sqrt_le_of (by norm_num) (by norm_num)
  have h12 : √(12 : ℝ) ≤ 34642 / 10000 := sqrt_le_of (by norm_num) (by norm_num)
  have hN0 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  have hN : N12bar n 12 ≤ 112 / 100000 := by
    unfold N12bar
    rw [div_le_iff₀ hn0]; linarith
  have hNN : N22bar n 12 ≤ 2242 / 1000000 := by
    unfold N22bar
    calc N12bar n 12 * (2 + N12bar n 12) ≤ 112 / 100000 * (2 + 112 / 100000) :=
          mul_le_mul hN (by linarith) (by linarith) (by norm_num)
      _ ≤ _ := by norm_num
  have hNN0 : 0 ≤ N22bar n 12 := by unfold N22bar; positivity
  have hq : √(12578 / 10000 * θ) ≤ 82491 / 100000 :=
    sqrt_le_of (by norm_num) (by nlinarith)
  have hp : θ * (1 + N22bar n 12) ≤ 541 / 1000 * (1 + 2242 / 1000000) :=
    mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
  unfold xiNr
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `√ξ°_hp ≤ 0.7422`, with `ξ_c ≤ 0.3285` as a hypothesis. -/
theorem x1_leB {n : ℕ} (hn : 8192 ≤ n) {θ ξ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000)
    (_hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3285 / 10000) :
    cD n 12 (11 / 1000) ξ + xiNr n θ (12578 / 10000) ≤ 7422 / 10000 := by
  have hT := T_le hn
  have hx := xiNr_le hn h0 h1
  have hξs : √ξ ≤ 5731492 / 10000000 := sqrt_le_of (by norm_num) (by nlinarith)
  unfold cD
  linarith

/-- `𝖾 ≤ 0.0021`, with `ξ_c ≤ 0.3285` and `b_n ≤ 0.00225` as hypotheses. -/
theorem eMP_leNumB {n : ℕ} (hn : 8192 ≤ n) {ξ b : ℝ}
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3285 / 10000) (hb0 : 0 ≤ b) (hb : b ≤ 225 / 100000) :
    0 ≤ eMP n (11 / 1000) ξ b ∧ eMP n (11 / 1000) ξ b ≤ 21 / 10000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  unfold eMP
  rw [h989]
  refine ⟨by positivity, ?_⟩
  have hπb : π * b ≤ 3.1416 * (225 / 100000) := mul_le_mul hπ.le hb hb0 (by norm_num)
  have hπξ : π * ξ ≤ 3.1416 * (3285 / 10000) := mul_le_mul hπ.le hξ hξ0 (by norm_num)
  have e1 : √(π * b / (n * (989 / 1000))) ≤ 94 / 100000 := by
    apply sqrt_le_of (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    norm_num at hπb ⊢; nlinarith
  have e2 : π * ξ / (n * (989 / 1000)) ≤ 13 / 100000 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num at hπξ ⊢; nlinarith
  linarith

/-- `√ξ°_∥ ≤ 0.2270`, with `ξ_c ≤ 0.3285` and `b_n ≤ 0.00225` as hypotheses. -/
theorem x2_leB {n : ℕ} (hn : 8192 ≤ n) {θ ξ b : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000)
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3285 / 10000) (hb0 : 0 ≤ b) (hb : b ≤ 225 / 100000) :
    LamMP n 12 (11 / 1000) ξ b + xiNr n θ (12578 / 10000) ≤ 2270 / 10000 := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hx := xiNr_le hn h0 h1
  have hp := plow_geB hn
  have hT := T_le hn
  have hT0 := Real.sqrt_nonneg (16 * 12 * (1 + 11 / 1000) / (n : ℝ))
  obtain ⟨he0, he⟩ := eMP_leNumB hn hξ0 hξ hb0 hb
  have hξs : √ξ ≤ 57315 / 100000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hξs0 := Real.sqrt_nonneg ξ
  have hc0 : 0 ≤ cD n 12 (11 / 1000) ξ := by unfold cD; positivity
  have hc : cD n 12 (11 / 1000) ξ ≤ 7271 / 10000 := by unfold cD; linarith
  -- `Π̄`
  have hA : √b ≤ 47435 / 1000000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hA0 := Real.sqrt_nonneg b
  have hsp : √π ≤ 17725 / 10000 :=
    sqrt_le_of (by norm_num) (by nlinarith [Real.pi_lt_d4])
  have hsp0 := Real.sqrt_nonneg π
  have hR : (90 : ℝ) ≤ √((n : ℝ) * (1 - 11 / 1000)) := by
    apply le_sqrt_of (by norm_num)
    rw [h989]; nlinarith
  have hB0 : 0 ≤ ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000))) := by positivity
  have hB : ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000))) ≤ 324 / 100000 := by
    rw [div_le_iff₀ (by linarith)]
    have : ξ * √π ≤ 3285 / 10000 * (17725 / 10000) := mul_le_mul hξ hsp hsp0 (by norm_num)
    nlinarith
  have h8 : 8 / ((n : ℝ) * √(n : ℝ)) ≤ 11 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    have : (8192 : ℝ) * (90509 / 1000) ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul hn' hs (by norm_num) hn0.le
    nlinarith
  have hP0 : 0 ≤ PiBarMP n 12 (11 / 1000) ξ b := by unfold PiBarMP; positivity
  have hP : PiBarMP n 12 (11 / 1000) ξ b ≤ 20474 / 100000 := by
    unfold PiBarMP
    have : (√b + ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000)))) * (1 + eMP n (11 / 1000) ξ b) ≤
        (47435 / 1000000 + 324 / 100000) * (1 + 21 / 10000) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    linarith
  -- the denominator
  have hD : (10137 / 100 : ℝ) ≤ 2 * plow n (11 / 1000) * √(n : ℝ) := by
    have : (56 / 100 : ℝ) * (90509 / 1000) ≤ plow n (11 / 1000) * √(n : ℝ) :=
      mul_le_mul hp hs (by norm_num) (by linarith)
    nlinarith
  have hD0 : (0 : ℝ) < 2 * plow n (11 / 1000) * √(n : ℝ) := by linarith
  have hς0 : 0 ≤ cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ)) :=
    div_nonneg hc0 hD0.le
  have hς : cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ)) ≤ 718 / 100000 := by
    rw [div_le_iff₀ hD0]; nlinarith
  have hc2 : cD n 12 (11 / 1000) ξ ^ 2 / (2 * plow n (11 / 1000) * √(n : ℝ)) ≤ 522 / 100000 := by
    rw [div_le_iff₀ hD0]
    have : cD n 12 (11 / 1000) ξ ^ 2 ≤ (7271 / 10000) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    nlinarith
  have hL : (1 + cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ))) *
      PiBarMP n 12 (11 / 1000) ξ b ≤ (1 + 718 / 100000) * (20474 / 100000) :=
    mul_le_mul (by linarith) hP hP0 (by norm_num)
  unfold LamMP
  linarith

private lemma term {n s α a X k : ℝ} (hs : 0 < s) (hsq : s ^ 2 = n) (hα0 : 0 ≤ α)
    (hα : α ≤ a / n) (hX : X ≤ k * s) (hk : 0 ≤ k) : α * X ≤ a * k * (1 / s) := by
  have hks : 0 ≤ k * s := by positivity
  calc α * X ≤ α * (k * s) := mul_le_mul_of_nonneg_left hX hα0
    _ ≤ a / n * (k * s) := mul_le_mul_of_nonneg_right hα hks
    _ = a * k * (1 / s) := by rw [← hsq]; field_simp

private lemma ab_le {n : ℕ} (hn : 8192 ≤ n) :
    alphaJ n ≤ (1792 / 10000) / n ∧ betaJ n ≤ (81 / 1000) / n ∧ alphaJ n ≤ 22 / 1000000 ∧
      betaJ n ≤ 1 / 100000 ∧ betaJ n + alphaJ n ^ 2 ≤ (81004 / 1000000) / n := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha0 : 0 ≤ alphaJ n := alphaJ_nonneg n
  have ha : alphaJ n ≤ (1792 / 10000) / n := by
    unfold alphaJ
    exact div_le_div_of_nonneg_right (c1F_kappa4_le (by omega)) hn0.le
  have hb : betaJ n ≤ (81 / 1000) / n := by
    unfold betaJ
    exact div_le_div_of_nonneg_right (c2F_kappa4_le_4096 (by omega)) hn0.le
  have hinvn : 1 / (n : ℝ) ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hn'
  have hinvn0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have e2 : (81004 / 1000000 : ℝ) / n = 81004 / 1000000 * (1 / n) := by ring
  have e3 : (81 / 1000 : ℝ) / n = 81 / 1000 * (1 / n) := by ring
  have e4 : (1792 / 10000 : ℝ) / n = 1792 / 10000 * (1 / n) := by ring
  have hb' : betaJ n ≤ 1 / 100000 := by linarith
  have ha' : alphaJ n ≤ 22 / 1000000 := by linarith
  refine ⟨ha, hb, ha', hb', ?_⟩
  have e1 : alphaJ n ^ 2 ≤ 22 / 1000000 * ((1792 / 10000) / n) := by
    rw [sq]; exact mul_le_mul ha' ha ha0 (by norm_num)
  rw [e4] at e1; rw [e3] at hb; rw [e2]
  linarith

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

private lemma deltaChi_le {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ deltaChi n 12 ∧ deltaChi n 12 ≤ 85 / 100000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hinvn : 1 / (n : ℝ) ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hn'
  have hinvn0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have h12 : √(12 : ℝ) ≤ 34642 / 10000 := sqrt_le_of (by norm_num) (by norm_num)
  unfold deltaChi
  refine ⟨by positivity, ?_⟩
  have e1 : 2 * √(12 : ℝ) / n ≤ 2 * (34642 / 10000) * (1 / 8192) := by
    have : 2 * √(12 : ℝ) / n = 2 * √(12 : ℝ) * (1 / n) := by ring
    rw [this]
    exact mul_le_mul (by linarith) hinvn hinvn0 (by norm_num)
  have e2 : 2 * 12 / (n : ℝ) ^ 2 ≤ 24 * (1 / 8192) ^ 2 := by
    have : 2 * 12 / (n : ℝ) ^ 2 = 24 * (1 / n) ^ 2 := by ring
    rw [this]
    have : (1 / (n : ℝ)) ^ 2 ≤ (1 / 8192) ^ 2 := pow_le_pow_left₀ hinvn0 hinvn 2
    linarith
  have e3 : (2 * (34642 / 10000) * (1 / 8192) + 24 * (1 / 8192) ^ 2 : ℝ) ≤ 85 / 100000 := by
    norm_num
  linarith

private lemma two_div_pi_le : 2 / π ≤ 63662 / 100000 := by
  have h := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d6.le
  have h3 : (1 : ℝ) / 3.141592 ≤ 31831 / 100000 := by norm_num
  have e : 2 / π = 2 * (1 / π) := by ring
  rw [e]; linarith

private lemma root1 {n : ℕ} (hn : 8192 ≤ n) :
    √(2 * (1 + 11 / 1000) * (1 + 2 * wn n * betaJ n) * n) ≤ 142199 / 100000 * √(n : ℝ) := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hw0, hw⟩ := wn_le hn
  obtain ⟨-, -, -, hb', -⟩ := ab_le hn
  have hb0 : 0 ≤ betaJ n := betaJ_nonneg n
  have hwb : wn n * betaJ n ≤ 1044683 / 1000000 * (1 / 100000) :=
    mul_le_mul hw hb' hb0 (by norm_num)
  apply sqrt_le_of (by positivity)
  rw [mul_pow, hsq]
  have : 2 * (1 + 11 / 1000) * (1 + 2 * wn n * betaJ n) ≤ (142199 / 100000 : ℝ) ^ 2 := by
    have e : (2 * (1 + 11 / 1000) * (1 + 2 * (1044683 / 1000000 * (1 / 100000))) : ℝ) ≤
        (142199 / 100000 : ℝ) ^ 2 := by norm_num
    nlinarith
  exact mul_le_mul_of_nonneg_right this hn0.le

private lemma root2 {n : ℕ} (hn : 8192 ≤ n) :
    √(2 * (1 + 11 / 1000) * wn n * n * (1 + deltaChi n 12 + 2 / π) / csC) ≤
      163419 / 100000 * √(n : ℝ) := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hw0, hw⟩ := wn_le hn
  obtain ⟨hd0, hd⟩ := deltaChi_le hn
  have hpi := two_div_pi_le
  have hpi0 : 0 ≤ 2 / π := by positivity
  have hcs := csC_ge
  have hcs0 : 0 < csC := by linarith
  have hq : wn n * (1 + deltaChi n 12 + 2 / π) ≤
      1044683 / 1000000 * (1 + 85 / 100000 + 63662 / 100000) :=
    mul_le_mul hw (by linarith) (by linarith) (by norm_num)
  apply sqrt_le_of (by positivity)
  rw [mul_pow, hsq, div_le_iff₀ hcs0]
  have e : (2 * (1 + 11 / 1000) * (1044683 / 1000000 * (1 + 85 / 100000 + 63662 / 100000)) : ℝ) ≤
      (163419 / 100000 : ℝ) ^ 2 * (129521 / 100000) := by norm_num
  have e' : (163419 / 100000 : ℝ) ^ 2 * (129521 / 100000) ≤ (163419 / 100000 : ℝ) ^ 2 * csC :=
    mul_le_mul_of_nonneg_left hcs (by norm_num)
  have h : 2 * (1 + 11 / 1000) * (wn n * (1 + deltaChi n 12 + 2 / π)) ≤
      (163419 / 100000 : ℝ) ^ 2 * csC := by linarith
  have := mul_le_mul_of_nonneg_right h hn0.le
  calc 2 * (1 + 11 / 1000) * wn n * n * (1 + deltaChi n 12 + 2 / π)
      = 2 * (1 + 11 / 1000) * (wn n * (1 + deltaChi n 12 + 2 / π)) * n := by ring
    _ ≤ (163419 / 100000 : ℝ) ^ 2 * csC * n := this
    _ = _ := by ring

private lemma root3 {n : ℕ} (hn : 8192 ≤ n) :
    4 * (1 / √(2 * π)) * wn n * √((n : ℝ) / csC) ≤ 14649 / 10000 * √(n : ℝ) := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  obtain ⟨hw0, hw⟩ := wn_le hn
  have hcs := csC_ge
  have hcs0 : 0 < csC := by linarith
  have h3 : √((n : ℝ) / csC) ≤ 87869 / 100000 * √(n : ℝ) := by
    apply sqrt_le_of (by positivity)
    rw [mul_pow, hsq, div_le_iff₀ hcs0]
    have e : (1 : ℝ) ≤ (87869 / 100000 : ℝ) ^ 2 * (129521 / 100000) := by norm_num
    have e' : (87869 / 100000 : ℝ) ^ 2 * (129521 / 100000) ≤ (87869 / 100000 : ℝ) ^ 2 * csC :=
      mul_le_mul_of_nonneg_left hcs (by norm_num)
    have := mul_le_mul_of_nonneg_right (e.trans e') hn0.le
    calc (n : ℝ) = 1 * n := by ring
      _ ≤ (87869 / 100000 : ℝ) ^ 2 * csC * n := this
      _ = _ := by ring
  have h30 := Real.sqrt_nonneg ((n : ℝ) / csC)
  have hisp : 1 / √(2 * π) ≤ 39895 / 100000 := by
    have h : (25066 / 10000 : ℝ) ≤ √(2 * π) :=
      le_sqrt_of (by norm_num) (by nlinarith [Real.pi_gt_d6])
    have h' := one_div_le_one_div_of_le (by norm_num) h
    have e : (1 : ℝ) / (25066 / 10000) ≤ 39895 / 100000 := by norm_num
    linarith
  have hisp0 : 0 ≤ 1 / √(2 * π) := by positivity
  have e1 : 4 * (1 / √(2 * π)) * wn n ≤ 4 * (39895 / 100000) * (1044683 / 1000000) :=
    mul_le_mul (by linarith) hw hw0 (by norm_num)
  have e2 : (4 * (39895 / 100000) * (1044683 / 1000000) * (87869 / 100000) : ℝ) ≤
      14649 / 10000 := by norm_num
  calc 4 * (1 / √(2 * π)) * wn n * √((n : ℝ) / csC)
      ≤ 4 * (39895 / 100000) * (1044683 / 1000000) * (87869 / 100000 * √(n : ℝ)) :=
        mul_le_mul e1 h3 h30 (by norm_num)
    _ = 4 * (39895 / 100000) * (1044683 / 1000000) * (87869 / 100000) * √(n : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right e2 hs0.le

/-- `ϵ_J ≤ 0.0106` for `J = n` atoms. -/
theorem epsJ_leB {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ∧
    epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ 106 / 10000 := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have ha0 : 0 ≤ alphaJ n := alphaJ_nonneg n
  have hb0 : 0 ≤ betaJ n := betaJ_nonneg n
  obtain ⟨ha, -, -, -, hg⟩ := ab_le hn
  have hg0 : 0 ≤ betaJ n + alphaJ n ^ 2 := by positivity
  obtain ⟨hw0, -⟩ := wn_le hn
  obtain ⟨hd0, -⟩ := deltaChi_le hn
  have hcs0 : 0 < csC := by linarith [csC_ge]
  have hinvs : 1 / √(n : ℝ) ≤ 1000 / 90509 := by
    have h := one_div_le_one_div_of_le (by norm_num) hs
    have h3 : (1 : ℝ) / (90509 / 1000) = 1000 / 90509 := by norm_num
    linarith
  have t1 := term hs0 hsq ha0 ha (root1 hn) (by norm_num)
  have t2 := term hs0 hsq ha0 ha (root2 hn) (by norm_num)
  have t3 := term hs0 hsq hg0 hg (root3 hn) (by norm_num)
  unfold epsJ
  refine ⟨by positivity, ?_⟩
  have e : alphaJ n * √(2 * (1 + 11 / 1000) * (1 + 2 * wn n * betaJ n) * n) +
      2 * alphaJ n * √(2 * (1 + 11 / 1000) * wn n * n * (1 + deltaChi n 12 + 2 / π) / csC) +
      4 * (1 / √(2 * π)) * wn n * √((n : ℝ) / csC) * (betaJ n + alphaJ n ^ 2) =
      alphaJ n * √(2 * (1 + 11 / 1000) * (1 + 2 * wn n * betaJ n) * n) +
      2 * (alphaJ n * √(2 * (1 + 11 / 1000) * wn n * n * (1 + deltaChi n 12 + 2 / π) / csC)) +
      (betaJ n + alphaJ n ^ 2) * (4 * (1 / √(2 * π)) * wn n * √((n : ℝ) / csC)) := by ring
  rw [e]
  have c : (1792 / 10000 * (142199 / 100000) + 2 * (1792 / 10000 * (163419 / 100000)) +
      81004 / 1000000 * (14649 / 10000) : ℝ) * (1000 / 90509) ≤ 106 / 10000 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hinvs (by norm_num : (0 : ℝ) ≤
    1792 / 10000 * (142199 / 100000) + 2 * (1792 / 10000 * (163419 / 100000)) +
      81004 / 1000000 * (14649 / 10000))]

end BstLean.Part154
