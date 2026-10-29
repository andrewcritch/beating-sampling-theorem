import BstLean.Part187All
import BstLean.Part154NumB16
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final





namespace BstLean.Part188.Base154_R
open BstLean.Part154 BstLean.Part154.R

open Real
open BstLean.Part150 (epsJ alphaJ betaJ alphaJ_nonneg betaJ_nonneg c1F_kappa4_le
  c2F_kappa4_le_4096)
open BstLean.Part153 (wn N22bar N12bar N14bar N24bar x4n x4n_le x4n_nonneg)

private lemma sqrt_le_of {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  Real.sqrt_le_iff.mpr ⟨hy, h⟩

private lemma le_sqrt_of {x y : ℝ} (hx : 0 < x) (h : x ^ 2 ≤ y) : x ≤ √y :=
  (Real.le_sqrt' hx).mpr h

private lemma sqrt_n {n : ℕ} (hn : 16200 ≤ n) :
    (16200 : ℝ) ≤ n ∧ (127 : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) ^ 2 = n := by
  have h : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨h, ?_, Real.sq_sqrt (by linarith)⟩
  apply le_sqrt_of (by norm_num)
  norm_num; linarith

private lemma h989 : (1 - 11 / 1000 : ℝ) = 989 / 1000 := by norm_num

/-- `p_low ≥ 0.56`. -/
theorem plow_geB16 {n : ℕ} (hn : 16200 ≤ n) : 56 / 100 ≤ plow n (11 / 1000) :=
  plow_geB (by omega)

private lemma csC_ge : (129521 / 100000 : ℝ) ≤ csC := by
  unfold csC
  have h := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d6.le
  norm_num at h ⊢; linarith

private lemma T_le {n : ℕ} (hn : 16200 ≤ n) :
    √(16 * 12 * (1 + 11 / 1000) / (n : ℝ)) ≤ 109465 / 1000000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  apply sqrt_le_of (by norm_num)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

private lemma wn_le {n : ℕ} (hn : 16200 ≤ n) : 0 ≤ wn n ∧ wn n ≤ 1031745 / 1000000 := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hinvs : 1 / √(n : ℝ) ≤ 1 / 127 := one_div_le_one_div_of_le (by norm_num) hs
  unfold wn
  refine ⟨by positivity, ?_⟩
  have h2 : 2 / √(n : ℝ) ≤ 2 / 127 := by
    have : 2 / √(n : ℝ) = 2 * (1 / √(n : ℝ)) := by ring
    linarith
  have h20 : 0 ≤ 2 / √(n : ℝ) := by positivity
  calc (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / 127) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
    _ ≤ _ := by norm_num

/-- `N̄₂₂ ≤ 18.334/n`, `N̄₂₄ ≤ 24.779/n`. -/
theorem Nbar_leB16 {n : ℕ} (hn : 16200 ≤ n) :
    0 ≤ N22bar n 12 ∧ N22bar n 12 ≤ 18334 / 1000 / (n : ℝ) ∧
    0 ≤ N24bar n 12 ∧ N24bar n 12 ≤ 24779 / 1000 / (n : ℝ) := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have ht : 1 / (n : ℝ) ≤ 1 / 16200 := one_div_le_one_div_of_le (by norm_num) hn'
  have h5 : √(5 : ℝ) ≤ 223607 / 100000 := sqrt_le_of (by norm_num) (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3464102 / 1000000 := sqrt_le_of (by norm_num) (by norm_num)
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have h120 := Real.sqrt_nonneg (12 : ℝ)
  have hx := x4n_le (n := n) (by omega)
  have hx0 := x4n_nonneg n
  obtain ⟨hw0, hw⟩ := wn_le hn
  -- N12
  have e12 : N12bar n 12 = (√5 + 2 * √12) * (1 / (n : ℝ)) := by unfold N12bar; ring
  have hN0 : 0 ≤ N12bar n 12 := by rw [e12]; positivity
  have hN : N12bar n 12 ≤ 9164274 / 1000000 * (1 / (n : ℝ)) := by
    rw [e12]; exact mul_le_mul_of_nonneg_right (by linarith) ht0
  have hN' : N12bar n 12 ≤ 57 / 100000 := by linarith
  have h22 : N22bar n 12 ≤ 18334 / 1000 / (n : ℝ) := by
    unfold N22bar
    calc N12bar n 12 * (2 + N12bar n 12)
        ≤ 9164274 / 1000000 * (1 / (n : ℝ)) * (2 + 9164274 / 1000000 * (1 / 16200)) :=
          mul_le_mul hN (by linarith) (by linarith) (by positivity)
      _ = 9164274 / 1000000 * (2 + 9164274 / 1000000 * (1 / 16200)) * (1 / (n : ℝ)) := by ring
      _ ≤ 18334 / 1000 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) ht0
      _ = _ := by ring
  have h220 : 0 ≤ N22bar n 12 := by unfold N22bar; positivity
  -- N14
  have e14 : N14bar n 12 = (x4n n + 2 * √12) * (1 / (n : ℝ)) := by unfold N14bar; ring
  have hM0 : 0 ≤ N14bar n 12 := by rw [e14]; positivity
  have hM : N14bar n 12 ≤ 99284 / 10000 * (1 / (n : ℝ)) := by
    rw [e14]; exact mul_le_mul_of_nonneg_right (by linarith) ht0
  have hM' : N14bar n 12 ≤ 62 / 100000 := by linarith
  have hq : √(2 * 12 * wn n) ≤ 49762 / 10000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hq0 := Real.sqrt_nonneg (2 * 12 * wn n)
  have hp : x4n n * (1 + N14bar n 12) ≤ 3 * (1 + 62 / 100000) :=
    mul_le_mul hx (by linarith) (by linarith) (by norm_num)
  have hp0 : 0 ≤ x4n n * (1 + N14bar n 12) := by positivity
  have e24 : N24bar n 12 = x4n n * (1 + N14bar n 12) * (1 / (n : ℝ)) + N14bar n 12 +
      2 * √(2 * 12 * wn n) * (1 / (n : ℝ)) := by unfold N24bar; ring
  have a1 : x4n n * (1 + N14bar n 12) * (1 / (n : ℝ)) ≤ 3 * (1 + 62 / 100000) * (1 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hp ht0
  have a3 : 2 * √(2 * 12 * wn n) * (1 / (n : ℝ)) ≤ 2 * (49762 / 10000) * (1 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) ht0
  have e : (24779 / 1000 : ℝ) / n = 24779 / 1000 * (1 / (n : ℝ)) := by ring
  refine ⟨h220, h22, ?_, ?_⟩
  · rw [e24]; positivity
  · rw [e24, e]; linarith

private lemma xiNr_le {n : ℕ} (hn : 16200 ≤ n) {θ : ℝ} (h1 : θ ≤ 55 / 100) :
    xiNr n θ (11911 / 10000) ≤ 10710 / 1000000 := by
  obtain ⟨hn', hs, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hNN0, hNN', -, -⟩ := Nbar_leB16 hn
  have ht : 1 / (n : ℝ) ≤ 1 / 16200 := one_div_le_one_div_of_le (by norm_num) hn'
  have hNN : N22bar n 12 ≤ 1132 / 1000000 := by
    have e : (18334 / 1000 : ℝ) / n = 18334 / 1000 * (1 / (n : ℝ)) := by ring
    rw [e] at hNN'; linarith
  have hq : √(11911 / 10000 * θ) ≤ 80939 / 100000 :=
    sqrt_le_of (by norm_num) (by nlinarith)
  have hp : θ * (1 + N22bar n 12) ≤ 55 / 100 * (1 + 1132 / 1000000) :=
    mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
  unfold xiNr
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `√ξ°_hp ≤ 0.6890`, with `ξ_c ≤ 0.3235` as a hypothesis. -/
theorem x1_leB16 {n : ℕ} (hn : 16200 ≤ n) {θ ξ : ℝ} (_h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100)
    (_hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3235 / 10000) :
    cD n 12 (11 / 1000) ξ + xiNr n θ (11911 / 10000) ≤ 6890 / 10000 := by
  have hT := T_le hn
  have hx := xiNr_le hn h1
  have hξs : √ξ ≤ 568772 / 1000000 := sqrt_le_of (by norm_num) (by nlinarith)
  unfold cD
  linarith

private lemma eMP_le' {n : ℕ} (hn : 16200 ≤ n) {ξ b : ℝ}
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3235 / 10000) (hb0 : 0 ≤ b) (hb : b ≤ 113 / 100000) :
    0 ≤ eMP n (11 / 1000) ξ b ∧ eMP n (11 / 1000) ξ b ≤ 11 / 10000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  unfold eMP
  rw [h989]
  refine ⟨by positivity, ?_⟩
  have hπb : π * b ≤ 3.1416 * (113 / 100000) := mul_le_mul hπ.le hb hb0 (by norm_num)
  have hπξ : π * ξ ≤ 3.1416 * (3235 / 10000) := mul_le_mul hπ.le hξ hξ0 (by norm_num)
  have e1 : √(π * b / (n * (989 / 1000))) ≤ 48 / 100000 := by
    apply sqrt_le_of (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    norm_num at hπb ⊢; nlinarith
  have e2 : π * ξ / (n * (989 / 1000)) ≤ 7 / 100000 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num at hπξ ⊢; nlinarith
  linarith

/-- `√ξ°_∥ ≤ 0.1601`, with `ξ_c ≤ 0.3235` and `b_n ≤ 0.00112` as hypotheses. -/
theorem x2_leB16 {n : ℕ} (hn : 16200 ≤ n) {θ ξ b : ℝ} (_h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100)
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3235 / 10000) (hb0 : 0 ≤ b) (hb : b ≤ 113 / 100000) :
    LamMP n 12 (11 / 1000) ξ b + xiNr n θ (11911 / 10000) ≤ 1601 / 10000 := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hx := xiNr_le hn h1
  have hp := plow_geB16 hn
  have hT := T_le hn
  have hT0 := Real.sqrt_nonneg (16 * 12 * (1 + 11 / 1000) / (n : ℝ))
  obtain ⟨he0, he⟩ := eMP_le' hn hξ0 hξ hb0 hb
  have hξs : √ξ ≤ 568772 / 1000000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hξs0 := Real.sqrt_nonneg ξ
  have hc0 : 0 ≤ cD n 12 (11 / 1000) ξ := by unfold cD; positivity
  have hc : cD n 12 (11 / 1000) ξ ≤ 67824 / 100000 := by unfold cD; linarith
  have hA : √b ≤ 33616 / 1000000 := sqrt_le_of (by norm_num) (by nlinarith)
  have hA0 := Real.sqrt_nonneg b
  have hsp : √π ≤ 17725 / 10000 :=
    sqrt_le_of (by norm_num) (by nlinarith [Real.pi_lt_d4])
  have hsp0 := Real.sqrt_nonneg π
  have hR : (1265 / 10 : ℝ) ≤ √((n : ℝ) * (1 - 11 / 1000)) := by
    apply le_sqrt_of (by norm_num)
    rw [h989]; nlinarith
  have hB0 : 0 ≤ ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000))) := by positivity
  have hB : ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000))) ≤ 227 / 100000 := by
    rw [div_le_iff₀ (by linarith)]
    have : ξ * √π ≤ 3235 / 10000 * (17725 / 10000) := mul_le_mul hξ hsp hsp0 (by norm_num)
    nlinarith
  have h8 : 8 / ((n : ℝ) * √(n : ℝ)) ≤ 4 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    have : (16200 : ℝ) * 127 ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul hn' hs (by norm_num) hn0.le
    nlinarith
  have hP0 : 0 ≤ PiBarMP n 12 (11 / 1000) ξ b := by unfold PiBarMP; positivity
  have hP : PiBarMP n 12 (11 / 1000) ξ b ≤ 14540 / 100000 := by
    unfold PiBarMP
    have : (√b + ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000)))) * (1 + eMP n (11 / 1000) ξ b) ≤
        (33616 / 1000000 + 227 / 100000) * (1 + 11 / 10000) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    linarith
  have hD : (14224 / 100 : ℝ) ≤ 2 * plow n (11 / 1000) * √(n : ℝ) := by
    have : (56 / 100 : ℝ) * 127 ≤ plow n (11 / 1000) * √(n : ℝ) :=
      mul_le_mul hp hs (by norm_num) (by linarith)
    nlinarith
  have hD0 : (0 : ℝ) < 2 * plow n (11 / 1000) * √(n : ℝ) := by linarith
  have hς0 : 0 ≤ cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ)) :=
    div_nonneg hc0 hD0.le
  have hς : cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ)) ≤ 477 / 100000 := by
    rw [div_le_iff₀ hD0]; nlinarith
  have hc2 : cD n 12 (11 / 1000) ξ ^ 2 / (2 * plow n (11 / 1000) * √(n : ℝ)) ≤ 324 / 100000 := by
    rw [div_le_iff₀ hD0]
    have : cD n 12 (11 / 1000) ξ ^ 2 ≤ (67824 / 100000) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    nlinarith
  have hL : (1 + cD n 12 (11 / 1000) ξ / (2 * plow n (11 / 1000) * √(n : ℝ))) *
      PiBarMP n 12 (11 / 1000) ξ b ≤ (1 + 477 / 100000) * (14540 / 100000) :=
    mul_le_mul (by linarith) hP hP0 (by norm_num)
  unfold LamMP
  linarith

private lemma term {n s α a X k : ℝ} (hs : 0 < s) (hsq : s ^ 2 = n) (hα0 : 0 ≤ α)
    (hα : α ≤ a / n) (hX : X ≤ k * s) (hk : 0 ≤ k) : α * X ≤ a * k * (1 / s) := by
  have hks : 0 ≤ k * s := by positivity
  calc α * X ≤ α * (k * s) := mul_le_mul_of_nonneg_left hX hα0
    _ ≤ a / n * (k * s) := mul_le_mul_of_nonneg_right hα hks
    _ = a * k * (1 / s) := by rw [← hsq]; field_simp

private lemma ab_le {n : ℕ} (hn : 16200 ≤ n) :
    alphaJ n ≤ (1792 / 10000) / n ∧ betaJ n ≤ (81 / 1000) / n ∧ alphaJ n ≤ 12 / 1000000 ∧
      betaJ n ≤ 5 / 1000000 ∧ betaJ n + alphaJ n ^ 2 ≤ (81003 / 1000000) / n := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha0 : 0 ≤ alphaJ n := alphaJ_nonneg n
  have ha : alphaJ n ≤ (1792 / 10000) / n := by
    unfold alphaJ
    exact div_le_div_of_nonneg_right (c1F_kappa4_le (by omega)) hn0.le
  have hb : betaJ n ≤ (81 / 1000) / n := by
    unfold betaJ
    exact div_le_div_of_nonneg_right (c2F_kappa4_le_4096 (by omega)) hn0.le
  have hinvn : 1 / (n : ℝ) ≤ 1 / 16200 := one_div_le_one_div_of_le (by norm_num) hn'
  have hinvn0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have e2 : (81003 / 1000000 : ℝ) / n = 81003 / 1000000 * (1 / n) := by ring
  have e3 : (81 / 1000 : ℝ) / n = 81 / 1000 * (1 / n) := by ring
  have e4 : (1792 / 10000 : ℝ) / n = 1792 / 10000 * (1 / n) := by ring
  have hb' : betaJ n ≤ 5 / 1000000 := by linarith
  have ha' : alphaJ n ≤ 12 / 1000000 := by linarith
  refine ⟨ha, hb, ha', hb', ?_⟩
  have e1 : alphaJ n ^ 2 ≤ 12 / 1000000 * ((1792 / 10000) / n) := by
    rw [sq]; exact mul_le_mul ha' ha ha0 (by norm_num)
  rw [e4] at e1; rw [e3] at hb; rw [e2]
  linarith

private lemma deltaChi_le {n : ℕ} (hn : 16200 ≤ n) :
    0 ≤ deltaChi n 12 ∧ deltaChi n 12 ≤ 428 / 1000000 := by
  obtain ⟨hn', -, -⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hinvn : 1 / (n : ℝ) ≤ 1 / 16200 := one_div_le_one_div_of_le (by norm_num) hn'
  have hinvn0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have h12 : √(12 : ℝ) ≤ 34642 / 10000 := sqrt_le_of (by norm_num) (by norm_num)
  unfold deltaChi
  refine ⟨by positivity, ?_⟩
  have e1 : 2 * √(12 : ℝ) / n ≤ 2 * (34642 / 10000) * (1 / 16200) := by
    have : 2 * √(12 : ℝ) / n = 2 * √(12 : ℝ) * (1 / n) := by ring
    rw [this]
    exact mul_le_mul (by linarith) hinvn hinvn0 (by norm_num)
  have e2 : 2 * 12 / (n : ℝ) ^ 2 ≤ 24 * (1 / 16200) ^ 2 := by
    have : 2 * 12 / (n : ℝ) ^ 2 = 24 * (1 / n) ^ 2 := by ring
    rw [this]
    have : (1 / (n : ℝ)) ^ 2 ≤ (1 / 16200) ^ 2 := pow_le_pow_left₀ hinvn0 hinvn 2
    linarith
  have e3 : (2 * (34642 / 10000) * (1 / 16200) + 24 * (1 / 16200) ^ 2 : ℝ) ≤ 428 / 1000000 := by
    norm_num
  linarith

private lemma two_div_pi_le : 2 / π ≤ 63662 / 100000 := by
  have h := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d6.le
  have h3 : (1 : ℝ) / 3.141592 ≤ 31831 / 100000 := by norm_num
  have e : 2 / π = 2 * (1 / π) := by ring
  rw [e]; linarith

private lemma root1 {n : ℕ} (hn : 16200 ≤ n) :
    √(2 * (1 + 11 / 1000) * (1 + 2 * wn n * betaJ n) * n) ≤ 142198 / 100000 * √(n : ℝ) := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hw0, hw⟩ := wn_le hn
  obtain ⟨-, -, -, hb', -⟩ := ab_le hn
  have hb0 : 0 ≤ betaJ n := betaJ_nonneg n
  have hwb : wn n * betaJ n ≤ 1031745 / 1000000 * (5 / 1000000) :=
    mul_le_mul hw hb' hb0 (by norm_num)
  apply sqrt_le_of (by positivity)
  rw [mul_pow, hsq]
  have : 2 * (1 + 11 / 1000) * (1 + 2 * wn n * betaJ n) ≤ (142198 / 100000 : ℝ) ^ 2 := by
    have e : (2 * (1 + 11 / 1000) * (1 + 2 * (1031745 / 1000000 * (5 / 1000000))) : ℝ) ≤
        (142198 / 100000 : ℝ) ^ 2 := by norm_num
    nlinarith
  exact mul_le_mul_of_nonneg_right this hn0.le

private lemma root2 {n : ℕ} (hn : 16200 ≤ n) :
    √(2 * (1 + 11 / 1000) * wn n * n * (1 + deltaChi n 12 + 2 / π) / csC) ≤
      162382 / 100000 * √(n : ℝ) := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hw0, hw⟩ := wn_le hn
  obtain ⟨hd0, hd⟩ := deltaChi_le hn
  have hpi := two_div_pi_le
  have hpi0 : 0 ≤ 2 / π := by positivity
  have hcs := csC_ge
  have hcs0 : 0 < csC := by linarith
  have hq : wn n * (1 + deltaChi n 12 + 2 / π) ≤
      1031745 / 1000000 * (1 + 428 / 1000000 + 63662 / 100000) :=
    mul_le_mul hw (by linarith) (by linarith) (by norm_num)
  apply sqrt_le_of (by positivity)
  rw [mul_pow, hsq, div_le_iff₀ hcs0]
  have e : (2 * (1 + 11 / 1000) * (1031745 / 1000000 * (1 + 428 / 1000000 + 63662 / 100000)) : ℝ) ≤
      (162382 / 100000 : ℝ) ^ 2 * (129521 / 100000) := by norm_num
  have e' : (162382 / 100000 : ℝ) ^ 2 * (129521 / 100000) ≤ (162382 / 100000 : ℝ) ^ 2 * csC :=
    mul_le_mul_of_nonneg_left hcs (by norm_num)
  have h : 2 * (1 + 11 / 1000) * (wn n * (1 + deltaChi n 12 + 2 / π)) ≤
      (162382 / 100000 : ℝ) ^ 2 * csC := by linarith
  have := mul_le_mul_of_nonneg_right h hn0.le
  calc 2 * (1 + 11 / 1000) * wn n * n * (1 + deltaChi n 12 + 2 / π)
      = 2 * (1 + 11 / 1000) * (wn n * (1 + deltaChi n 12 + 2 / π)) * n := by ring
    _ ≤ (162382 / 100000 : ℝ) ^ 2 * csC * n := this
    _ = _ := by ring

private lemma root3 {n : ℕ} (hn : 16200 ≤ n) :
    4 * (1 / √(2 * π)) * wn n * √((n : ℝ) / csC) ≤ 14468 / 10000 * √(n : ℝ) := by
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
  have e1 : 4 * (1 / √(2 * π)) * wn n ≤ 4 * (39895 / 100000) * (1031745 / 1000000) :=
    mul_le_mul (by linarith) hw hw0 (by norm_num)
  have e2 : (4 * (39895 / 100000) * (1031745 / 1000000) * (87869 / 100000) : ℝ) ≤
      14468 / 10000 := by norm_num
  calc 4 * (1 / √(2 * π)) * wn n * √((n : ℝ) / csC)
      ≤ 4 * (39895 / 100000) * (1031745 / 1000000) * (87869 / 100000 * √(n : ℝ)) :=
        mul_le_mul e1 h3 h30 (by norm_num)
    _ = 4 * (39895 / 100000) * (1031745 / 1000000) * (87869 / 100000) * √(n : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right e2 hs0.le

/-- `ϵ_J ≤ 0.00752` for `J = n` atoms, `n ≥ 16200`. -/
theorem epsJ_leB16 {n : ℕ} (hn : 16200 ≤ n) :
    0 ≤ epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ∧
    epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ 752 / 100000 := by
  obtain ⟨hn', hs, hsq⟩ := sqrt_n hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have ha0 : 0 ≤ alphaJ n := alphaJ_nonneg n
  have hb0 : 0 ≤ betaJ n := betaJ_nonneg n
  obtain ⟨ha, -, -, -, hg⟩ := ab_le hn
  have hg0 : 0 ≤ betaJ n + alphaJ n ^ 2 := by positivity
  obtain ⟨hw0, -⟩ := wn_le hn
  obtain ⟨hd0, -⟩ := deltaChi_le hn
  have hcs0 : 0 < csC := by linarith [csC_ge]
  have hinvs : 1 / √(n : ℝ) ≤ 1 / 127 := one_div_le_one_div_of_le (by norm_num) hs
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
  have c : (1792 / 10000 * (142198 / 100000) + 2 * (1792 / 10000 * (162382 / 100000)) +
      81003 / 1000000 * (14468 / 10000) : ℝ) * (1 / 127) ≤ 752 / 100000 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hinvs (by norm_num : (0 : ℝ) ≤
    1792 / 10000 * (142198 / 100000) + 2 * (1792 / 10000 * (162382 / 100000)) +
      81003 / 1000000 * (14468 / 10000))]

end BstLean.Part188.Base154_R
