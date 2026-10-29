import BstLean.Part150Kappa

/-!
# Part 150, item 2: the numeric values of the constants of Lemma B-F

Paper source: `onW45-opus-prover.md` §2 ("Values"): `c_1(J) ≤ 0.1792` for `J ≥ 1 000`,
`c_1(1) ≤ 0.4156`, `c_2(J) = 0.0737 + 0.4331/√J + …`.

* `kappa4_le : κ_4 ≤ 0.1157` (the value is `0.115626…`).
* **`c1F_kappa4_le`**: `c1F kappa4 J ≤ 0.1792` for `J ≥ 1 000`; `c1F_kappa4_le_all`: `≤ 0.4156` for
  `J ≥ 1`.
* **`c2F_kappa4_le`**: `c2F kappa4 J ≤ 0.0737 + 0.434/√J + e^{−J/2}/J` for `J ≥ 1`;
  `c2F_kappa4_le_4096`: `≤ 0.081` for `J ≥ 4 096`.
* **`lemmaBF1_1000`**, `lemmaBF1_all`, **`lemmaBF2_num`**, `lemmaBF2_4096`: Lemma B-F with these
  numbers.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part130 BstLean.Part137 BstLean.Part141

lemma exp_neg_ge5 {w : ℝ} (hw : 0 ≤ w) :
    1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24 - w ^ 5 / 120 ≤ rexp (-w) := by
  have h := nonneg_of_deriv_nonneg
    (f := fun w => rexp (-w) - (1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24 - w ^ 5 / 120))
    (f' := fun w => -rexp (-w) - (0 - 1 + w - w ^ 2 / 2 + w ^ 3 / 6 - w ^ 4 / 24)) (by simp)
    (fun x => by
      have h2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        convert this using 1; ring
      have h3 : HasDerivAt (fun w : ℝ => w ^ 3 / 6) (x ^ 2 / 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 6
        convert this using 1; ring
      have h4 : HasDerivAt (fun w : ℝ => w ^ 4 / 24) (x ^ 3 / 6) x := by
        have := (hasDerivAt_pow 4 x).div_const 24
        convert this using 1; ring
      have h5 : HasDerivAt (fun w : ℝ => w ^ 5 / 120) (x ^ 4 / 24) x := by
        have := (hasDerivAt_pow 5 x).div_const 120
        convert this using 1; ring
      exact (hasDerivAt_exp_neg x).sub
        ((((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add h2).sub h3).add h4).sub h5))
    (fun x hx => by have := exp_neg_le4 hx; linarith) w hw
  linarith

lemma exp_neg_le6 {w : ℝ} (hw : 0 ≤ w) :
    rexp (-w) ≤ 1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24 - w ^ 5 / 120 + w ^ 6 / 720 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun w => (1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24 - w ^ 5 / 120 + w ^ 6 / 720) -
      rexp (-w))
    (f' := fun w => (0 - 1 + w - w ^ 2 / 2 + w ^ 3 / 6 - w ^ 4 / 24 + w ^ 5 / 120) - -rexp (-w))
    (by simp) (fun x => by
      have h2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        convert this using 1; ring
      have h3 : HasDerivAt (fun w : ℝ => w ^ 3 / 6) (x ^ 2 / 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 6
        convert this using 1; ring
      have h4 : HasDerivAt (fun w : ℝ => w ^ 4 / 24) (x ^ 3 / 6) x := by
        have := (hasDerivAt_pow 4 x).div_const 24
        convert this using 1; ring
      have h5 : HasDerivAt (fun w : ℝ => w ^ 5 / 120) (x ^ 4 / 24) x := by
        have := (hasDerivAt_pow 5 x).div_const 120
        convert this using 1; ring
      have h6 : HasDerivAt (fun w : ℝ => w ^ 6 / 720) (x ^ 5 / 120) x := by
        have := (hasDerivAt_pow 6 x).div_const 720
        convert this using 1; ring
      exact (((((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add h2).sub h3).add h4).sub
        h5).add h6).sub (hasDerivAt_exp_neg x))
    (fun x hx => by have := exp_neg_ge5 hx; linarith) w hw
  linarith

/-- `κ_4 ≤ 0.1157`. -/
theorem kappa4_le : kappa4 ≤ 1157 / 10000 := by
  unfold kappa4
  have hc : (389 : ℝ) / 720 ≤ Real.cos 1 := by
    have := cos_ge6 1; norm_num at this; linarith
  have he : rexp (-(6157 / 10000)) ≤ 389 / 720 := by
    have := exp_neg_le6 (w := 6157 / 10000) (by norm_num)
    norm_num at this ⊢; linarith
  have hpos : 0 < Real.cos 1 := by linarith
  have : -(6157 / 10000 : ℝ) ≤ Real.log (Real.cos 1) :=
    (Real.le_log_iff_exp_le hpos).mpr (he.trans hc)
  linarith

lemma sqrt_half_pi_le : √(π / 2) ≤ 1253315 / 1000000 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have := Real.pi_lt_d6
  norm_num at this ⊢; linarith

lemma sqrt_two_pi_le : √(2 * π) ≤ 2506629 / 1000000 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have := Real.pi_lt_d6
  norm_num at this ⊢; linarith

lemma exp_neg_half_le {J : ℕ} (hJ : 1 ≤ J) : rexp (-((J : ℝ) / 2)) ≤ 16 / (J : ℝ) ^ 2 := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have h1 := Real.add_one_le_exp ((J : ℝ) / 4)
  have h2 : (1 + (J : ℝ) / 4) ^ 2 ≤ rexp ((J : ℝ) / 2) := by
    have : rexp ((J : ℝ) / 2) = rexp ((J : ℝ) / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith

lemma one_le_sqrtJ {J : ℕ} (hJ : 1 ≤ J) : 1 ≤ √(J : ℝ) := by
  rw [Real.one_le_sqrt]; exact_mod_cast hJ

/-- **`c_1(J) ≤ 0.1792` for `J ≥ 1 000`** (the paper's value). -/
theorem c1F_kappa4_le {J : ℕ} (hJ : 1000 ≤ J) : c1F kappa4 J ≤ 1792 / 10000 := by
  have hJ1 : 1 ≤ J := by omega
  have hJr : (1000 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by linarith
  have hk := kappa4_le
  have hk0 := kappa4_nonneg
  have hs1 := sqrt_half_pi_le
  have hs2 := sqrt_two_pi_le
  have hs10 : 0 ≤ √(π / 2) := Real.sqrt_nonneg _
  have hs20 : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  have t1 : kappa4 * √(π / 2) ≤ 1157 / 10000 * (1253315 / 1000000) :=
    mul_le_mul hk hs1 hs10 (by norm_num)
  have t3 : 44 / 9 * (√(2 * π) / 90) / J ≤ 44 / 9 * (2506629 / 1000000 / 90) / 1000 := by
    apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) hJr
  have t4 : rexp (-((J : ℝ) / 2)) / √(J : ℝ) ≤ 16 / 1000000 := by
    have h1 := exp_neg_half_le hJ1
    have h2 : 16 / (J : ℝ) ^ 2 ≤ 16 / 1000000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3 : rexp (-((J : ℝ) / 2)) / √(J : ℝ) ≤ rexp (-((J : ℝ) / 2)) :=
      div_le_self (Real.exp_pos _).le (one_le_sqrtJ hJ1)
    linarith
  have hpi6 : (3141592 / 1000000 : ℝ) < π := by
    have := Real.pi_gt_d6
    norm_num at this ⊢; linarith
  unfold c1F
  rw [one_div, inv_mul_le_iff₀ Real.pi_pos]
  linarith

/-- `c_1(J) ≤ 0.4156` for every `J ≥ 1` (the paper's value of `c_1(1)`). -/
theorem c1F_kappa4_le_all {J : ℕ} (hJ : 1 ≤ J) : c1F kappa4 J ≤ 4156 / 10000 := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by linarith
  have hk := kappa4_le
  have hk0 := kappa4_nonneg
  have hs1 := sqrt_half_pi_le
  have hs2 := sqrt_two_pi_le
  have hs10 : 0 ≤ √(π / 2) := Real.sqrt_nonneg _
  have hs20 : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  have t1 : kappa4 * √(π / 2) ≤ 1157 / 10000 * (1253315 / 1000000) :=
    mul_le_mul hk hs1 hs10 (by norm_num)
  have t3 : 44 / 9 * (√(2 * π) / 90) / J ≤ 44 / 9 * (2506629 / 1000000 / 90) / 1 := by
    apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) hJr
  have t4 : rexp (-((J : ℝ) / 2)) / √(J : ℝ) ≤ 6066 / 10000 := by
    have h1 : rexp (-((J : ℝ) / 2)) ≤ rexp (-(1 / 2)) := Real.exp_le_exp.mpr (by linarith)
    have h2 := exp_neg_le6 (w := (1 : ℝ) / 2) (by norm_num)
    have h3 : rexp (-((J : ℝ) / 2)) / √(J : ℝ) ≤ rexp (-((J : ℝ) / 2)) :=
      div_le_self (Real.exp_pos _).le (one_le_sqrtJ hJ)
    norm_num at h2
    linarith
  have hpi6 : (3141592 / 1000000 : ℝ) < π := by
    have := Real.pi_gt_d6
    norm_num at this ⊢; linarith
  unfold c1F
  rw [one_div, inv_mul_le_iff₀ Real.pi_pos]
  linarith

/-- **`c_2(J) ≤ 0.0737 + 0.434/√J + e^{−J/2}/J`** for every `J ≥ 1`. -/
theorem c2F_kappa4_le {J : ℕ} (hJ : 1 ≤ J) :
    c2F kappa4 J ≤ 737 / 10000 + 434 / 1000 / √(J : ℝ) + rexp (-((J : ℝ) / 2)) / J := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by linarith
  have hsJ : 0 < √(J : ℝ) := Real.sqrt_pos.mpr hJpos
  have hpi := Real.pi_pos
  have hpi6 : (3141592 / 1000000 : ℝ) < π := by
    have := Real.pi_gt_d6
    norm_num at this ⊢; linarith
  have hk := kappa4_le
  have hs2 := sqrt_two_pi_le
  have hs20 : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  have t1 : 2 / π * kappa4 ≤ 737 / 10000 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi]
    linarith
  have hp4 : (3141592 / 1000000 : ℝ) ^ 4 ≤ π ^ 4 := pow_le_pow_left₀ (by norm_num) hpi6.le 4
  have t2 : 2 / π * (√(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ)) ≤ 434 / 1000 / √(J : ℝ) := by
    have e : 2 / π * (√(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ)) =
        2 * √(2 * π) * 56807 / (6750 * π ^ 4) / √(J : ℝ) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hsJ.le
    rw [div_le_iff₀ (by positivity)]
    have n1 : 2 * √(2 * π) * 56807 ≤ 2 * (2506629 / 1000000) * 56807 := by linarith
    have n2 : (2 : ℝ) * (2506629 / 1000000) * 56807 ≤
        434 / 1000 * (6750 * (3141592 / 1000000) ^ 4) := by norm_num
    linarith
  have t3 : 2 / π * (rexp (-((J : ℝ) / 2)) / J) ≤ rexp (-((J : ℝ) / 2)) / J := by
    have h2 : 2 / π ≤ 1 := by rw [div_le_one hpi]; linarith
    have h0 : 0 ≤ rexp (-((J : ℝ) / 2)) / J := by positivity
    nlinarith
  unfold c2F
  rw [mul_add, mul_add]
  linarith

/-- `c_2(J) ≤ 0.081` for `J ≥ 4 096`. -/
theorem c2F_kappa4_le_4096 {J : ℕ} (hJ : 4096 ≤ J) : c2F kappa4 J ≤ 81 / 1000 := by
  have hJ1 : 1 ≤ J := by omega
  have hJr : (4096 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by linarith
  have h := c2F_kappa4_le hJ1
  have hs : (64 : ℝ) ≤ √(J : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have t2 : 434 / 1000 / √(J : ℝ) ≤ 434 / 1000 / 64 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have t3 : rexp (-((J : ℝ) / 2)) / J ≤ 1 / 1000000 := by
    have h1 := exp_neg_half_le hJ1
    have h2 : 16 / (J : ℝ) ^ 2 ≤ 16 / 16000000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3 : rexp (-((J : ℝ) / 2)) / J ≤ rexp (-((J : ℝ) / 2)) :=
      div_le_self (Real.exp_pos _).le (by linarith)
    linarith
  linarith

/-- **Lemma B-F (i), numeric form**: `0.1792·s/J` for `J ≥ 1 000`. -/
theorem lemmaBF1_1000 {J : ℕ} (hJ : 1000 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z)) - psiS s a| ≤ 1792 / 10000 * s / J := by
  have hJpos : (0 : ℝ) < J := by
    have : (1000 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  refine (lemmaBF1_paper (by omega) a hs).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (c1F_kappa4_le hJ) hs) hJpos.le

/-- Lemma B-F (i), numeric form: `0.4156·s/J` for every `J ≥ 1`. -/
theorem lemmaBF1_all {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z)) - psiS s a| ≤ 4156 / 10000 * s / J := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  refine (lemmaBF1_paper hJ a hs).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (c1F_kappa4_le_all hJ) hs) hJpos.le

/-- **Lemma B-F (ii), numeric form**: `(0.0737 + 0.434/√J + e^{−J/2}/J)·s²/J`, `J ≥ 1`. -/
theorem lemmaBF2_num {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z) ^ 2) - ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤
      (737 / 10000 + 434 / 1000 / √(J : ℝ) + rexp (-((J : ℝ) / 2)) / J) * s ^ 2 / J := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  refine (lemmaBF2_paper hJ a hs).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (c2F_kappa4_le hJ) (sq_nonneg s)) hJpos.le

/-- Lemma B-F (ii), numeric form: `0.081·s²/J` for `J ≥ 4 096`. -/
theorem lemmaBF2_4096 {J : ℕ} (hJ : 4096 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z) ^ 2) - ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤
      81 / 1000 * s ^ 2 / J := by
  have hJpos : (0 : ℝ) < J := by
    have : (4096 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  refine (lemmaBF2_paper (by omega) a hs).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (c2F_kappa4_le_4096 hJ) (sq_nonneg s)) hJpos.le

end BstLean.Part150
