import BstLean.Part246TI
import BstLean.Part238M12Cov

/-! Part 246: the TI charge `53e^{-τ} + 12e^{-2η²m}` fits the paper's covariance payment.
At `τ = 46` (with `2η²m ≥ 46`) the charge is at most `7·10⁻¹⁹`, so the cutoff `δ/ε` with the
paper's `ε = 1/4000` is at most `2.8·10⁻¹⁵`; the exceptional factor stays below `.001032`, and the
conditional `.34` covariance bound holds. Alternatively `τ ≥ 46.27` brings the charge below the
paper's `50e^{-46}`. Nothing that depends on `ε` changes. -/
namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
  BstLean.Part208
open BstLean.Part199 (Window radiusMinus exampleCore exampleWide example_nested pairRowBound
  outsideBound)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)
open BstLean.Part238 (SharpCovEvent sharpScalar sharpK ta_lam_nonneg sharpK_nonneg
  cov_at_sharp_M12)

/-- **The charge at `τ = 46`.** -/
theorem charge_46 {n : ℕ} {η : ℝ} (hη : 46 ≤ 2 * η ^ 2 * (mA n : ℕ)) :
    53 * exp (-46) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) ≤ (7 / 10 ^ 19 : ℝ) := by
  have h1 : exp (-2 * η ^ 2 * (mA n : ℕ)) ≤ exp (-46) := Real.exp_le_exp.mpr (by linarith)
  have h2 := BstLean.Part182.exp_neg_nat_le 46
  have h3 : (65 : ℝ) * (3678794412 / 10 ^ 10) ^ 46 ≤ 7 / 10 ^ 19 := by norm_num
  have h4 : exp (-46 : ℝ) = exp (-((46 : ℕ) : ℝ)) := by norm_num
  rw [h4] at h1 ⊢
  linarith

/-- **The paper's charge `50e^{-46}`** from `τ ≥ 46.27` and `2η²m ≥ τ`. -/
theorem charge_paper {n : ℕ} {η τ : ℝ} (hτ : 46 + 27 / 100 ≤ τ) (hη : τ ≤ 2 * η ^ 2 * (mA n : ℕ)) :
    53 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) ≤ 50 * exp (-46) := by
  have h1 : exp (-2 * η ^ 2 * (mA n : ℕ)) ≤ exp (-τ) := Real.exp_le_exp.mpr (by linarith)
  have h2 : exp (-τ) ≤ exp (-46) * exp (-(27 / 100)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h3 : (130 / 100 : ℝ) ≤ exp (27 / 100) := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 27 / 100 by norm_num)
    linarith
  have h4 : exp (-(27 / 100) : ℝ) ≤ 100 / 130 := by
    rw [Real.exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    linarith
  have h5 : exp (-τ) ≤ exp (-46) * (100 / 130) :=
    h2.trans (mul_le_mul_of_nonneg_left h4 (exp_pos _).le)
  have := exp_pos (-46 : ℝ)
  nlinarith

/-- The cutoff with the paper's `ε = 1/4000`. -/
theorem cutoff_46 {n : ℕ} {η : ℝ} (hη : 46 ≤ 2 * η ^ 2 * (mA n : ℕ)) :
    (53 * exp (-46) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) / (1 / 4000) ≤ (28 / 10 ^ 16 : ℝ) := by
  have h := charge_46 hη
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- The exceptional factor with mass `2e^{-32} + 2b`, `b ≤ 2.8·10⁻¹⁵`, is at most `.001032`. -/
theorem exceptional_bound_28 {b : ℝ} (hb : b ≤ 28 / 10 ^ 16) :
    2 * √(√(2 * exp (-exampleWide.pair ^ 2 / 2) + 2 * b)) + √(outsideBound exampleWide) ≤
      (1032 / 10 ^ 6 : ℝ) := by
  have hp : 2 * exp (-exampleWide.pair ^ 2 / 2) ≤ (26 / 10 ^ 15 : ℝ) := by
    simpa only [exampleWide] using BstLean.Part182.two_exp_neg32
  have hq : √(√(2 * exp (-exampleWide.pair ^ 2 / 2) + 2 * b)) ≤ (422 / 10 ^ 6 : ℝ) := by
    apply BstLean.Part182.sqrt_sqrt_le_of (by norm_num)
    linarith only [hp, hb]
  have ho : √(outsideBound exampleWide) ≤ (188 / 10 ^ 6 : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    linarith only [BstLean.Part235.wide_outside_bound]
  linarith only [hq, ho]

/-- The rational covariance upper bound with the exceptional constant `.001032`. -/
noncomputable def ratCov (lam₀ K M : ℝ) : ℝ :=
  (528 / 1000) * (K * (5000 / 4999) + lam₀ * (500 / 473) * (121 / 10 ^ 4) +
    lam₀ * (10 / 9) * (409 / 10 ^ 4)) + M * (1032 / 10 ^ 6)

theorem sharp_rational_bound_28 {n : ℕ} (hn : 11883 ≤ n) {θ lam₀ K M b : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 528 / 1000) (hl₀ : 0 ≤ lam₀) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hr₀ : radiusMinus n θ exampleWide ≤ 1 / 10)
    (hr₁ : radiusMinus n θ exampleCore ≤ 54 / 1000) (hb : b ≤ 28 / 10 ^ 16) :
    sharpScalar n θ exampleWide exampleCore K lam₀ (1 - 4 * θ / n)⁻¹ M
      (2 * exp (-exampleWide.pair ^ 2 / 2) + 2 * b) ≤ ratCov lam₀ K M := by
  have hw : (1 - radiusMinus n θ exampleWide)⁻¹ ≤ (10 / 9 : ℝ) := by
    rw [← one_div]
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 9 / 10)
      (by linarith only [hr₀])).trans (by norm_num)
  have hc : (1 - radiusMinus n θ exampleCore)⁻¹ ≤ (500 / 473 : ℝ) := by
    rw [← one_div]
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 473 / 500)
      (by linarith only [hr₁])).trans (by norm_num)
  have hp0 : 0 ≤ pairRowBound exampleCore := by unfold pairRowBound; positivity
  have ho0 : 0 ≤ outsideBound exampleCore := by unfold outsideBound; positivity
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hc hl₀) BstLean.Part235.core_pair_bound hp0
    (by positivity : 0 ≤ lam₀ * (500 / 473))
  have ho := mul_le_mul (mul_le_mul_of_nonneg_left hw hl₀) BstLean.Part235.core_outside_bound
    ho0 (by positivity : 0 ≤ lam₀ * (10 / 9))
  have he := mul_le_mul_of_nonneg_left (BstLean.Part235.radius_mean_factor_bound hn hθ) hK
  have hsum := add_le_add (add_le_add he hp) ho
  have hθsum := (mul_le_mul_of_nonneg_left hsum hθ0).trans
    (mul_le_mul_of_nonneg_right hθ (by positivity))
  have hx := mul_le_mul_of_nonneg_left (exceptional_bound_28 hb) hM
  unfold sharpScalar ratCov
  linarith only [hθsum, hx]

theorem ratCov_sufficient {lam₀ K M : ℝ} (hl₀ : lam₀ ≤ 66 / 100) (hK : K ≤ 60 / 100)
    (hM : M ≤ 13 / 10) : ratCov lam₀ K M ≤ (34 / 100 : ℝ) := by
  unfold ratCov
  linarith only [hl₀, hK, hM]

/-- **Conditional M1/M2 covariance bound `.34` with the actual TI charge and `ε = 1/4000`.**
The cutoff is `δ/ε` with `δ = 53e^{-46} + 12e^{-2η²m}`. The wide coefficient may be up to `.66`
(the calculator estimate is `≈ .657`). -/
theorem cov_at_034_sharp_M12_charge {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k) {kE ko ks lam₀ M η : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hl₀u : lam₀ ≤ 66 / 100)
    (hKu : min (kE + 14284 / 10000 * ko + 51 / 100 * ks) (ta_lam kE ko ks) ≤ 60 / 100)
    (hMu : M ≤ 13 / 10) (hη : 46 ≤ 2 * η ^ 2 * (mA n : ℕ))
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc (46 / 100) (528 / 1000))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      SharpCovEvent n exampleWide exampleCore (46 / 100) (528 / 1000) lam₀ kE ko ks (63 / 100)
        ((53 * exp (-46) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) / (1 / 4000))) :
    COV_at D k (34 / 100) := by
  have hr₀ := (BstLean.Part235.wide_radius_caps hn hw.1 hw.2).1
  have hr₁ := (BstLean.Part235.core_radius_caps hn hw.1 hw.2).1
  have hsq : √(51 / 100 : ℝ) ≤ 7142 / 10000 :=
    BstLean.Part182.sqrt_le_of_sq' (by norm_num) (by norm_num)
  have hK1 : sharpK kE ko ks (51 / 100) ≤ kE + 14284 / 10000 * ko + 51 / 100 * ks := by
    unfold sharpK
    have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * ko)
    linarith
  have hKmin : min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks) ≤ 60 / 100 :=
    (min_le_min_right _ hK1).trans hKu
  have hK0 : 0 ≤ min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks) :=
    le_min (sharpK_nonneg hkE hko hks (by norm_num)) (ta_lam_nonneg hkE hks)
  refine cov_at_sharp_M12 hn D k hτ hkE hko hks hl₀ hM hw hX hC ?_
  exact (sharp_rational_bound_28 hn (by linarith only [hw.1]) hw.2 hl₀ hK0 hM hr₀ hr₁
    (cutoff_46 hη)).trans (ratCov_sufficient hl₀u hKmin hMu)

theorem ratCov_sufficient_067 {lam₀ K M : ℝ} (hl₀ : lam₀ ≤ 67 / 100) (hK : K ≤ 60 / 100)
    (hM : M ≤ 13 / 10) : ratCov lam₀ K M ≤ (34 / 100 : ℝ) := by
  unfold ratCov
  linarith only [hl₀, hK, hM]

/-- **Conditional M1/M2 covariance bound `.34` with the actual TI charge and `ε = 1/4000`.**
The cutoff is `δ/ε` with `δ = 53e^{-46} + 12e^{-2η²m}`. Version with the Part 245 repaired wide cap `.67`. -/
theorem cov_at_034_sharp_M12_charge_067 {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k) {kE ko ks lam₀ M η : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hl₀u : lam₀ ≤ 67 / 100)
    (hKu : min (kE + 14284 / 10000 * ko + 51 / 100 * ks) (ta_lam kE ko ks) ≤ 60 / 100)
    (hMu : M ≤ 13 / 10) (hη : 46 ≤ 2 * η ^ 2 * (mA n : ℕ))
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc (46 / 100) (528 / 1000))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      SharpCovEvent n exampleWide exampleCore (46 / 100) (528 / 1000) lam₀ kE ko ks (63 / 100)
        ((53 * exp (-46) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) / (1 / 4000))) :
    COV_at D k (34 / 100) := by
  have hr₀ := (BstLean.Part235.wide_radius_caps hn hw.1 hw.2).1
  have hr₁ := (BstLean.Part235.core_radius_caps hn hw.1 hw.2).1
  have hsq : √(51 / 100 : ℝ) ≤ 7142 / 10000 :=
    BstLean.Part182.sqrt_le_of_sq' (by norm_num) (by norm_num)
  have hK1 : sharpK kE ko ks (51 / 100) ≤ kE + 14284 / 10000 * ko + 51 / 100 * ks := by
    unfold sharpK
    have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * ko)
    linarith
  have hKmin : min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks) ≤ 60 / 100 :=
    (min_le_min_right _ hK1).trans hKu
  have hK0 : 0 ≤ min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks) :=
    le_min (sharpK_nonneg hkE hko hks (by norm_num)) (ta_lam_nonneg hkE hks)
  refine cov_at_sharp_M12 hn D k hτ hkE hko hks hl₀ hM hw hX hC ?_
  exact (sharp_rational_bound_28 hn (by linarith only [hw.1]) hw.2 hl₀ hK0 hM hr₀ hr₁
    (cutoff_46 hη)).trans (ratCov_sufficient_067 hl₀u hKmin hMu)

/-- The Part 244 numeric premises imply the Part 246 ones (the exact `r₂` is smaller). -/
theorem ta_num_sharp_of_244 {n : ℕ} {cm cp kE ko ks η τ : ℝ} (hτ : 0 ≤ τ)
    (h : BstLean.Part244.ta_num_sharp n cm cp kE ko ks η τ) :
    ta_num_sharp n cm cp kE ko ks η τ := by
  obtain ⟨hko, ham, hall⟩ := h
  refine ⟨hko, ham, fun c h1 h2 => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hall c h1 h2
  refine ⟨a1, a2, a3, a4, a5, le_trans ?_ a6, a7⟩
  unfold e3s_bound BstLean.Part244.e3s_bound
  have hl : 0 ≤ (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ) ^ 2 := sq_nonneg _
  have ht : 0 ≤ 2 / ((mA n : ℕ) : ℝ) := by positivity
  have hs : 0 ≤ √(2 * (n : ℝ)) + √(2 * τ) := by positivity
  have hr : 2 * √(((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ c) / 2 + η)) * (√(2 * (n : ℝ)) + √(2 * τ)) +
      (√(2 * (n : ℝ)) + √(2 * τ)) ^ 2 ≤
      2 * √(((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ c) / 2 + η)) * (√(2 * (n : ℝ)) + √(2 * τ)) + 4 +
      (√(2 * (n : ℝ)) + √(2 * τ) + 2) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr ht) hl
  linarith

end BstLean.Part246
