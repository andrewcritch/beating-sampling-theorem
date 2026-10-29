import BstLean.Part64Final

/-!
# Part 64: numeric certificates for the explicit threshold of Theorem 1

At failure `1/100`, `C = 1`, `ε_lo = ε_hi = 1/2`:

* `N56_22_le : N56 2 2 1 (1/2) (1/2) ≤ 10^178` (`(d_M, d_f) = (2, 2)`, small-ball degree `h = 4`, `K = 5⁸`);
* `N56_33_le : N56 3 3 1 (1/2) (1/2) ≤ 10^330` (`(d_M, d_f) = (3, 3)`, `h = 6`, `K = 5¹²`);
* `part64_22`, `part64_33`: the conclusion of `part64_general` for every `n ≥ 10^178`
  (respectively `n ≥ 10^330`).

The only real inputs are `e < 2.7182818286` (`Real.exp_one_lt_d9`) and `√x ≤ y` from `x ≤ y²`.
Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part64

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part56
open BstLean.Part62 (tK)

lemma CDT1_2 : CDT1 2 = 21761088 := by
  unfold CDT1 CD64 CK64 Clin64
  norm_num [Finset.sum_Icc_succ_top]

lemma CDT1_3 : CDT1 3 = 752677632 := by
  unfold CDT1 CD64 CK64 Clin64
  norm_num [Finset.sum_Icc_succ_top]

lemma tsb64_2 : tsb64 2 = (1 / 200) ^ 8 / (2 * (8 * 5 ^ 8 * 9) ^ 8 * 9) := by
  unfold tsb64 tK Kbest
  norm_num

lemma tsb64_3 : tsb64 3 = (1 / 200) ^ 12 / (2 * (8 * 5 ^ 12 * 13) ^ 12 * 13) := by
  unfold tsb64 tK Kbest
  norm_num

lemma CR64_2 : CR64 2 = 106 := by
  unfold CR64; norm_num [Finset.sum_range_succ, aR]

lemma CR64_3 : CR64 3 = 10500 := by
  unfold CR64; norm_num [Finset.sum_range_succ, aR]

lemma CA64_2 : CA64 2 2 = 9041880 := by
  unfold CA64 CW64 momentBudget64
  norm_num [Finset.sum_range_succ, BstLean.Part53.T2Aux.heatWeight, Nat.factorial]

lemma CA64_3 : CA64 3 3 = 10085931197396 := by
  unfold CA64 CW64 momentBudget64
  norm_num [Finset.sum_range_succ, BstLean.Part53.T2Aux.heatWeight, Nat.factorial]

lemma W_2 : BstLean.Part56.LowCoefficients.weightBound 2 2 = 183397 := by
  unfold BstLean.Part56.LowCoefficients.weightBound
  norm_num [Finset.sum_range_succ, BstLean.Part53.FloorHeat.heatWeight, Nat.factorial]

lemma W_3 : BstLean.Part56.LowCoefficients.weightBound 3 3 = 7274827045 := by
  unfold BstLean.Part56.LowCoefficients.weightBound
  norm_num [Finset.sum_range_succ, BstLean.Part53.FloorHeat.heatWeight, Nat.factorial]

lemma exp4_le : Real.exp (2 * (1 + 1)) ≤ 55 := by
  have h : Real.exp (2 * (1 + 1)) = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  nlinarith [pow_le_pow_left₀ h0.le this.le 4]

lemma θL64_1_ge : (1 / 221 : ℝ) ≤ θL64 1 := by
  unfold θL64
  have := exp4_le
  rw [one_div]
  apply inv_anti₀ (by positivity)
  linarith


lemma ceil_add_le {x : ℝ} (hx : 0 ≤ x) {a M : ℕ} (h : x + a ≤ M) : ⌈x⌉₊ + a ≤ M := by
  have h1 := Nat.ceil_lt_add_one hx
  have h2 : ((⌈x⌉₊ + a : ℕ) : ℝ) < M + 1 := by push_cast; linarith
  have h3 : ⌈x⌉₊ + a < M + 1 := by exact_mod_cast h2
  omega

lemma ceil_two_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {M : ℕ} (h : x + y + 3 ≤ M) :
    ⌈x⌉₊ + ⌈y⌉₊ + 1 ≤ M := by
  have h1 := Nat.ceil_lt_add_one hx
  have h2 := Nat.ceil_lt_add_one hy
  have h3 : ((⌈x⌉₊ + ⌈y⌉₊ + 1 : ℕ) : ℝ) < M + 1 := by push_cast; linarith
  have h4 : ⌈x⌉₊ + ⌈y⌉₊ + 1 < M + 1 := by exact_mod_cast h3
  omega

lemma sqrt_le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- The rational lower bound of `cL64 2 2 1`. -/
lemma cL_22_ge : ((1 / 221 : ℝ) ^ 2 / 2) / (27 * 183397) ≤ cL64 2 2 1 := by
  have h := θL64_1_ge
  calc ((1 / 221 : ℝ) ^ 2 / 2) / (27 * 183397) ≤ θL64 1 ^ 2 / 2 / (27 * 183397) := by gcongr
    _ = cL64 2 2 1 := by unfold cL64 aL64; rw [W_2]; norm_num

lemma cL_33_ge : ((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045) ≤ cL64 3 3 1 := by
  have h := θL64_1_ge
  calc ((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045) ≤ θL64 1 ^ 3 / 2 / (64 * 7274827045) := by gcongr
    _ = cL64 3 3 1 := by unfold cL64 aL64; rw [W_3]; norm_num

lemma n2_le (CD : ℝ) (M : ℕ) (h40 : 40 ≤ M) (hCD : 0 ≤ CD) (h : 8 * CD + 2 ≤ M) :
    n2T2_64 CD (nL64 1) ≤ M := by
  unfold n2T2_64 nL64
  refine max_le (max_le (by simp; omega) h40) (ceil_add_le (by positivity) ?_)
  rw [abs_of_nonneg hCD]; push_cast; linarith

lemma n1_le (CD : ℝ) (M : ℕ) (h40 : 40 ≤ M) (hCD : 0 ≤ CD) (h : 8 * CD + 2 ≤ M) :
    n1T1_64 CD ≤ M := by
  unfold n1T1_64
  refine max_le h40 (ceil_add_le (by positivity) ?_)
  rw [abs_of_nonneg hCD]; push_cast; linarith

/-- **Certificate, `(d_M, d_f) = (2, 2)`**: `N56 2 2 1 (1/2) (1/2) ≤ 10^178`. -/
theorem N56_22_le : N56 2 2 1 (1 / 2) (1 / 2) ≤ 10 ^ 178 := by
  have hcL := cL_22_ge
  have ht := tsb64_2
  have ht0 : 0 < tsb64 2 := tsb64_pos 2
  have hC2 : |C2T2_64 2 2 (tsb64 2) (cL64 2 2 1)| ≤
      2 * (2 * 106 * 9041880) * 2 / (tsb64 2 / 4 * (((1 / 221 : ℝ) ^ 2 / 2) / (27 * 183397))) := by
    have hc0 := cL64_pos 2 2 1
    calc |C2T2_64 2 2 (tsb64 2) (cL64 2 2 1)| =
        2 * (2 * 106 * 9041880) * 2 / (tsb64 2 / 4 * cL64 2 2 1) := by
          unfold C2T2_64 CM64
          rw [CR64_2, CA64_2, abs_of_nonneg (by positivity)]
          norm_num [Nat.factorial]
      _ ≤ _ := by gcongr
  have hCerr : |Cerr64 2 21761088| ≤ 90 * 6598 := by
    unfold Cerr64
    rw [abs_of_nonneg (by positivity)]
    have : Real.sqrt (2 * |(21761088 : ℝ)|) ≤ 6598 := sqrt_le_of_sq (by norm_num) (by norm_num)
    norm_num only at this ⊢
    nlinarith
  have hA2 : (500 * |Cerr64 2 21761088| / ((1 / 2) ^ 2 * s64 2)) ^ 2 ≤
      (500 * (90 * 6598) / ((1 / 2) ^ 2 * (tsb64 2 / 4))) ^ 2 := by
    unfold s64
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have k1 : 500 * (2 * (2 * 106 * 9041880) * 2 / (tsb64 2 / 4 * (((1 / 221 : ℝ) ^ 2 / 2) /
      (27 * 183397)))) + 1 ≤ 10 ^ 178 := by rw [ht]; norm_num
  have k2 : (500 * (90 * 6598) / ((1 / 2) ^ 2 * (tsb64 2 / 4))) ^ 2 + 1 ≤ (10 : ℝ) ^ 178 := by
    rw [ht]; norm_num
  unfold N56 NF56 nfail64
  rw [CDT1_2]
  refine max_le (max_le (max_le (max_le ?_ ?_) (max_le ?_ ?_)) ?_) (by norm_num)
  · exact n1_le _ _ (by norm_num) (by norm_num) (by norm_num)
  · exact n2_le _ _ (by norm_num) (by norm_num) (by norm_num)
  · refine ceil_add_le (by positivity) ?_
    push_cast; linarith
  · refine ceil_add_le (by positivity) ?_
    push_cast; linarith
  · unfold ncost64
    exact ceil_two_le (by norm_num) (by norm_num) (by norm_num)


set_option exponentiation.threshold 400 in
/-- **Certificate, `(d_M, d_f) = (3, 3)`**: `N56 3 3 1 (1/2) (1/2) ≤ 10^330`. -/
theorem N56_33_le : N56 3 3 1 (1 / 2) (1 / 2) ≤ 10 ^ 330 := by
  have hcL := cL_33_ge
  have ht := tsb64_3
  have ht0 : 0 < tsb64 3 := tsb64_pos 3
  have hC2 : |C2T2_64 3 3 (tsb64 3) (cL64 3 3 1)| ≤
      2 * (3 * 10500 * 10085931197396) * 6 /
        (tsb64 3 / 4 * (((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045))) := by
    have hc0 := cL64_pos 3 3 1
    calc |C2T2_64 3 3 (tsb64 3) (cL64 3 3 1)| =
        2 * (3 * 10500 * 10085931197396) * 6 / (tsb64 3 / 4 * cL64 3 3 1) := by
          unfold C2T2_64 CM64
          rw [CR64_3, CA64_3, abs_of_nonneg (by positivity)]
          norm_num [Nat.factorial]
      _ ≤ _ := by gcongr
  have hCerr : |Cerr64 3 752677632| ≤ 160 * 38800 := by
    unfold Cerr64
    rw [abs_of_nonneg (by positivity)]
    have : Real.sqrt (2 * |(752677632 : ℝ)|) ≤ 38800 := sqrt_le_of_sq (by norm_num) (by norm_num)
    norm_num only at this ⊢
    nlinarith
  have hA2 : (500 * |Cerr64 3 752677632| / ((1 / 2) ^ 2 * s64 3)) ^ 2 ≤
      (500 * (160 * 38800) / ((1 / 2) ^ 2 * (tsb64 3 / 4))) ^ 2 := by
    unfold s64
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have k1 : 500 * (2 * (3 * 10500 * 10085931197396) * 6 / (tsb64 3 / 4 *
      (((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045)))) + 1 ≤ 10 ^ 330 := by rw [ht]; norm_num
  have k2 : (500 * (160 * 38800) / ((1 / 2) ^ 2 * (tsb64 3 / 4))) ^ 2 + 1 ≤ (10 : ℝ) ^ 330 := by
    rw [ht]; norm_num
  unfold N56 NF56 nfail64
  rw [CDT1_3]
  refine max_le (max_le (max_le (max_le ?_ ?_) (max_le ?_ ?_)) ?_) (by norm_num)
  · exact n1_le _ _ (by norm_num) (by norm_num) (by norm_num)
  · exact n2_le _ _ (by norm_num) (by norm_num) (by norm_num)
  · refine ceil_add_le (by positivity) ?_
    push_cast; linarith
  · refine ceil_add_le (by positivity) ?_
    push_cast; linarith
  · unfold ncost64
    exact ceil_two_le (by norm_num) (by norm_num) (by norm_num)


/-- **Theorem 1 at `(d_M, d_f) = (D, D)`, `C = 1`, `ε ∈ [1/2, 1/2]`, for every `n ≥ M`**, given `N56 ≤ M`. -/
theorem part64_of_le (D : ℕ) (hD : 2 ≤ D) (M : ℕ) (hM : N56 D D 1 (1 / 2) (1 / 2) ≤ M) :
    ∀ n : ℕ, M ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK D D)) (pg : Prog (In56 n D D) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpec56 pm (KRK 1 n (eRK D (s64 D) (1 / 2))) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n D D (KRK 1 n (eRK D (s64 D) (1 / 2))) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
        ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
        ∀ (f0 : ℝ) (T : Tens n), TSymm D T → 0 < frob (T D) →
          stdGauss (CoefIdxD n D) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) D f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) D f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n D pm.cost ε (1 / 2) ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n D ε :=
  fun n hn => (part64_general D D hD le_rfl 1 (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)).2.2 n
    (hM.trans hn)


/-- **Theorem 1 certificate, `(d_M, d_f) = (2, 2)`**, `C = 1`, `ε_lo = ε_hi = 1/2`: the conclusion of
`part64_general` holds for every `n ≥ 10^178`. -/
theorem part64_22 : ∀ n : ℕ, 10 ^ 178 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK 2 2)) (pg : Prog (In56 n 2 2) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpec56 pm (KRK 1 n (eRK 2 (s64 2) (1 / 2))) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n 2 2 (KRK 1 n (eRK 2 (s64 2) (1 / 2))) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
        ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
        ∀ (f0 : ℝ) (T : Tens n), TSymm 2 T → 0 < frob (T 2) →
          stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) 2 f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) 2 f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n 2 pm.cost ε (1 / 2) ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n 2 ε :=
  part64_of_le 2 (by norm_num) (10 ^ 178) N56_22_le

/-- **Theorem 1 certificate, `(d_M, d_f) = (3, 3)`**, `C = 1`, `ε_lo = ε_hi = 1/2`: the conclusion of
`part64_general` holds for every `n ≥ 10^330`. -/
theorem part64_33 : ∀ n : ℕ, 10 ^ 330 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpec56 pm (KRK 1 n (eRK 3 (s64 3) (1 / 2))) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n 3 3 (KRK 1 n (eRK 3 (s64 3) (1 / 2))) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
        ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
        ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
          stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n 3 pm.cost ε (1 / 2) ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n 3 ε :=
  part64_of_le 3 (by norm_num) (10 ^ 330) N56_33_le

end BstLean.Part64
