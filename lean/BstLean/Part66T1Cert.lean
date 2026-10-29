import BstLean.Part64Cert
import BstLean.Part66T1Final

/-!
# Part 66: numeric certificates for Theorem 1 at the weighted-rotation level `tW`

At failure `1/100`, `C = 1`, `ε_lo = ε_hi = 1/2`, small-ball level `tW (2k) (1/200)`:

* `N56W_22_le : N56L 2 2 1 (1/2) (1/2) (tW 4 (1/200)) ≤ 10^92` (old `10^178`);
* `N56W_33_le : N56L 3 3 1 (1/2) (1/2) (tW 6 (1/200)) ≤ 10^138` (old `10^330`);
* `part66T1_of_le`: the conclusion of `part66T1_general` at `(D, D)` for every `n ≥ M`, given
  `N56L … ≤ M` and the hypothesis `SBLevel (2D) (1/200) (tW (2D) (1/200))`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part66

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part56
open BstLean.Part64

lemma tW_4 : tW 4 (1 / 200) = (1 / 32400) ^ 8 := by unfold tW; norm_num

lemma tW_6 : tW 6 (1 / 200) = (1 / 67600) ^ 12 := by unfold tW; norm_num

/-- **Certificate, `(d_M, d_f) = (2, 2)`**: `N56L 2 2 1 (1/2) (1/2) (tW 4 (1/200)) ≤ 10^92`. -/
theorem N56W_22_le : N56L 2 2 1 (1 / 2) (1 / 2) (tW 4 (1 / 200)) ≤ 10 ^ 92 := by
  have hcL := cL_22_ge
  have ht := tW_4
  have ht0 : 0 < tW 4 (1 / 200) := tW_pos 4 _ (by norm_num)
  have hC2 : |C2T2_64 2 2 (tW 4 (1 / 200)) (cL64 2 2 1)| ≤
      2 * (2 * 106 * 9041880) * 2 / (tW 4 (1 / 200) / 4 * (((1 / 221 : ℝ) ^ 2 / 2) / (27 * 183397))) := by
    have hc0 := cL64_pos 2 2 1
    calc |C2T2_64 2 2 (tW 4 (1 / 200)) (cL64 2 2 1)| =
        2 * (2 * 106 * 9041880) * 2 / (tW 4 (1 / 200) / 4 * cL64 2 2 1) := by
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
  have hA2 : (500 * |Cerr64 2 21761088| / ((1 / 2) ^ 2 * (tW 4 (1 / 200) / 4))) ^ 2 ≤
      (500 * (90 * 6598) / ((1 / 2) ^ 2 * (tW 4 (1 / 200) / 4))) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have k1 : 500 * (2 * (2 * 106 * 9041880) * 2 / (tW 4 (1 / 200) / 4 * (((1 / 221 : ℝ) ^ 2 / 2) /
      (27 * 183397)))) + 1 ≤ 10 ^ 92 := by rw [ht]; norm_num
  have k2 : (500 * (90 * 6598) / ((1 / 2) ^ 2 * (tW 4 (1 / 200) / 4))) ^ 2 + 1 ≤ (10 : ℝ) ^ 92 := by
    rw [ht]; norm_num
  unfold N56L NF56L nfail64
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

/-- **Certificate, `(d_M, d_f) = (3, 3)`**: `N56L 3 3 1 (1/2) (1/2) (tW 6 (1/200)) ≤ 10^138`. -/
theorem N56W_33_le : N56L 3 3 1 (1 / 2) (1 / 2) (tW 6 (1 / 200)) ≤ 10 ^ 138 := by
  have hcL := cL_33_ge
  have ht := tW_6
  have ht0 : 0 < tW 6 (1 / 200) := tW_pos 6 _ (by norm_num)
  have hC2 : |C2T2_64 3 3 (tW 6 (1 / 200)) (cL64 3 3 1)| ≤
      2 * (3 * 10500 * 10085931197396) * 6 /
        (tW 6 (1 / 200) / 4 * (((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045))) := by
    have hc0 := cL64_pos 3 3 1
    calc |C2T2_64 3 3 (tW 6 (1 / 200)) (cL64 3 3 1)| =
        2 * (3 * 10500 * 10085931197396) * 6 / (tW 6 (1 / 200) / 4 * cL64 3 3 1) := by
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
  have hA2 : (500 * |Cerr64 3 752677632| / ((1 / 2) ^ 2 * (tW 6 (1 / 200) / 4))) ^ 2 ≤
      (500 * (160 * 38800) / ((1 / 2) ^ 2 * (tW 6 (1 / 200) / 4))) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have k1 : 500 * (2 * (3 * 10500 * 10085931197396) * 6 / (tW 6 (1 / 200) / 4 *
      (((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045)))) + 1 ≤ 10 ^ 138 := by rw [ht]; norm_num
  have k2 : (500 * (160 * 38800) / ((1 / 2) ^ 2 * (tW 6 (1 / 200) / 4))) ^ 2 + 1 ≤ (10 : ℝ) ^ 138 := by
    rw [ht]; norm_num
  unfold N56L NF56L nfail64
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

/-- **Theorem 1 at `(D, D)`, `C = 1`, `ε ∈ [1/2, 1/2]`, level `tW (2D) (1/200)`, for every
`n ≥ M`**, given `N56L ≤ M` and the small-ball level hypothesis. -/
theorem part66T1_of_le (D : ℕ) (hD : 2 ≤ D) (hSB : SBLevel (2 * D) (1 / 200) (tW (2 * D) (1 / 200)))
    (M : ℕ) (hM : N56L D D 1 (1 / 2) (1 / 2) (tW (2 * D) (1 / 200)) ≤ M) :
    ∀ n : ℕ, M ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK D D)) (pg : Prog (In56 n D D) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧
        MomSpec56 pm (KRK 1 n (eRK D (tW (2 * D) (1 / 200) / 4) (1 / 2))) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n D D (KRK 1 n (eRK D (tW (2 * D) (1 / 200) / 4) (1 / 2))) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
        ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
        ∀ (f0 : ℝ) (T : Tens n), TSymm D T → 0 < frob (T D) →
          stdGauss (CoefIdxD n D) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) D f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) D f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n D pm.cost ε (1 / 2) ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n D ε :=
  fun n hn => (part66T1_general D D hD le_rfl 1 (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)
    (tW (2 * D) (1 / 200)) (tW_pos _ _ (by norm_num)) hSB).2.2 n (hM.trans hn)

end BstLean.Part66
