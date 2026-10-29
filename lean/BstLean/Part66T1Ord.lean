import BstLean.Part66T1Cert
import BstLean.Part66LevelOrd

/-!
# Part 66: Theorem 1 at the ordered-node small-ball level `tO`

At failure `1/100`, `C = 1`, `ε_lo = ε_hi = 1/2`, level `tO (2k) (1/200)`
(`Part66LevelOrd.sb_level_ordered`):

* `N56O_22_le : N56L 2 2 1 (1/2) (1/2) (tO 4 (1/200)) ≤ 10^86` (old `10^178`; `tW`: `10^92`);
* `N56O_33_le : N56L 3 3 1 (1/2) (1/2) (tO 6 (1/200)) ≤ 10^125` (old `10^330`; `tW`: `10^138`);
* `part66T1_of_le_lvl`: the certificate shape at any level `t > 0`;
* `part66T1O_22`, `part66T1O_33`: unconditional, every `n ≥ 10^86` (resp. `n ≥ 10^125`).

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

lemma tO_4 : tO 4 (1 / 200) = (1 / 200) ^ 8 * 40320 / (4 ^ 8 * 9 ^ 15) := by
  unfold tO; norm_num [Nat.factorial]

lemma tO_6 : tO 6 (1 / 200) = (1 / 200) ^ 12 * 479001600 / (4 ^ 12 * 13 ^ 23) := by
  unfold tO; norm_num [Nat.factorial]

/-- **Certificate, `(d_M, d_f) = (2, 2)`**: `N56L 2 2 1 (1/2) (1/2) (tW 4 (1/200)) ≤ 10^86`. -/
theorem N56O_22_le : N56L 2 2 1 (1 / 2) (1 / 2) (tO 4 (1 / 200)) ≤ 10 ^ 86 := by
  have hcL := cL_22_ge
  have ht := tO_4
  have ht0 : 0 < tO 4 (1 / 200) := tO_pos 4 _ (by norm_num)
  have hC2 : |C2T2_64 2 2 (tO 4 (1 / 200)) (cL64 2 2 1)| ≤
      2 * (2 * 106 * 9041880) * 2 / (tO 4 (1 / 200) / 4 * (((1 / 221 : ℝ) ^ 2 / 2) / (27 * 183397))) := by
    have hc0 := cL64_pos 2 2 1
    calc |C2T2_64 2 2 (tO 4 (1 / 200)) (cL64 2 2 1)| =
        2 * (2 * 106 * 9041880) * 2 / (tO 4 (1 / 200) / 4 * cL64 2 2 1) := by
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
  have hA2 : (500 * |Cerr64 2 21761088| / ((1 / 2) ^ 2 * (tO 4 (1 / 200) / 4))) ^ 2 ≤
      (500 * (90 * 6598) / ((1 / 2) ^ 2 * (tO 4 (1 / 200) / 4))) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have k1 : 500 * (2 * (2 * 106 * 9041880) * 2 / (tO 4 (1 / 200) / 4 * (((1 / 221 : ℝ) ^ 2 / 2) /
      (27 * 183397)))) + 1 ≤ 10 ^ 86 := by rw [ht]; norm_num
  have k2 : (500 * (90 * 6598) / ((1 / 2) ^ 2 * (tO 4 (1 / 200) / 4))) ^ 2 + 1 ≤ (10 : ℝ) ^ 86 := by
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

/-- **Certificate, `(d_M, d_f) = (3, 3)`**: `N56L 3 3 1 (1/2) (1/2) (tW 6 (1/200)) ≤ 10^125`. -/
theorem N56O_33_le : N56L 3 3 1 (1 / 2) (1 / 2) (tO 6 (1 / 200)) ≤ 10 ^ 125 := by
  have hcL := cL_33_ge
  have ht := tO_6
  have ht0 : 0 < tO 6 (1 / 200) := tO_pos 6 _ (by norm_num)
  have hC2 : |C2T2_64 3 3 (tO 6 (1 / 200)) (cL64 3 3 1)| ≤
      2 * (3 * 10500 * 10085931197396) * 6 /
        (tO 6 (1 / 200) / 4 * (((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045))) := by
    have hc0 := cL64_pos 3 3 1
    calc |C2T2_64 3 3 (tO 6 (1 / 200)) (cL64 3 3 1)| =
        2 * (3 * 10500 * 10085931197396) * 6 / (tO 6 (1 / 200) / 4 * cL64 3 3 1) := by
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
  have hA2 : (500 * |Cerr64 3 752677632| / ((1 / 2) ^ 2 * (tO 6 (1 / 200) / 4))) ^ 2 ≤
      (500 * (160 * 38800) / ((1 / 2) ^ 2 * (tO 6 (1 / 200) / 4))) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have k1 : 500 * (2 * (3 * 10500 * 10085931197396) * 6 / (tO 6 (1 / 200) / 4 *
      (((1 / 221 : ℝ) ^ 3 / 2) / (64 * 7274827045)))) + 1 ≤ 10 ^ 125 := by rw [ht]; norm_num
  have k2 : (500 * (160 * 38800) / ((1 / 2) ^ 2 * (tO 6 (1 / 200) / 4))) ^ 2 + 1 ≤ (10 : ℝ) ^ 125 := by
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

/-- **Theorem 1 at `(D, D)`, `C = 1`, `ε ∈ [1/2, 1/2]`, at any small-ball level `t > 0`, for every
`n ≥ M`**, given `N56L … t ≤ M`. -/
theorem part66T1_of_le_lvl (D : ℕ) (hD : 2 ≤ D) (t : ℝ) (ht : 0 < t) (hSB : SBLevel (2 * D) (1 / 200) t)
    (M : ℕ) (hM : N56L D D 1 (1 / 2) (1 / 2) t ≤ M) :
    ∀ n : ℕ, M ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK D D)) (pg : Prog (In56 n D D) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧
        MomSpec56 pm (KRK 1 n (eRK D (t / 4) (1 / 2))) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n D D (KRK 1 n (eRK D (t / 4) (1 / 2))) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t' : ℝ, 0 ≤ t' → t' ≤ 1 * n →
        ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
        ∀ (f0 : ℝ) (T : Tens n), TSymm D T → 0 < frob (T D) →
          stdGauss (CoefIdxD n D) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t' v) D f0 T (unitOfD Z) <
              (BofQ (lawRK n t' v) D f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t' v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n D pm.cost ε (1 / 2) ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n D ε :=
  fun n hn => (part66T1_general D D hD le_rfl 1 (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)
    t ht hSB).2.2 n (hM.trans hn)

/-- **Theorem 1 certificate, `(2,2)`**, level `tO 4 (1/200)`: every `n ≥ 10^86`. -/
theorem part66T1O_22 : ∀ n : ℕ, 10 ^ 86 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK 2 2)) (pg : Prog (In56 n 2 2) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧
        MomSpec56 pm (KRK 1 n (eRK 2 (tO (2 * 2) (1 / 200) / 4) (1 / 2))) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n 2 2 (KRK 1 n (eRK 2 (tO (2 * 2) (1 / 200) / 4) (1 / 2))) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
        ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
        ∀ (f0 : ℝ) (T : Tens n), TSymm 2 T → 0 < frob (T 2) →
          stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) 2 f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) 2 f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n 2 pm.cost ε (1 / 2) ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n 2 ε :=
  part66T1_of_le_lvl 2 (by norm_num) (tO (2 * 2) (1 / 200)) (tO_pos _ _ (by norm_num)) (sb_level_ordered (2 * 2) (by norm_num) (1 / 200) (by norm_num))
    (10 ^ 86) N56O_22_le

/-- **Theorem 1 certificate, `(3,3)`**, level `tO 6 (1/200)`: every `n ≥ 10^125`. -/
theorem part66T1O_33 : ∀ n : ℕ, 10 ^ 125 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧
        MomSpec56 pm (KRK 1 n (eRK 3 (tO (2 * 3) (1 / 200) / 4) (1 / 2))) ∧
        GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n 3 3 (KRK 1 n (eRK 3 (tO (2 * 3) (1 / 200) / 4) (1 / 2))) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
        ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
        ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
          stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n 3 pm.cost ε (1 / 2) ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n 3 ε :=
  part66T1_of_le_lvl 3 (by norm_num) (tO (2 * 3) (1 / 200)) (tO_pos _ _ (by norm_num)) (sb_level_ordered (2 * 3) (by norm_num) (1 / 200) (by norm_num))
    (10 ^ 125) N56O_33_le

end BstLean.Part66
