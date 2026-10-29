import BstLean.Part223StatisticNorm
import BstLean.Part223SquaredLatitude

/-! Scalar node statistics from the same weighted first-layer fields. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part172
open BstLean.Part170 (mkR tA hB aLat)
open BstLean.Part161 (xLat momN)
open BstLean.Part162 (tanSq)
open BstLean.Part53 (unitF53)
open BstLean.Part220 (statisticsField)

variable {n : ℕ}

/-- Each retained-plane projection uses its own latitude statistic. -/
lemma planeStatistic_integral (hn : 3 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hOp : OpB A O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0)
    (i : Fin 3) (hi : i ≠ 2) (e : Fin (mA n) → ℝ)
    (he : ∀ v, statisticsField wr g i A v = e) :
    ∫ v, tanSq (fun x => e ⬝ᵥ reluV (A *ᵥ x))
        (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v ∂stdGauss (Fin (n - 1)) ≤
      (1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n * paperNodeStatistic wr g i A := by
  let K := (1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n
  have hK : 0 ≤ K := mul_nonneg (sub_nonneg.mpr hs) (tA_nonneg n)
  have hz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 := BstLean.Part168.stdGauss_zero (by omega : 1 ≤ n - 1)
    rw [ae_iff]
    simpa using h0
  have hEq : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      tanSq (fun x => e ⬝ᵥ reluV (A *ᵥ x))
        (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v = K * paperField wr g i A v := by
    filter_upwards [hz, hk] with v hv hkv
    have ht := tan_dot (c := mkR wr (A, 0)) (s := nodeS (mkR wr (A, 0)) g)
      (by omega) hc hs hv A e hkv
    rw [ht]
    have htf := statisticsTf_eq_paperPsi (by omega) wr g i A v
    simp only [Tf, he] at htf
    simp only [paperField, paperWeight, if_neg hi, mul_one, K]
    exact htf
  obtain ⟨B, hB⟩ := paperField_bounded (by omega) wr hc g hs i A hOp
  have hm := (paperField_measurable wr g i).of_uncurry_left (x := A)
  have hInt := mo_bdd_int (μ := stdGauss (Fin (n - 1))) hm hB
  have H := gd_int_le (hInt.const_mul K) (hEq.mono fun _ hv => hv.le)
  have hab : ∀ v, |K * paperField wr g i A v| = K * |paperField wr g i A v| := by
    intro v; rw [abs_mul, abs_of_nonneg hK]
  simp_rw [hab] at H
  rw [integral_const_mul] at H
  exact H.trans (mul_le_mul_of_nonneg_left
    (paperNodeStatistic_mean (by omega) wr hc g hs i A hOp) hK)

/-- The paper event's first two statistics control the installed plane trace. -/
theorem DstN_le_paperStatistics (hn : 3 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB A O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    DstN (mkR wr (A, 0)) g ≤
      (1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n *
        (paperNodeStatistic wr g 0 A + paperNodeStatistic wr g 1 A) / ((n : ℝ) - 2) := by
  have h0 := planeStatistic_integral hn wr hc g hs A hOp hk 0 (by decide)
    (e1v (mkR wr (A, 0))) (fun _ => rfl)
  have h1 := planeStatistic_integral hn wr hc g hs A hOp hk 1 (by decide)
    (e2v (mkR wr (A, 0)) g) (fun _ => rfl)
  have hD := DstN_le_tan hn (mkR wr (A, 0)) g hs hO hOp
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < n - 2)]
  have htot := hD.trans (add_le_add h0 h1)
  nlinarith only [htot]

theorem hUN_le_paperStatistics (hn : 3 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB A O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    hUN (mkR wr (A, 0)) g ≤
      (1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n *
        (paperNodeStatistic wr g 0 A + paperNodeStatistic wr g 1 A) / ((n : ℝ) - 2) := by
  rw [hUN_eq_DstN (by omega) (mkR wr (A, 0)) g hs hO hOp]
  exact DstN_le_paperStatistics hn wr hc g hs A hO hOp hk

#print axioms DstN_le_paperStatistics
#print axioms hUN_le_paperStatistics

lemma wT_le_activation (c : Ret n) (g : ℕ) (v : Fin (n - 1) → ℝ) :
    wT c g v ≤ tA n * normSq (aLat c (nodeS c g) v) := by
  unfold wT
  exact mul_le_mul_of_nonneg_left
    ((BstLean.Part167.normSq_perp_le _ _).trans (BstLean.Part167.normSq_perp_le _ _))
    (tA_nonneg n)

/-- The third paper field bounds the squared-energy gradient, with its activation weight. -/
theorem squaredEnergy_gradient (hn : 3 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      4 * wT (mkR wr (A, 0)) g v *
        tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0))
          (nodeS (mkR wr (A, 0)) g) v ≤
      (8 * tA n / (n : ℝ) * (1 - nodeS (mkR wr (0, 0)) g ^ 2)) *
        |paperField wr g 2 A v| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 := BstLean.Part168.stdGauss_zero (by omega : 1 ≤ n - 1)
    rw [ae_iff]
    simpa using h0
  let c := mkR wr (A, 0)
  have hrh : ∑ j, BstLean.Part134.res (hB c) (a1Bar c (nodeS c g)) j * hB c j = 0 := by
    rw [← BstLean.Part170.perp_eq_res]
    exact gr_perp_orth _ _
  filter_upwards [hz, hk] with v hv hkv
  have ht := tan_sqrtw (c := c) (by omega) hc hs hv A (tA n) (hB c)
    (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g))) hrh hkv
  change tanSq (SN c g) c (nodeS c g) v ≤
    Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g)
      (statisticsField wr g 2) A v at ht
  rw [statisticsTf_eq_paperPsi (by omega)] at ht
  have hq : 0 ≤ (1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n :=
    mul_nonneg (sub_nonneg.mpr hs) (tA_nonneg n)
  have hT := ht.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hq)
  have hW := wT_le_activation c g v
  have hw0 := wT_nonneg c g v
  have hact : 0 ≤ activationWeight wr g A v := by
    unfold activationWeight
    have := tA_nonneg n
    have := normSq_nonneg
      (reluV (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)))
    positivity
  calc
    _ ≤ 4 * wT c g v *
        ((1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n * |paperPsi wr g 2 A v|) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ 4 * (tA n * normSq (aLat c (nodeS c g) v)) *
        ((1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n * |paperPsi wr g 2 A v|) := by
      gcongr
    _ = _ := by
      simp only [paperField, paperWeight, ite_true, abs_mul, abs_of_nonneg hact]
      unfold activationWeight
      change 4 * (tA n * normSq (aLat c (nodeS c g) v)) *
        ((1 - nodeS (mkR wr (0, 0)) g ^ 2) * tA n * |paperPsi wr g 2 A v|) =
        (8 * tA n / (n : ℝ) * (1 - nodeS (mkR wr (0, 0)) g ^ 2)) *
          (|paperPsi wr g 2 A v| * (((n : ℝ) * tA n / 2) * normSq (aLat c (nodeS c g) v)))
      field_simp
      <;> ring

/-- The installed transverse energy variance follows from the weighted third statistic. -/
theorem energyVariance_le_paperStatistic (hn : 3 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB A O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    (∫ v, (wT (mkR wr (A, 0)) g v -
      ∫ w, wT (mkR wr (A, 0)) g w ∂stdGauss (Fin (n - 1))) ^ 2
        ∂stdGauss (Fin (n - 1))) ≤
      (8 * tA n / (n : ℝ) * (1 - nodeS (mkR wr (0, 0)) g ^ 2)) *
        paperNodeStatistic wr g 2 A / ((n : ℝ) - 2) := by
  let c := mkR wr (A, 0)
  have hL := S_lip (tA n) (hB c) (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g))) hO hOp
  have hhom := S_hom (tA n) (hB c)
    (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g))) A
  have h := squared_latitude_variance (Φ := SN c g) (s := nodeS c g)
    hn c hs (by positivity) hL hhom
  simp_rw [SN_eq, sq_sqrt (wT_nonneg _ _ _)] at h
  let K := 8 * tA n / (n : ℝ) * (1 - nodeS (mkR wr (0, 0)) g ^ 2)
  have hK : 0 ≤ K := mul_nonneg (by have := tA_nonneg n; positivity) (sub_nonneg.mpr hs)
  obtain ⟨B, hB⟩ := paperField_bounded (by omega) wr hc g hs 2 A hOp
  have hm := (paperField_measurable wr g 2).of_uncurry_left (x := A)
  have hi := (mo_bdd_int (μ := stdGauss (Fin (n - 1))) hm hB).abs.const_mul K
  have hInt := gd_int_le hi (squaredEnergy_gradient hn wr hc g hs A hk)
  simp_rw [abs_mul, abs_of_nonneg hK, abs_abs] at hInt
  rw [integral_const_mul] at hInt
  have hb := mul_le_mul_of_nonneg_left
    (paperNodeStatistic_mean (by omega) wr hc g hs 2 A hOp) hK
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < n - 2)]
  exact (mul_comm _ _).le.trans (h.trans (hInt.trans hb))

#print axioms squaredEnergy_gradient
#print axioms energyVariance_le_paperStatistic

noncomputable def energyGradientCoefficient (n : ℕ) (s : ℝ) : ℝ :=
  8 * tA n / (n : ℝ) * (1 - s ^ 2)

noncomputable def energyEighthBound (n : ℕ) (s M : ℝ) : ℝ :=
  BstLean.Part162.cLS 4 ^ 8 * (energyGradientCoefficient n s * M) ^ 4 *
    inverseRadius8 (n - 1)

/-- The centred eighth moment uses the same third statistic as the variance. -/
theorem energyEighth_le_paperStatistic (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB A O)
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) j ≠ 0) :
    (∫ v, (wT (mkR wr (A, 0)) g v -
      ∫ w, wT (mkR wr (A, 0)) g w ∂stdGauss (Fin (n - 1))) ^ 8
        ∂stdGauss (Fin (n - 1))) ≤
      energyEighthBound n (nodeS (mkR wr (0, 0)) g) (paperNodeStatistic wr g 2 A) := by
  let c := mkR wr (A, 0)
  let K := energyGradientCoefficient n (nodeS (mkR wr (0, 0)) g)
  let M := paperNodeStatistic wr g 2 A
  have hK : 0 ≤ K := mul_nonneg (by have := tA_nonneg n; positivity) (sub_nonneg.mpr hs)
  have hM : 0 ≤ M := paperNodeStatistic_nonneg wr g 2 A
  have hL := S_lip (tA n) (hB c) (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g))) hO hOp
  have hhom := S_hom (tA n) (hB c)
    (BstLean.Part134.res (hB c) (a1Bar c (nodeS c g))) A
  have h := squared_latitude_eight_exact (Φ := SN c g) (s := nodeS c g)
    hn c hs (by positivity) hL hhom
  simp_rw [SN_eq, sq_sqrt (wT_nonneg _ _ _)] at h
  obtain ⟨B, hB⟩ := paperField_bounded (by omega) wr hc g hs 2 A hOp
  have hm := (paperField_measurable wr g 2).of_uncurry_left (x := A)
  have hi := (mo_bdd_pow (μ := stdGauss (Fin (n - 1))) hm.abs
    (fun v => by simpa only [abs_abs] using hB v) 4).const_mul (K ^ 4)
  have hgrad := squaredEnergy_gradient (by omega) wr hc g hs A hk
  have hGI : (∫ v, |sqrt (4 * wT c g v * tanSq (SN c g) c (nodeS c g) v)| ^ 8
      ∂stdGauss (Fin (n - 1))) ≤ (sqrt (K * M)) ^ 8 := by
    have hpt : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        |sqrt (4 * wT c g v * tanSq (SN c g) c (nodeS c g) v)| ^ 8 ≤
          K ^ 4 * |paperField wr g 2 A v| ^ 4 := by
      filter_upwards [hgrad] with v hv
      rw [abs_of_nonneg (sqrt_nonneg _)]
      have hsq := pow_le_pow_left₀ (sqrt_nonneg _) (sqrt_le_sqrt hv) 8
      have he : (sqrt (K * |paperField wr g 2 A v|)) ^ 8 =
          K ^ 4 * |paperField wr g 2 A v| ^ 4 := by
        rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sq_sqrt (by positivity), mul_pow]
      exact hsq.trans_eq he
    have H := integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity) hi hpt
    rw [integral_const_mul] at H
    have hM4 : ∫ v, |paperField wr g 2 A v| ^ 4 ∂stdGauss (Fin (n - 1)) = M ^ 4 := by
      exact (BstLean.Part161.momN_pow _ (by norm_num : (4 : ℕ) ≠ 0) _).symm
    rw [hM4] at H
    refine H.trans_eq ?_
    rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sq_sqrt (mul_nonneg hK hM), mul_pow]
  have hGM := nd_momN_le_of_int (by norm_num : 0 < 8) (sqrt_nonneg (K * M)) hGI
  have hdim : 8 < n - 1 := by omega
  have hrad : 0 ≤ radiusFactor8 (n - 1) :=
    Real.rpow_nonneg (inverseRadius8_pos hdim).le _
  have hnorm := h.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hGM hrad)
    (BstLean.Part162.cLS_pos (by norm_num : 1 ≤ 4)).le)
  have hpow := nd_int_le_of_momN (by norm_num : 0 < 8) (by
    have := (BstLean.Part162.cLS_pos (by norm_num : 1 ≤ 4)).le
    positivity) hnorm
  simp_rw [Even.pow_abs (by decide : Even 8)] at hpow
  refine hpow.trans_eq ?_
  have hp : ∀ x : ℝ, 0 ≤ x → sqrt x ^ 8 = x ^ 4 := by
    intro x hx
    rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sq_sqrt hx]
  rw [mul_pow, mul_pow, hp _ (mul_nonneg hK hM), radiusFactor8_pow hdim]
  unfold energyEighthBound
  simp only [K, M, inv_pow, div_eq_mul_inv]
  ring

#print axioms energyEighth_le_paperStatistic
end BstLean.Part223
