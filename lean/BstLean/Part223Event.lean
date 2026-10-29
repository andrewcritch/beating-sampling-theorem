import BstLean.Part223Statistics

/-! One first-layer event pays for all three weighted latitude statistics. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (mkR)
open BstLean.Part220

noncomputable def weightedPaperStatistic {n J : ℕ} (wr : WRet n) (ν : Measure (Fin J))
    (node : Fin J → ℕ) (i : Fin 3) (A : Matrix (Fin (mA n)) (Fin n) ℝ) : ℝ≥0∞ :=
  ∫⁻ g, latitudeStatistic64 (stdGauss (Fin (n - 1))) (paperField wr (node g) i A) ∂ν

def paperStatisticsEvent {n J : ℕ} (wr : WRet n) (ν : Measure (Fin J))
    (node : Fin J → ℕ) (C : ℝ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | ∀ i, weightedPaperStatistic wr ν node i A ≤ ENNReal.ofReal (C ^ 64)}

lemma weightedPaperStatistic_measurable {n J : ℕ} (wr : WRet n) (ν : Measure (Fin J))
    [SFinite ν] (node : Fin J → ℕ) (i : Fin 3) :
    Measurable (weightedPaperStatistic wr ν node i) := by
  have hm : ∀ g : Fin J, Measurable (fun A =>
      latitudeStatistic64 (stdGauss (Fin (n - 1))) (paperField wr (node g) i A)) := by
    intro g
    exact ((paperField_measurable wr (node g) i).abs.pow_const 4 |>.ennreal_ofReal
      |>.lintegral_prod_right').pow_const 16
  exact (measurable_from_prod_countable_right hm).lintegral_prod_left

lemma paperStatisticsEvent_measurable {n J : ℕ} (wr : WRet n) (ν : Measure (Fin J))
    [SFinite ν] (node : Fin J → ℕ) (C : ℝ) :
    MeasurableSet (paperStatisticsEvent wr ν node C) := by
  have he : paperStatisticsEvent wr ν node C =
      ⋂ i, {A | weightedPaperStatistic wr ν node i A ≤ ENNReal.ofReal (C ^ 64)} := by
    ext A
    simp only [paperStatisticsEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  exact MeasurableSet.iInter fun i => measurableSet_le
    (weightedPaperStatistic_measurable wr ν node i) measurable_const

theorem weightedPaperStatistic_moment {n q J : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) (i : Fin 3) :
    ∫⁻ A, weightedPaperStatistic wr ν node i A ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (paperStatisticsBound n q ^ 64) := by
  have hm : Measurable (fun p : Fin J × Matrix (Fin (mA n)) (Fin n) ℝ =>
      latitudeStatistic64 (stdGauss (Fin (n - 1))) (paperField wr (node p.1) i p.2)) := by
    apply measurable_from_prod_countable_right
    intro g
    exact ((paperField_measurable wr (node g) i).abs.pow_const 4 |>.ennreal_ofReal
      |>.lintegral_prod_right').pow_const 16
  unfold weightedPaperStatistic
  rw [← lintegral_lintegral_swap hm.aemeasurable]
  refine (lintegral_mono fun g => paperLatitude_moment64 hn hq wr hc (node g) (hs g) i).trans ?_
  rw [lintegral_const]
  exact (mul_le_mul' le_rfl hmass).trans_eq (mul_one _)

/-- The node measure is fixed before drawing the first layer. Its total mass is at most one. -/
theorem paperStatistics_charge {n q J : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    {C : ℝ} (hC : 0 < C) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (paperStatisticsEvent wr ν node C)ᶜ ≤
      3 * (paperStatisticsBound n q / C) ^ 64 := by
  let σ := gaussMat (mA n) n (2 / (n : ℝ))
  have hCp : 0 < C ^ 64 := pow_pos hC _
  have hi : ∀ i : Fin 3,
      σ {A | ENNReal.ofReal (C ^ 64) < weightedPaperStatistic wr ν node i A} ≤
        ENNReal.ofReal ((paperStatisticsBound n q / C) ^ 64) := by
    intro i
    have hmark := meas_ge_le_lintegral_div (μ := σ)
      (weightedPaperStatistic_measurable wr ν node i).aemeasurable
      (ne_of_gt (ENNReal.ofReal_pos.mpr hCp)) ENNReal.ofReal_ne_top
    have hsub : {A | ENNReal.ofReal (C ^ 64) < weightedPaperStatistic wr ν node i A} ⊆
        {A | ENNReal.ofReal (C ^ 64) ≤ weightedPaperStatistic wr ν node i A} := by
      intro A hA
      change ENNReal.ofReal (C ^ 64) < weightedPaperStatistic wr ν node i A at hA
      change ENNReal.ofReal (C ^ 64) ≤ weightedPaperStatistic wr ν node i A
      exact le_of_lt hA
    refine (measure_mono hsub).trans (hmark.trans ?_)
    refine (ENNReal.div_le_div_right
      (weightedPaperStatistic_moment hn hq wr hc ν hmass node hs i) _).trans_eq ?_
    rw [← ENNReal.ofReal_div_of_pos hCp, div_pow]
  have he : (paperStatisticsEvent wr ν node C)ᶜ =
      ⋃ i : Fin 3, {A | ENNReal.ofReal (C ^ 64) < weightedPaperStatistic wr ν node i A} := by
    ext A
    simp [paperStatisticsEvent, not_forall]
  have hprob : σ (paperStatisticsEvent wr ν node C)ᶜ ≤
      ENNReal.ofReal (3 * (paperStatisticsBound n q / C) ^ 64) := by
    rw [he]
    refine (measure_iUnion_le _).trans ?_
    rw [tsum_fintype]
    calc
      (∑ i : Fin 3, σ {A | ENNReal.ofReal (C ^ 64) <
          weightedPaperStatistic wr ν node i A}) ≤
          ∑ _i : Fin 3, ENNReal.ofReal ((paperStatisticsBound n q / C) ^ 64) :=
        Finset.sum_le_sum fun i _ => hi i
      _ = ENNReal.ofReal (3 * (paperStatisticsBound n q / C) ^ 64) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by norm_num)
      (pow_nonneg (div_nonneg (paperStatisticsBound_nonneg n q) hC.le) 64)) hprob

/-- The exact order64 threshold pays one ten-thousandth once for all three fields. -/
theorem paperStatistics_oneTenThousand {n q J : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (paperStatisticsEvent wr ν node (statisticsConstant (paperStatisticsBound n q)))ᶜ ≤
        1 / 10000 := by
  have hB := paperStatisticsBound_pos hn hq
  have h := paperStatistics_charge hn hq wr hc ν hmass node hs (statisticsConstant_pos hB)
  rwa [three_statistics_price hB] at h

#print axioms paperStatistics_charge
#print axioms paperStatistics_oneTenThousand
end BstLean.Part223
