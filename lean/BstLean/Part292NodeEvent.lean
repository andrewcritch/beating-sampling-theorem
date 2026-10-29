import BstLean.Part292Statistics
import BstLean.Part239NodeSupply

/-! A single event supplies all three weighted statistics throughout the band. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (mkR)
open BstLean.Part239

theorem weightedPaperStatistic_moment {n J : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) (i : Fin 3) :
    ∫⁻ A, weightedPaperStatistic wr ν node i A ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal ((251898099 / 100000000 : ℝ) ^ 416) := by
  have hm : Measurable (fun p : Fin J × Matrix (Fin (mA n)) (Fin n) ℝ =>
      latitudeStatistic416 (stdGauss (Fin (n - 1))) (paperField wr (node p.1) i p.2)) := by
    apply measurable_from_prod_countable_right
    intro g
    exact ((paperField_measurable wr (node g) i).abs.pow_const 4 |>.ennreal_ofReal
      |>.lintegral_prod_right').pow_const 104
  unfold weightedPaperStatistic
  rw [← lintegral_lintegral_swap hm.aemeasurable]
  refine (lintegral_mono fun g => BstLean.Part292.paperLatitude_moment416 hn hn' wr hc (node g) (hs g) i).trans ?_
  rw [lintegral_const]
  exact (mul_le_mul' le_rfl hmass).trans_eq (mul_one _)

/-- The node measure is fixed before drawing the first layer. Its total mass is at most one. -/
theorem paperStatistics_charge {n J : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    {C : ℝ} (hC : 0 < C) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (paperStatisticsEvent wr ν node C)ᶜ ≤
      3 * ((251898099 / 100000000 : ℝ) / C) ^ 416 := by
  let σ := gaussMat (mA n) n (2 / (n : ℝ))
  have hCp : 0 < C ^ 416 := pow_pos hC _
  have hi : ∀ i : Fin 3,
      σ {A | ENNReal.ofReal (C ^ 416) < weightedPaperStatistic wr ν node i A} ≤
        ENNReal.ofReal (((251898099 / 100000000 : ℝ) / C) ^ 416) := by
    intro i
    have hmark := meas_ge_le_lintegral_div (μ := σ)
      (weightedPaperStatistic_measurable wr ν node i).aemeasurable
      (ne_of_gt (ENNReal.ofReal_pos.mpr hCp)) ENNReal.ofReal_ne_top
    have hsub : {A | ENNReal.ofReal (C ^ 416) < weightedPaperStatistic wr ν node i A} ⊆
        {A | ENNReal.ofReal (C ^ 416) ≤ weightedPaperStatistic wr ν node i A} := by
      intro A hA
      change ENNReal.ofReal (C ^ 416) < weightedPaperStatistic wr ν node i A at hA
      change ENNReal.ofReal (C ^ 416) ≤ weightedPaperStatistic wr ν node i A
      exact le_of_lt hA
    refine (measure_mono hsub).trans (hmark.trans ?_)
    refine (ENNReal.div_le_div_right
      (weightedPaperStatistic_moment hn hn' wr hc ν hmass node hs i) _).trans_eq ?_
    rw [← ENNReal.ofReal_div_of_pos hCp]
    simp only [div_pow]
  have he : (paperStatisticsEvent wr ν node C)ᶜ =
      ⋃ i : Fin 3, {A | ENNReal.ofReal (C ^ 416) < weightedPaperStatistic wr ν node i A} := by
    ext A
    simp [paperStatisticsEvent, not_forall]
  have hprob : σ (paperStatisticsEvent wr ν node C)ᶜ ≤
      ENNReal.ofReal (3 * ((251898099 / 100000000 : ℝ) / C) ^ 416) := by
    rw [he]
    refine (measure_iUnion_le _).trans ?_
    rw [tsum_fintype]
    calc
      (∑ i : Fin 3, σ {A | ENNReal.ofReal (C ^ 416) <
          weightedPaperStatistic wr ν node i A}) ≤
          ∑ _i : Fin 3, ENNReal.ofReal (((251898099 / 100000000 : ℝ) / C) ^ 416) :=
        Finset.sum_le_sum fun i _ => hi i
      _ = ENNReal.ofReal (3 * ((251898099 / 100000000 : ℝ) / C) ^ 416) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by norm_num)
      (pow_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 251898099 / 100000000) hC.le) 416)) hprob


theorem statistics_price_bound :
    3 * ((251898099 / 100000000 : ℝ) / (517 / 200)) ^ 416 ≤ 1 / 10000 := by
  have h : ((251898099 / 100000000 : ℝ) / (517 / 200)) ^ 32 ≤ 438 / 1000 := by
    norm_num
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    ((251898099 / 100000000 : ℝ) / (517 / 200)) ^ 32) h 13
  rw [← pow_mul] at hp
  rw [show (32 : ℕ)*13 = 416 by norm_num] at hp
  have hc : (3 : ℝ) * (438 / 1000 : ℝ) ^ 13 ≤ 1 / 10000 := by norm_num
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3)).trans hc

theorem node416_charge_band {n J : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν Set.univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (node416Event wr ν node (517 / 200))ᶜ ≤ 1 / 10000 := by
  rw [node416Event_eq (by omega) wr hc ν node hs (by norm_num : (0 : ℝ) ≤ 517 / 200)]
  exact (paperStatistics_charge hn hn' wr hc ν hmass node hs (by norm_num)).trans
    statistics_price_bound

end BstLean.Part292

/-- info: 'BstLean.Part292.node416_charge_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.node416_charge_band
