import BstLean.Part280Prices
import BstLean.Part276World

/-! Part 280, task 2 (charge): one first-layer event and the four original
second-layer moments pay for the M2 sharp table event, for every `n` in 11883–12224.
The total retained charge is at most `126145e-9 + 717e-6 ≤ 9/10000`. -/
namespace BstLean.Part280
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223
open BstLean.Part252 (product_charge_ae exp_neg12_row)
open BstLean.Part276 (fourA)

variable {n : ℕ}

theorem first_matrix_rowN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) (c : Ret n)
    (hc : A1 c ∈ Eop n) : OpB (A1 c) 160 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : (n : ℝ) ≤ 12224 := by exact_mod_cast hn2
  have hx0 : (0 : ℝ) < n := by linarith
  apply opB_of_opN
  refine hc.trans ?_
  have hA : √(2 / (n : ℝ)) * (n : ℝ) ≤ 15637 / 100 := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by norm_num)
    rw [mul_pow, sq_sqrt (by positivity), div_mul_eq_mul_div, div_le_iff₀ hx0]
    nlinarith
  have hs2 : √(2 / (n : ℝ)) * √(n : ℝ) = √2 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hx0.ne']
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have e : √(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ)) =
      √(2 / (n : ℝ)) * (n : ℝ) + 2 * (√(2 / (n : ℝ)) * √(n : ℝ)) := by ring
  rw [e, hs2]
  linarith

theorem first_charge_priceN (hn : 11883 ≤ n) :
    exp (-(n : ℝ) / 2) + 2 / 10 ^ 5 + 1 / 10000 ≤ (126145 / 10 ^ 9 : ℝ) := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have he : exp (-(n : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by linarith : -(n : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem total_charge_priceN : (126145 / 10 ^ 9 : ℝ) + 717 / 10 ^ 6 ≤ 9 / 10000 := by
  norm_num

def sharpVarianceEventN (n : ℕ) (wr : WRet n) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {X | ∀ g : Fin (Js n),
    17 / (100 * (n : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem sharpVarianceEventN_measurable (wr : WRet n) :
    MeasurableSet (sharpVarianceEventN n wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : sharpVarianceEventN n wr = ⋂ g : Fin (Js n),
      {X | 17 / (100 * (n : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [sharpVarianceEventN, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem sharpVarianceEventN_charge (hn : 11883 ≤ n) {wr : WRet n} (hw : tightG wr) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (sharpVarianceEventN n wr)ᶜ ≤ 2 / 10 ^ 5 := by
  have hs : (sharpVarianceEventN n wr)ᶜ ⊆ {X | ∃ g < Js n,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (BstLean.Part276.node_trace_charge8000 (by omega) hw.1 (fun g hg => ?_))
  have h := node_geometryN hn hw (0, 0) hg
  exact ⟨h.1, h.2.1, by linarith [h.2.2]⟩

def sharpFirstEventN (hn : 1 ≤ n) (wr : WRet n) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  (Eop n ∩ sharpVarianceEventN n wr) ∩
    paperStatisticsEvent wr (nodeMeasureN hn wr) Fin.val (statisticsConstant (paperBound256 n))

theorem sharpFirstEventN_measurable (hn : 1 ≤ n) (wr : WRet n) :
    MeasurableSet (sharpFirstEventN hn wr) :=
  ((measurableSet_Eop _).inter (sharpVarianceEventN_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (nodeMeasureN hn wr) Fin.val _)

theorem sharpFirstEventN_charge (hn : 11883 ≤ n) (hn2 : n ≤ 12224) {wr : WRet n}
    (hw : tightG wr) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (sharpFirstEventN (by omega) wr)ᶜ ≤
      (126145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by omega) hw.1
  have hs (g : Fin (Js n)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := node_geometryN hn hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by omega) (by omega)
    wr hc (nodeMeasureN (by omega) wr) (nodeMeasureN_mass (by omega) wr).le Fin.val hs
  unfold sharpFirstEventN
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by omega))
      (sharpVarianceEventN_charge hn hw))) hstat)).trans (first_charge_priceN hn)

def sharpBadPairN (n : ℕ) (wr : WRet n) : Set (AHid n) := {θ | mkR wr θ ∉ sharpTableN n}

theorem sharpBadPairN_measurable (wr : WRet n) : MeasurableSet (sharpBadPairN n wr) :=
  sharpTableN_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem sharp_conditional_chargeN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) {wr : WRet n}
    (hwt : tightG wr) :
    ∀ᵐ X ∂gaussMat (mA n) n (2 / (n : ℝ)), X ∈ sharpFirstEventN (by omega) wr →
      (gaussMat (mA n) (mA n) (tA n))
        {M | (X, M) ∈ sharpBadPairN n wr} ≤ ENNReal.ofReal (717 / 10 ^ 6 : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hw : windowW wr := hwt.1
  have hc := BstLean.Part172.sg_wr_ne hn1 hw
  have hs (g : Fin (Js n)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := node_geometryN hn hwt (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js n)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (58 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (node_geometryN hn hwt (0, 0) g.isLt).2.2⟩
  have h12 := nodeMeasureN_moment12 hn hwt
  filter_upwards [paperNodes_kink_ae (by omega) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js n)) := (hvar g).1
  have hmax (g : Fin (Js n)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * n) : ℝ) := by
    refine (hvar g).2.trans ?_
    have h1 : 42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ≤
        42 / (10 * (n : ℝ)) * (58 / 100) :=
      mul_le_mul_of_nonneg_left (hq g).2 (by positivity)
    have h2 : 42 / (10 * (n : ℝ)) * (58 / 100) ≤ 26 / (10 * n) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      norm_num
    exact h1.trans h2
  have htrace (g : Fin (Js n)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / n) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by positivity)]
    have e : (42 / 10 : ℝ) / n = 42 / (10 * n) := by
      rw [div_div]
    rw [e]
    exact (hvar g).2
  have hA (i : Fin 4) : 0 < fourA i := BstLean.Part276.fourA_pos i
  have hgap : 0 < envelopeGap n (58 / 100) 160 (17 / (100 * n)) :=
    lt_of_lt_of_le (by norm_num) (envelopeGap_geN hn hn2)
  have hmark := paperOriginalFour_markov (by omega) wr hc (nodeMeasureN hn1 wr)
    (nodeMeasureN_mass hn1 wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 58 / 100)
    (by norm_num : (0 : ℝ) ≤ 160) (by positivity : (0 : ℝ) < 17 / (100 * n))
    (by positivity : (0 : ℝ) ≤ 26 / (10 * n)) (statistics_constant_posN hn hn2).le
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 5275 / 10000)
    (first_matrix_rowN hn hn2 (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace hgap h12 hk fourA hA
  have hreal : (gaussMat (mA n) (mA n) (tA n)).real
      {M | (X, M) ∈ sharpBadPairN n wr} ≤ (717 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (sharpTableN_bad_subset hn1 (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans (four_priceN hn hn2)
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem sharp_world_chargeN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) (wr : WRet n) :
    (nuA n).real (sharpBadPairN n wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : tightG wr
  · exact (product_charge_ae _ _ (sharpFirstEventN_measurable (by omega) wr)
      (sharpBadPairN_measurable wr) (by norm_num) (by norm_num)
      (sharpFirstEventN_charge hn hn2 hw)
      (sharp_conditional_chargeN hn hn2 hw)).trans total_charge_priceN
  · have he : sharpBadPairN n wr = ∅ := by
      ext θ
      simp only [sharpBadPairN, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

def sharpPairEventN (n : ℕ) : Set (WRet n × AHid n) :=
  {p | mkR p.1 p.2 ∈ sharpTableN n}

theorem sharpPairEventN_measurable : MeasurableSet (sharpPairEventN n) :=
  sharpTableN_measurable.preimage measurable_mkR

/-- Task 2: the retained-distribution payment of the M2 sharp table event, for every
`n` in 11883–12224. -/
theorem sharpTableN_ret_charge (hn : 11883 ≤ n) (hn2 : n ≤ 12224) :
    (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres n) sharpPairEventN_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) (sharp_world_chargeN hn hn2)
  convert h using 1
  congr 1

end BstLean.Part280
