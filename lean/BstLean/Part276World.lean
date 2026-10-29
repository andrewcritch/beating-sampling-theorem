import BstLean.Part276Prices
import BstLean.Part276Table

/-! One first-layer event and the four original second-layer moments pay for
the sharp stored-table event at dimension 12224. -/
namespace BstLean.Part276
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223
open BstLean.Part252 (product_charge_ae exp_neg12_row)

theorem first_matrix_row_12224 (c : Ret 12224) (hc : A1 c ∈ Eop 12224) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12224 : ℝ)) ≤ 1285 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12224 : ℝ) ≤ 111 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12224 : ℝ) + 2 * √12224 ≤ 12446 := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem bulk_radius_12224 : (63 / 100 : ℝ) ≤ √(qB 12224) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12224 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12224 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12224 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem bulk_positive_12224 : 0 < qB 12224 := by
  have h := bulk_radius_12224
  exact Real.sqrt_pos.mp (by linarith)

theorem node_geometry_12224 {wr : WRet 12224} (hw : windowW wr)
    (θ : AHid 12224) {g : ℕ} (hg : g < Js 12224) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12224 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12224 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12224 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12224 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12224 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12224 := by
    have hr := bulk_radius_12224
    have hr2 := Real.sq_sqrt bulk_positive_12224.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12224)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem sharp_first_charge_price :
    exp (-(12224 : ℝ) / 2) + 2 / 10 ^ 5 + 1 / 10000 ≤ (126145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12224 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12224 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem sharp_total_charge_price :
    (126145 / 10 ^ 9 : ℝ) + 667 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

def sharpVarianceEvent (wr : WRet 12224) : Set (Matrix (Fin (mA 12224)) (Fin 12224) ℝ) :=
  {X | ∀ g : Fin (Js 12224),
    17 / (100 * (12224 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12224 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem sharpVarianceEvent_measurable (wr : WRet 12224) :
    MeasurableSet (sharpVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : sharpVarianceEvent wr = ⋂ g : Fin (Js 12224),
      {X | 17 / (100 * (12224 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12224 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [sharpVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem sharpVarianceEvent_charge {wr : WRet 12224} (hw : windowW wr) :
    (gaussMat (mA 12224) 12224 (2 / (12224 : ℝ))).real (sharpVarianceEvent wr)ᶜ ≤
      2 / 10 ^ 5 := by
  have hs : (sharpVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12224,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12224 : ℝ)) ∨
      42 / (10 * (12224 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge8000 (by norm_num) hw (fun g hg => node_geometry_12224 hw (0, 0) hg))

def sharpFirstEvent (wr : WRet 12224) : Set (Matrix (Fin (mA 12224)) (Fin 12224) ℝ) :=
  (Eop 12224 ∩ sharpVarianceEvent wr) ∩
    paperStatisticsEvent wr (nodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12224))

theorem sharpFirstEvent_measurable (wr : WRet 12224) : MeasurableSet (sharpFirstEvent wr) :=
  ((measurableSet_Eop _).inter (sharpVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (nodeMeasure wr) Fin.val _)

theorem sharpFirstEvent_charge {wr : WRet 12224} (hw : windowW wr) :
    (gaussMat (mA 12224) 12224 (2 / (12224 : ℝ))).real (sharpFirstEvent wr)ᶜ ≤
      (126145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12224)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := node_geometry_12224 hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (nodeMeasure wr) (nodeMeasure_mass wr).le Fin.val hs
  unfold sharpFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (sharpVarianceEvent_charge hw))) hstat)).trans sharp_first_charge_price

def sharpBadPair (wr : WRet 12224) : Set (AHid 12224) := {θ | mkR wr θ ∉ sharpTable}

theorem sharpBadPair_measurable (wr : WRet 12224) : MeasurableSet (sharpBadPair wr) :=
  sharpTable_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem sharp_conditional_charge {wr : WRet 12224} (hwt : tightW wr) :
    ∀ᵐ X ∂gaussMat (mA 12224) 12224 (2 / (12224 : ℝ)), X ∈ sharpFirstEvent wr →
      (gaussMat (mA 12224) (mA 12224) (tA 12224))
        {M | (X, M) ∈ sharpBadPair wr} ≤ ENNReal.ofReal (667 / 10 ^ 6 : ℝ) := by
  have hw : windowW wr := hwt.1
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12224)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := node_geometry_12224 hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12224)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (node_geometry_12224 hw (0, 0) g.isLt).2.2⟩
  have h12 := nodeMeasure_moment12 hwt
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12224)) := (hvar g).1
  have hmax (g : Fin (Js 12224)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12224) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12224)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12224) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourA i := by fin_cases i <;> norm_num [fourA]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (nodeMeasure wr)
    (nodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 160) (by norm_num : (0 : ℝ) < 17 / (100 * 12224))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12224)) statistics_constant_pos_12224.le
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 5435 / 10000)
    (first_matrix_row_12224 (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace sharp_envelope_gap h12 hk fourA hA
  have hreal : (gaussMat (mA 12224) (mA 12224) (tA 12224)).real
      {M | (X, M) ∈ sharpBadPair wr} ≤ (667 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (sharpTable_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans sharp_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem sharp_world_charge (wr : WRet 12224) :
    (nuA 12224).real (sharpBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : tightW wr
  · exact (product_charge_ae _ _ (sharpFirstEvent_measurable wr) (sharpBadPair_measurable wr)
      (by norm_num) (by norm_num) (sharpFirstEvent_charge hw.1)
      (sharp_conditional_charge hw)).trans sharp_total_charge_price
  · have he : sharpBadPair wr = ∅ := by
      ext θ
      simp only [sharpBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num


def sharpPairEvent : Set (WRet 12224 × AHid 12224) :=
  {p | mkR p.1 p.2 ∈ sharpTable}

theorem sharpPairEvent_measurable : MeasurableSet sharpPairEvent :=
  sharpTable_measurable.preimage measurable_mkR

/-- The retained-distribution payment of the sharp table event. -/
theorem sharpTable_ret_charge :
    (retDist (paperCentres 12224)).real sharpTableᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12224) sharpPairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) sharp_world_charge
  convert h using 1
  congr 1

end BstLean.Part276
