import BstLean.Part266Shard6Step5


/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12500
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12500 : ℝ) *
      √(tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12500 : ℝ) ^ 24 = (12500 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) ^ 24 =
      (tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12500 ≤ (2 * 12500 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) * √((42 / 10 : ℝ) / 12500) *
      energyCoefficient18 12500) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) ^ 18 =
      (tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12500) ^ 18 = ((42 / 10 : ℝ) / 12500) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12500) ^ 9 *
        (2 * 12500 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12500

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12500
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12500 (61 / 100) 161 (17 / (100 * 12500)) (26 / (10 * 12500))
    (statisticsConstant (paperBound256 12500)) √((42 / 10 : ℝ) / 12500) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12500) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12500 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12500 * ((161 : ℝ) ^ 2 / (12500 - 2))) *
      √((42 / 10 : ℝ) / 12500) * energyCoefficient18 12500) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12500 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12500 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12500 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12500

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12500
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12500) : Set (Matrix (Fin (mA 12500)) (Fin 12500) ℝ) :=
  {X | ∀ g : Fin (Js 12500),
    17 / (100 * (12500 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12500 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12500) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12500),
      {X | 17 / (100 * (12500 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12500 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12500} (hw : windowW wr) :
    (gaussMat (mA 12500) 12500 (2 / (12500 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12500,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12500 : ℝ)) ∨
      42 / (10 * (12500 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12500) : Set (Matrix (Fin (mA 12500)) (Fin 12500) ℝ) :=
  (Eop 12500 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12500))

theorem tableFirstEvent_measurable (wr : WRet 12500) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12500} (hw : windowW wr) :
    (gaussMat (mA 12500) 12500 (2 / (12500 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12500)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12500) : Set (AHid 12500) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12500) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12500} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12500) 12500 (2 / (12500 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12500) (mA 12500) (tA 12500))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12500)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12500)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12500)) := (hvar g).1
  have hmax (g : Fin (Js 12500)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12500) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12500)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12500) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12500))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12500)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12500) (mA 12500) (tA 12500)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12500) :
    (nuA 12500).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12500

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12500
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12500 × AHid 12500) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12500)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12500) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12500)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12500)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12500)) :
    (retDist (paperCentres 12500)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12500

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12500 :
    BstLean.Part262.ActualRootCertificate 12500 BstLean.Part266.agent12500.root where
  dimension := by norm_num
  table_payment := Row12500.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12500.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12500.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12501
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12501 : ℝ) *
      √(tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12501 : ℝ) ^ 24 = (12501 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) ^ 24 =
      (tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12501 ≤ (2 * 12501 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) * √((42 / 10 : ℝ) / 12501) *
      energyCoefficient18 12501) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) ^ 18 =
      (tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12501) ^ 18 = ((42 / 10 : ℝ) / 12501) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12501) ^ 9 *
        (2 * 12501 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12501

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12501
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12501 (61 / 100) 161 (17 / (100 * 12501)) (26 / (10 * 12501))
    (statisticsConstant (paperBound256 12501)) √((42 / 10 : ℝ) / 12501) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12501) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12501 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12501 * ((161 : ℝ) ^ 2 / (12501 - 2))) *
      √((42 / 10 : ℝ) / 12501) * energyCoefficient18 12501) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12501 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12501 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12501 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12501

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12501
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12501) : Set (Matrix (Fin (mA 12501)) (Fin 12501) ℝ) :=
  {X | ∀ g : Fin (Js 12501),
    17 / (100 * (12501 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12501 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12501) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12501),
      {X | 17 / (100 * (12501 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12501 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12501} (hw : windowW wr) :
    (gaussMat (mA 12501) 12501 (2 / (12501 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12501,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12501 : ℝ)) ∨
      42 / (10 * (12501 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12501) : Set (Matrix (Fin (mA 12501)) (Fin 12501) ℝ) :=
  (Eop 12501 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12501))

theorem tableFirstEvent_measurable (wr : WRet 12501) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12501} (hw : windowW wr) :
    (gaussMat (mA 12501) 12501 (2 / (12501 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12501)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12501) : Set (AHid 12501) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12501) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12501} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12501) 12501 (2 / (12501 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12501) (mA 12501) (tA 12501))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12501)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12501)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12501)) := (hvar g).1
  have hmax (g : Fin (Js 12501)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12501) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12501)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12501) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12501))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12501)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12501) (mA 12501) (tA 12501)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12501) :
    (nuA 12501).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12501

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12501
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12501 × AHid 12501) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12501)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12501) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12501)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12501)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12501)) :
    (retDist (paperCentres 12501)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12501

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12501 :
    BstLean.Part262.ActualRootCertificate 12501 BstLean.Part266.agent12501.root where
  dimension := by norm_num
  table_payment := Row12501.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12501.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12501.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12502
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12502 : ℝ) *
      √(tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12502 : ℝ) ^ 24 = (12502 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) ^ 24 =
      (tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12502 ≤ (2 * 12502 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) * √((42 / 10 : ℝ) / 12502) *
      energyCoefficient18 12502) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) ^ 18 =
      (tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12502) ^ 18 = ((42 / 10 : ℝ) / 12502) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12502) ^ 9 *
        (2 * 12502 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12502

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12502
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12502 (61 / 100) 161 (17 / (100 * 12502)) (26 / (10 * 12502))
    (statisticsConstant (paperBound256 12502)) √((42 / 10 : ℝ) / 12502) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12502) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12502 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12502 * ((161 : ℝ) ^ 2 / (12502 - 2))) *
      √((42 / 10 : ℝ) / 12502) * energyCoefficient18 12502) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12502 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12502 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12502 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12502

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12502
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12502) : Set (Matrix (Fin (mA 12502)) (Fin 12502) ℝ) :=
  {X | ∀ g : Fin (Js 12502),
    17 / (100 * (12502 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12502 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12502) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12502),
      {X | 17 / (100 * (12502 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12502 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12502} (hw : windowW wr) :
    (gaussMat (mA 12502) 12502 (2 / (12502 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12502,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12502 : ℝ)) ∨
      42 / (10 * (12502 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12502) : Set (Matrix (Fin (mA 12502)) (Fin 12502) ℝ) :=
  (Eop 12502 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12502))

theorem tableFirstEvent_measurable (wr : WRet 12502) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12502} (hw : windowW wr) :
    (gaussMat (mA 12502) 12502 (2 / (12502 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12502)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12502) : Set (AHid 12502) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12502) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12502} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12502) 12502 (2 / (12502 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12502) (mA 12502) (tA 12502))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12502)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12502)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12502)) := (hvar g).1
  have hmax (g : Fin (Js 12502)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12502) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12502)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12502) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12502))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12502)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12502) (mA 12502) (tA 12502)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12502) :
    (nuA 12502).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12502

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12502
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12502 × AHid 12502) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12502)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12502) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12502)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12502)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12502)) :
    (retDist (paperCentres 12502)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12502

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12502 :
    BstLean.Part262.ActualRootCertificate 12502 BstLean.Part266.agent12502.root where
  dimension := by norm_num
  table_payment := Row12502.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12502.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12502.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12503
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12503 : ℝ) *
      √(tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12503 : ℝ) ^ 24 = (12503 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) ^ 24 =
      (tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12503 ≤ (2 * 12503 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) * √((42 / 10 : ℝ) / 12503) *
      energyCoefficient18 12503) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) ^ 18 =
      (tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12503) ^ 18 = ((42 / 10 : ℝ) / 12503) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12503) ^ 9 *
        (2 * 12503 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12503

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12503
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12503 (61 / 100) 161 (17 / (100 * 12503)) (26 / (10 * 12503))
    (statisticsConstant (paperBound256 12503)) √((42 / 10 : ℝ) / 12503) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12503) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12503 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12503 * ((161 : ℝ) ^ 2 / (12503 - 2))) *
      √((42 / 10 : ℝ) / 12503) * energyCoefficient18 12503) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12503 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12503 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12503 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12503

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12503
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12503) : Set (Matrix (Fin (mA 12503)) (Fin 12503) ℝ) :=
  {X | ∀ g : Fin (Js 12503),
    17 / (100 * (12503 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12503 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12503) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12503),
      {X | 17 / (100 * (12503 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12503 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12503} (hw : windowW wr) :
    (gaussMat (mA 12503) 12503 (2 / (12503 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12503,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12503 : ℝ)) ∨
      42 / (10 * (12503 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12503) : Set (Matrix (Fin (mA 12503)) (Fin 12503) ℝ) :=
  (Eop 12503 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12503))

theorem tableFirstEvent_measurable (wr : WRet 12503) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12503} (hw : windowW wr) :
    (gaussMat (mA 12503) 12503 (2 / (12503 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12503)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12503) : Set (AHid 12503) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12503) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12503} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12503) 12503 (2 / (12503 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12503) (mA 12503) (tA 12503))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12503)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12503)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12503)) := (hvar g).1
  have hmax (g : Fin (Js 12503)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12503) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12503)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12503) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12503))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12503)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12503) (mA 12503) (tA 12503)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12503) :
    (nuA 12503).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12503

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12503
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12503 × AHid 12503) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12503)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12503) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12503)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12503)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12503)) :
    (retDist (paperCentres 12503)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12503

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12503 :
    BstLean.Part262.ActualRootCertificate 12503 BstLean.Part266.agent12503.root where
  dimension := by norm_num
  table_payment := Row12503.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12503.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12503.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12504
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12504 : ℝ) *
      √(tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12504 : ℝ) ^ 24 = (12504 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) ^ 24 =
      (tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12504 ≤ (2 * 12504 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) * √((42 / 10 : ℝ) / 12504) *
      energyCoefficient18 12504) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) ^ 18 =
      (tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12504) ^ 18 = ((42 / 10 : ℝ) / 12504) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12504) ^ 9 *
        (2 * 12504 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12504

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12504
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12504 (61 / 100) 161 (17 / (100 * 12504)) (26 / (10 * 12504))
    (statisticsConstant (paperBound256 12504)) √((42 / 10 : ℝ) / 12504) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12504) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12504 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12504 * ((161 : ℝ) ^ 2 / (12504 - 2))) *
      √((42 / 10 : ℝ) / 12504) * energyCoefficient18 12504) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12504 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12504 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12504 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12504

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12504
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12504) : Set (Matrix (Fin (mA 12504)) (Fin 12504) ℝ) :=
  {X | ∀ g : Fin (Js 12504),
    17 / (100 * (12504 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12504 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12504) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12504),
      {X | 17 / (100 * (12504 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12504 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12504} (hw : windowW wr) :
    (gaussMat (mA 12504) 12504 (2 / (12504 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12504,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12504 : ℝ)) ∨
      42 / (10 * (12504 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12504) : Set (Matrix (Fin (mA 12504)) (Fin 12504) ℝ) :=
  (Eop 12504 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12504))

theorem tableFirstEvent_measurable (wr : WRet 12504) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12504} (hw : windowW wr) :
    (gaussMat (mA 12504) 12504 (2 / (12504 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12504)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12504) : Set (AHid 12504) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12504) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12504} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12504) 12504 (2 / (12504 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12504) (mA 12504) (tA 12504))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12504)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12504)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12504)) := (hvar g).1
  have hmax (g : Fin (Js 12504)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12504) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12504)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12504) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12504))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12504)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12504) (mA 12504) (tA 12504)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12504) :
    (nuA 12504).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12504

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12504
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12504 × AHid 12504) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12504)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12504) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12504)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12504)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12504)) :
    (retDist (paperCentres 12504)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12504

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12504 :
    BstLean.Part262.ActualRootCertificate 12504 BstLean.Part266.agent12504.root where
  dimension := by norm_num
  table_payment := Row12504.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12504.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12504.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12505
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12505 : ℝ) *
      √(tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12505 : ℝ) ^ 24 = (12505 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) ^ 24 =
      (tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12505 ≤ (2 * 12505 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) * √((42 / 10 : ℝ) / 12505) *
      energyCoefficient18 12505) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) ^ 18 =
      (tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12505) ^ 18 = ((42 / 10 : ℝ) / 12505) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12505) ^ 9 *
        (2 * 12505 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12505

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12505
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12505 (61 / 100) 161 (17 / (100 * 12505)) (26 / (10 * 12505))
    (statisticsConstant (paperBound256 12505)) √((42 / 10 : ℝ) / 12505) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12505) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12505 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12505 * ((161 : ℝ) ^ 2 / (12505 - 2))) *
      √((42 / 10 : ℝ) / 12505) * energyCoefficient18 12505) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12505 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12505 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12505 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12505

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12505
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12505) : Set (Matrix (Fin (mA 12505)) (Fin 12505) ℝ) :=
  {X | ∀ g : Fin (Js 12505),
    17 / (100 * (12505 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12505 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12505) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12505),
      {X | 17 / (100 * (12505 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12505 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12505} (hw : windowW wr) :
    (gaussMat (mA 12505) 12505 (2 / (12505 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12505,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12505 : ℝ)) ∨
      42 / (10 * (12505 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12505) : Set (Matrix (Fin (mA 12505)) (Fin 12505) ℝ) :=
  (Eop 12505 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12505))

theorem tableFirstEvent_measurable (wr : WRet 12505) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12505} (hw : windowW wr) :
    (gaussMat (mA 12505) 12505 (2 / (12505 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12505)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12505) : Set (AHid 12505) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12505) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12505} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12505) 12505 (2 / (12505 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12505) (mA 12505) (tA 12505))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12505)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12505)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12505)) := (hvar g).1
  have hmax (g : Fin (Js 12505)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12505) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12505)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12505) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12505))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12505)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12505) (mA 12505) (tA 12505)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12505) :
    (nuA 12505).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12505

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12505
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12505 × AHid 12505) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12505)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12505) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12505)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12505)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12505)) :
    (retDist (paperCentres 12505)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12505

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12505 :
    BstLean.Part262.ActualRootCertificate 12505 BstLean.Part266.agent12505.root where
  dimension := by norm_num
  table_payment := Row12505.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12505.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12505.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12506
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12506 : ℝ) *
      √(tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12506 : ℝ) ^ 24 = (12506 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) ^ 24 =
      (tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12506 ≤ (2 * 12506 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) * √((42 / 10 : ℝ) / 12506) *
      energyCoefficient18 12506) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) ^ 18 =
      (tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12506) ^ 18 = ((42 / 10 : ℝ) / 12506) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12506) ^ 9 *
        (2 * 12506 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12506

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12506
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12506 (61 / 100) 161 (17 / (100 * 12506)) (26 / (10 * 12506))
    (statisticsConstant (paperBound256 12506)) √((42 / 10 : ℝ) / 12506) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12506) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12506 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12506 * ((161 : ℝ) ^ 2 / (12506 - 2))) *
      √((42 / 10 : ℝ) / 12506) * energyCoefficient18 12506) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12506 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12506 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12506 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12506

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12506
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12506) : Set (Matrix (Fin (mA 12506)) (Fin 12506) ℝ) :=
  {X | ∀ g : Fin (Js 12506),
    17 / (100 * (12506 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12506 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12506) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12506),
      {X | 17 / (100 * (12506 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12506 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12506} (hw : windowW wr) :
    (gaussMat (mA 12506) 12506 (2 / (12506 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12506,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12506 : ℝ)) ∨
      42 / (10 * (12506 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12506) : Set (Matrix (Fin (mA 12506)) (Fin 12506) ℝ) :=
  (Eop 12506 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12506))

theorem tableFirstEvent_measurable (wr : WRet 12506) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12506} (hw : windowW wr) :
    (gaussMat (mA 12506) 12506 (2 / (12506 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12506)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12506) : Set (AHid 12506) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12506) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12506} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12506) 12506 (2 / (12506 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12506) (mA 12506) (tA 12506))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12506)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12506)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12506)) := (hvar g).1
  have hmax (g : Fin (Js 12506)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12506) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12506)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12506) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12506))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12506)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12506) (mA 12506) (tA 12506)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12506) :
    (nuA 12506).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12506

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12506
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12506 × AHid 12506) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12506)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12506) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12506)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12506)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12506)) :
    (retDist (paperCentres 12506)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12506

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12506 :
    BstLean.Part262.ActualRootCertificate 12506 BstLean.Part266.agent12506.root where
  dimension := by norm_num
  table_payment := Row12506.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12506.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12506.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12507
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12507 : ℝ) *
      √(tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12507 : ℝ) ^ 24 = (12507 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) ^ 24 =
      (tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12507 ≤ (2 * 12507 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) * √((42 / 10 : ℝ) / 12507) *
      energyCoefficient18 12507) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) ^ 18 =
      (tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12507) ^ 18 = ((42 / 10 : ℝ) / 12507) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12507) ^ 9 *
        (2 * 12507 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12507

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12507
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12507 (61 / 100) 161 (17 / (100 * 12507)) (26 / (10 * 12507))
    (statisticsConstant (paperBound256 12507)) √((42 / 10 : ℝ) / 12507) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12507) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12507 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12507 * ((161 : ℝ) ^ 2 / (12507 - 2))) *
      √((42 / 10 : ℝ) / 12507) * energyCoefficient18 12507) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12507 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12507 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12507 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12507

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12507
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12507) : Set (Matrix (Fin (mA 12507)) (Fin 12507) ℝ) :=
  {X | ∀ g : Fin (Js 12507),
    17 / (100 * (12507 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12507 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12507) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12507),
      {X | 17 / (100 * (12507 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12507 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12507} (hw : windowW wr) :
    (gaussMat (mA 12507) 12507 (2 / (12507 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12507,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12507 : ℝ)) ∨
      42 / (10 * (12507 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12507) : Set (Matrix (Fin (mA 12507)) (Fin 12507) ℝ) :=
  (Eop 12507 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12507))

theorem tableFirstEvent_measurable (wr : WRet 12507) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12507} (hw : windowW wr) :
    (gaussMat (mA 12507) 12507 (2 / (12507 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12507)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12507) : Set (AHid 12507) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12507) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12507} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12507) 12507 (2 / (12507 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12507) (mA 12507) (tA 12507))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12507)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12507)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12507)) := (hvar g).1
  have hmax (g : Fin (Js 12507)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12507) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12507)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12507) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12507))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12507)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12507) (mA 12507) (tA 12507)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12507) :
    (nuA 12507).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12507

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12507
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12507 × AHid 12507) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12507)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12507) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12507)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12507)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12507)) :
    (retDist (paperCentres 12507)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12507

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12507 :
    BstLean.Part262.ActualRootCertificate 12507 BstLean.Part266.agent12507.root where
  dimension := by norm_num
  table_payment := Row12507.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12507.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12507.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12508
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12508 : ℝ) *
      √(tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12508 : ℝ) ^ 24 = (12508 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) ^ 24 =
      (tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12508 ≤ (2 * 12508 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) * √((42 / 10 : ℝ) / 12508) *
      energyCoefficient18 12508) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) ^ 18 =
      (tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12508) ^ 18 = ((42 / 10 : ℝ) / 12508) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12508) ^ 9 *
        (2 * 12508 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12508

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12508
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12508 (61 / 100) 161 (17 / (100 * 12508)) (26 / (10 * 12508))
    (statisticsConstant (paperBound256 12508)) √((42 / 10 : ℝ) / 12508) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12508) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12508 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12508 * ((161 : ℝ) ^ 2 / (12508 - 2))) *
      √((42 / 10 : ℝ) / 12508) * energyCoefficient18 12508) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12508 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12508 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12508 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12508

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12508
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12508) : Set (Matrix (Fin (mA 12508)) (Fin 12508) ℝ) :=
  {X | ∀ g : Fin (Js 12508),
    17 / (100 * (12508 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12508 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12508) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12508),
      {X | 17 / (100 * (12508 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12508 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12508} (hw : windowW wr) :
    (gaussMat (mA 12508) 12508 (2 / (12508 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12508,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12508 : ℝ)) ∨
      42 / (10 * (12508 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12508) : Set (Matrix (Fin (mA 12508)) (Fin 12508) ℝ) :=
  (Eop 12508 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12508))

theorem tableFirstEvent_measurable (wr : WRet 12508) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12508} (hw : windowW wr) :
    (gaussMat (mA 12508) 12508 (2 / (12508 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12508)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12508) : Set (AHid 12508) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12508) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12508} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12508) 12508 (2 / (12508 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12508) (mA 12508) (tA 12508))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12508)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12508)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12508)) := (hvar g).1
  have hmax (g : Fin (Js 12508)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12508) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12508)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12508) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12508))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12508)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12508) (mA 12508) (tA 12508)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12508) :
    (nuA 12508).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12508

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12508
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12508 × AHid 12508) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12508)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12508) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12508)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12508)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12508)) :
    (retDist (paperCentres 12508)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12508

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12508 :
    BstLean.Part262.ActualRootCertificate 12508 BstLean.Part266.agent12508.root where
  dimension := by norm_num
  table_payment := Row12508.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12508.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12508.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12509
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12509 : ℝ) *
      √(tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12509 : ℝ) ^ 24 = (12509 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) ^ 24 =
      (tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12509 ≤ (2 * 12509 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) * √((42 / 10 : ℝ) / 12509) *
      energyCoefficient18 12509) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) ^ 18 =
      (tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12509) ^ 18 = ((42 / 10 : ℝ) / 12509) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12509) ^ 9 *
        (2 * 12509 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12509

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12509
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12509 (61 / 100) 161 (17 / (100 * 12509)) (26 / (10 * 12509))
    (statisticsConstant (paperBound256 12509)) √((42 / 10 : ℝ) / 12509) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12509) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12509 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12509 * ((161 : ℝ) ^ 2 / (12509 - 2))) *
      √((42 / 10 : ℝ) / 12509) * energyCoefficient18 12509) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12509 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12509 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12509 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12509

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12509
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12509) : Set (Matrix (Fin (mA 12509)) (Fin 12509) ℝ) :=
  {X | ∀ g : Fin (Js 12509),
    17 / (100 * (12509 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12509 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12509) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12509),
      {X | 17 / (100 * (12509 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12509 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12509} (hw : windowW wr) :
    (gaussMat (mA 12509) 12509 (2 / (12509 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12509,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12509 : ℝ)) ∨
      42 / (10 * (12509 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12509) : Set (Matrix (Fin (mA 12509)) (Fin 12509) ℝ) :=
  (Eop 12509 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12509))

theorem tableFirstEvent_measurable (wr : WRet 12509) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12509} (hw : windowW wr) :
    (gaussMat (mA 12509) 12509 (2 / (12509 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12509)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12509) : Set (AHid 12509) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12509) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12509} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12509) 12509 (2 / (12509 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12509) (mA 12509) (tA 12509))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12509)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12509)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12509)) := (hvar g).1
  have hmax (g : Fin (Js 12509)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12509) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12509)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12509) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12509))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12509)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12509) (mA 12509) (tA 12509)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12509) :
    (nuA 12509).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12509

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12509
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12509 × AHid 12509) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12509)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12509) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12509)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12509)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12509)) :
    (retDist (paperCentres 12509)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12509

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12509 :
    BstLean.Part262.ActualRootCertificate 12509 BstLean.Part266.agent12509.root where
  dimension := by norm_num
  table_payment := Row12509.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12509.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12509.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12510
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12510 : ℝ) *
      √(tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12510 : ℝ) ^ 24 = (12510 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) ^ 24 =
      (tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12510 ≤ (2 * 12510 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) * √((42 / 10 : ℝ) / 12510) *
      energyCoefficient18 12510) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) ^ 18 =
      (tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12510) ^ 18 = ((42 / 10 : ℝ) / 12510) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12510) ^ 9 *
        (2 * 12510 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12510

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12510
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12510 (61 / 100) 162 (17 / (100 * 12510)) (26 / (10 * 12510))
    (statisticsConstant (paperBound256 12510)) √((42 / 10 : ℝ) / 12510) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12510) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12510 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12510 * ((162 : ℝ) ^ 2 / (12510 - 2))) *
      √((42 / 10 : ℝ) / 12510) * energyCoefficient18 12510) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12510 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12510 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12510 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12510

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12510
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12510) : Set (Matrix (Fin (mA 12510)) (Fin 12510) ℝ) :=
  {X | ∀ g : Fin (Js 12510),
    17 / (100 * (12510 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12510 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12510) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12510),
      {X | 17 / (100 * (12510 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12510 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12510} (hw : windowW wr) :
    (gaussMat (mA 12510) 12510 (2 / (12510 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12510,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12510 : ℝ)) ∨
      42 / (10 * (12510 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12510) : Set (Matrix (Fin (mA 12510)) (Fin 12510) ℝ) :=
  (Eop 12510 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12510))

theorem tableFirstEvent_measurable (wr : WRet 12510) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12510} (hw : windowW wr) :
    (gaussMat (mA 12510) 12510 (2 / (12510 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12510)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12510) : Set (AHid 12510) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12510) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12510} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12510) 12510 (2 / (12510 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12510) (mA 12510) (tA 12510))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12510)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12510)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12510)) := (hvar g).1
  have hmax (g : Fin (Js 12510)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12510) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12510)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12510) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12510))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12510)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12510) (mA 12510) (tA 12510)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12510) :
    (nuA 12510).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12510

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12510
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12510 × AHid 12510) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12510)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12510) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12510)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12510)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12510)) :
    (retDist (paperCentres 12510)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12510

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12510 :
    BstLean.Part262.ActualRootCertificate 12510 BstLean.Part266.agent12510.root where
  dimension := by norm_num
  table_payment := Row12510.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12510.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12510.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12511
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12511 : ℝ) *
      √(tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12511 : ℝ) ^ 24 = (12511 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) ^ 24 =
      (tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12511 ≤ (2 * 12511 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) * √((42 / 10 : ℝ) / 12511) *
      energyCoefficient18 12511) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) ^ 18 =
      (tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12511) ^ 18 = ((42 / 10 : ℝ) / 12511) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12511) ^ 9 *
        (2 * 12511 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12511

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12511
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12511 (61 / 100) 162 (17 / (100 * 12511)) (26 / (10 * 12511))
    (statisticsConstant (paperBound256 12511)) √((42 / 10 : ℝ) / 12511) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12511) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12511 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12511 * ((162 : ℝ) ^ 2 / (12511 - 2))) *
      √((42 / 10 : ℝ) / 12511) * energyCoefficient18 12511) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12511 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12511 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12511 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12511

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12511
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12511) : Set (Matrix (Fin (mA 12511)) (Fin 12511) ℝ) :=
  {X | ∀ g : Fin (Js 12511),
    17 / (100 * (12511 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12511 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12511) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12511),
      {X | 17 / (100 * (12511 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12511 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12511} (hw : windowW wr) :
    (gaussMat (mA 12511) 12511 (2 / (12511 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12511,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12511 : ℝ)) ∨
      42 / (10 * (12511 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12511) : Set (Matrix (Fin (mA 12511)) (Fin 12511) ℝ) :=
  (Eop 12511 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12511))

theorem tableFirstEvent_measurable (wr : WRet 12511) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12511} (hw : windowW wr) :
    (gaussMat (mA 12511) 12511 (2 / (12511 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12511)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12511) : Set (AHid 12511) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12511) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12511} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12511) 12511 (2 / (12511 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12511) (mA 12511) (tA 12511))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12511)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12511)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12511)) := (hvar g).1
  have hmax (g : Fin (Js 12511)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12511) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12511)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12511) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12511))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12511)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12511) (mA 12511) (tA 12511)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12511) :
    (nuA 12511).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12511

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12511
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12511 × AHid 12511) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12511)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12511) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12511)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12511)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12511)) :
    (retDist (paperCentres 12511)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12511

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12511 :
    BstLean.Part262.ActualRootCertificate 12511 BstLean.Part266.agent12511.root where
  dimension := by norm_num
  table_payment := Row12511.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12511.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12511.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12512
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12512 : ℝ) *
      √(tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12512 : ℝ) ^ 24 = (12512 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) ^ 24 =
      (tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12512 ≤ (2 * 12512 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) * √((42 / 10 : ℝ) / 12512) *
      energyCoefficient18 12512) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) ^ 18 =
      (tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12512) ^ 18 = ((42 / 10 : ℝ) / 12512) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12512) ^ 9 *
        (2 * 12512 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12512

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12512
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12512 (61 / 100) 162 (17 / (100 * 12512)) (26 / (10 * 12512))
    (statisticsConstant (paperBound256 12512)) √((42 / 10 : ℝ) / 12512) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12512) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12512 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12512 * ((162 : ℝ) ^ 2 / (12512 - 2))) *
      √((42 / 10 : ℝ) / 12512) * energyCoefficient18 12512) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12512 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12512 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12512 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12512

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12512
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12512) : Set (Matrix (Fin (mA 12512)) (Fin 12512) ℝ) :=
  {X | ∀ g : Fin (Js 12512),
    17 / (100 * (12512 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12512 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12512) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12512),
      {X | 17 / (100 * (12512 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12512 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12512} (hw : windowW wr) :
    (gaussMat (mA 12512) 12512 (2 / (12512 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12512,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12512 : ℝ)) ∨
      42 / (10 * (12512 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12512) : Set (Matrix (Fin (mA 12512)) (Fin 12512) ℝ) :=
  (Eop 12512 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12512))

theorem tableFirstEvent_measurable (wr : WRet 12512) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12512} (hw : windowW wr) :
    (gaussMat (mA 12512) 12512 (2 / (12512 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12512)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12512) : Set (AHid 12512) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12512) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12512} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12512) 12512 (2 / (12512 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12512) (mA 12512) (tA 12512))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12512)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12512)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12512)) := (hvar g).1
  have hmax (g : Fin (Js 12512)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12512) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12512)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12512) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12512))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12512)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12512) (mA 12512) (tA 12512)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12512) :
    (nuA 12512).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12512

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12512
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12512 × AHid 12512) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12512)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12512) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12512)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12512)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12512)) :
    (retDist (paperCentres 12512)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12512

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12512 :
    BstLean.Part262.ActualRootCertificate 12512 BstLean.Part266.agent12512.root where
  dimension := by norm_num
  table_payment := Row12512.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12512.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12512.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12513
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12513 : ℝ) *
      √(tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12513 : ℝ) ^ 24 = (12513 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) ^ 24 =
      (tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12513 ≤ (2 * 12513 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) * √((42 / 10 : ℝ) / 12513) *
      energyCoefficient18 12513) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) ^ 18 =
      (tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12513) ^ 18 = ((42 / 10 : ℝ) / 12513) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12513) ^ 9 *
        (2 * 12513 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12513

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12513
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12513 (61 / 100) 162 (17 / (100 * 12513)) (26 / (10 * 12513))
    (statisticsConstant (paperBound256 12513)) √((42 / 10 : ℝ) / 12513) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12513) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12513 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12513 * ((162 : ℝ) ^ 2 / (12513 - 2))) *
      √((42 / 10 : ℝ) / 12513) * energyCoefficient18 12513) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12513 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12513 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12513 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12513

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12513
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12513) : Set (Matrix (Fin (mA 12513)) (Fin 12513) ℝ) :=
  {X | ∀ g : Fin (Js 12513),
    17 / (100 * (12513 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12513 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12513) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12513),
      {X | 17 / (100 * (12513 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12513 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12513} (hw : windowW wr) :
    (gaussMat (mA 12513) 12513 (2 / (12513 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12513,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12513 : ℝ)) ∨
      42 / (10 * (12513 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12513) : Set (Matrix (Fin (mA 12513)) (Fin 12513) ℝ) :=
  (Eop 12513 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12513))

theorem tableFirstEvent_measurable (wr : WRet 12513) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12513} (hw : windowW wr) :
    (gaussMat (mA 12513) 12513 (2 / (12513 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12513)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12513) : Set (AHid 12513) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12513) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12513} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12513) 12513 (2 / (12513 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12513) (mA 12513) (tA 12513))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12513)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12513)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12513)) := (hvar g).1
  have hmax (g : Fin (Js 12513)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12513) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12513)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12513) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12513))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12513)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12513) (mA 12513) (tA 12513)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12513) :
    (nuA 12513).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12513

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12513
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12513 × AHid 12513) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12513)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12513) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12513)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12513)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12513)) :
    (retDist (paperCentres 12513)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12513

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12513 :
    BstLean.Part262.ActualRootCertificate 12513 BstLean.Part266.agent12513.root where
  dimension := by norm_num
  table_payment := Row12513.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12513.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12513.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12514
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12514 : ℝ) *
      √(tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12514 : ℝ) ^ 24 = (12514 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) ^ 24 =
      (tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12514 ≤ (2 * 12514 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) * √((42 / 10 : ℝ) / 12514) *
      energyCoefficient18 12514) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) ^ 18 =
      (tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12514) ^ 18 = ((42 / 10 : ℝ) / 12514) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12514) ^ 9 *
        (2 * 12514 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12514

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12514
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12514 (61 / 100) 162 (17 / (100 * 12514)) (26 / (10 * 12514))
    (statisticsConstant (paperBound256 12514)) √((42 / 10 : ℝ) / 12514) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12514) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12514 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12514 * ((162 : ℝ) ^ 2 / (12514 - 2))) *
      √((42 / 10 : ℝ) / 12514) * energyCoefficient18 12514) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12514 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12514 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12514 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12514

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12514
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12514) : Set (Matrix (Fin (mA 12514)) (Fin 12514) ℝ) :=
  {X | ∀ g : Fin (Js 12514),
    17 / (100 * (12514 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12514 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12514) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12514),
      {X | 17 / (100 * (12514 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12514 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12514} (hw : windowW wr) :
    (gaussMat (mA 12514) 12514 (2 / (12514 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12514,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12514 : ℝ)) ∨
      42 / (10 * (12514 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12514) : Set (Matrix (Fin (mA 12514)) (Fin 12514) ℝ) :=
  (Eop 12514 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12514))

theorem tableFirstEvent_measurable (wr : WRet 12514) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12514} (hw : windowW wr) :
    (gaussMat (mA 12514) 12514 (2 / (12514 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12514)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12514) : Set (AHid 12514) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12514) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12514} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12514) 12514 (2 / (12514 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12514) (mA 12514) (tA 12514))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12514)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12514)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12514)) := (hvar g).1
  have hmax (g : Fin (Js 12514)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12514) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12514)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12514) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12514))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12514)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12514) (mA 12514) (tA 12514)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12514) :
    (nuA 12514).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12514

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12514
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12514 × AHid 12514) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12514)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12514) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12514)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12514)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12514)) :
    (retDist (paperCentres 12514)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12514

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12514 :
    BstLean.Part262.ActualRootCertificate 12514 BstLean.Part266.agent12514.root where
  dimension := by norm_num
  table_payment := Row12514.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12514.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12514.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12515
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12515 : ℝ) *
      √(tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12515 : ℝ) ^ 24 = (12515 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) ^ 24 =
      (tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12515 ≤ (2 * 12515 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) * √((42 / 10 : ℝ) / 12515) *
      energyCoefficient18 12515) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) ^ 18 =
      (tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12515) ^ 18 = ((42 / 10 : ℝ) / 12515) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12515) ^ 9 *
        (2 * 12515 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12515

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12515
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12515 (61 / 100) 162 (17 / (100 * 12515)) (26 / (10 * 12515))
    (statisticsConstant (paperBound256 12515)) √((42 / 10 : ℝ) / 12515) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12515) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12515 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12515 * ((162 : ℝ) ^ 2 / (12515 - 2))) *
      √((42 / 10 : ℝ) / 12515) * energyCoefficient18 12515) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12515 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12515 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12515 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12515

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12515
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12515) : Set (Matrix (Fin (mA 12515)) (Fin 12515) ℝ) :=
  {X | ∀ g : Fin (Js 12515),
    17 / (100 * (12515 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12515 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12515) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12515),
      {X | 17 / (100 * (12515 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12515 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12515} (hw : windowW wr) :
    (gaussMat (mA 12515) 12515 (2 / (12515 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12515,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12515 : ℝ)) ∨
      42 / (10 * (12515 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12515) : Set (Matrix (Fin (mA 12515)) (Fin 12515) ℝ) :=
  (Eop 12515 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12515))

theorem tableFirstEvent_measurable (wr : WRet 12515) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12515} (hw : windowW wr) :
    (gaussMat (mA 12515) 12515 (2 / (12515 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12515)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12515) : Set (AHid 12515) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12515) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12515} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12515) 12515 (2 / (12515 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12515) (mA 12515) (tA 12515))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12515)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12515)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12515)) := (hvar g).1
  have hmax (g : Fin (Js 12515)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12515) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12515)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12515) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12515))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12515)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12515) (mA 12515) (tA 12515)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12515) :
    (nuA 12515).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12515

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12515
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12515 × AHid 12515) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12515)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12515) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12515)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12515)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12515)) :
    (retDist (paperCentres 12515)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12515

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12515 :
    BstLean.Part262.ActualRootCertificate 12515 BstLean.Part266.agent12515.root where
  dimension := by norm_num
  table_payment := Row12515.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12515.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12515.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12516
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12516 : ℝ) *
      √(tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12516 : ℝ) ^ 24 = (12516 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) ^ 24 =
      (tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12516 ≤ (2 * 12516 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) * √((42 / 10 : ℝ) / 12516) *
      energyCoefficient18 12516) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) ^ 18 =
      (tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12516) ^ 18 = ((42 / 10 : ℝ) / 12516) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12516) ^ 9 *
        (2 * 12516 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12516

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12516
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12516 (61 / 100) 162 (17 / (100 * 12516)) (26 / (10 * 12516))
    (statisticsConstant (paperBound256 12516)) √((42 / 10 : ℝ) / 12516) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12516) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12516 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12516 * ((162 : ℝ) ^ 2 / (12516 - 2))) *
      √((42 / 10 : ℝ) / 12516) * energyCoefficient18 12516) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12516 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12516 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12516 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12516

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12516
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12516) : Set (Matrix (Fin (mA 12516)) (Fin 12516) ℝ) :=
  {X | ∀ g : Fin (Js 12516),
    17 / (100 * (12516 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12516 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12516) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12516),
      {X | 17 / (100 * (12516 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12516 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12516} (hw : windowW wr) :
    (gaussMat (mA 12516) 12516 (2 / (12516 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12516,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12516 : ℝ)) ∨
      42 / (10 * (12516 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12516) : Set (Matrix (Fin (mA 12516)) (Fin 12516) ℝ) :=
  (Eop 12516 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12516))

theorem tableFirstEvent_measurable (wr : WRet 12516) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12516} (hw : windowW wr) :
    (gaussMat (mA 12516) 12516 (2 / (12516 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12516)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12516) : Set (AHid 12516) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12516) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12516} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12516) 12516 (2 / (12516 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12516) (mA 12516) (tA 12516))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12516)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12516)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12516)) := (hvar g).1
  have hmax (g : Fin (Js 12516)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12516) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12516)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12516) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12516))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12516)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12516) (mA 12516) (tA 12516)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12516) :
    (nuA 12516).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12516

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12516
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12516 × AHid 12516) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12516)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12516) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12516)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12516)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12516)) :
    (retDist (paperCentres 12516)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12516

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12516 :
    BstLean.Part262.ActualRootCertificate 12516 BstLean.Part266.agent12516.root where
  dimension := by norm_num
  table_payment := Row12516.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12516.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12516.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12517
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12517 : ℝ) *
      √(tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12517 : ℝ) ^ 24 = (12517 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) ^ 24 =
      (tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12517 ≤ (2 * 12517 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) * √((42 / 10 : ℝ) / 12517) *
      energyCoefficient18 12517) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) ^ 18 =
      (tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12517) ^ 18 = ((42 / 10 : ℝ) / 12517) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12517) ^ 9 *
        (2 * 12517 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12517

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12517
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12517 (61 / 100) 162 (17 / (100 * 12517)) (26 / (10 * 12517))
    (statisticsConstant (paperBound256 12517)) √((42 / 10 : ℝ) / 12517) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12517) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12517 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12517 * ((162 : ℝ) ^ 2 / (12517 - 2))) *
      √((42 / 10 : ℝ) / 12517) * energyCoefficient18 12517) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12517 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12517 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12517 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12517

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12517
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12517) : Set (Matrix (Fin (mA 12517)) (Fin 12517) ℝ) :=
  {X | ∀ g : Fin (Js 12517),
    17 / (100 * (12517 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12517 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12517) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12517),
      {X | 17 / (100 * (12517 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12517 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12517} (hw : windowW wr) :
    (gaussMat (mA 12517) 12517 (2 / (12517 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12517,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12517 : ℝ)) ∨
      42 / (10 * (12517 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12517) : Set (Matrix (Fin (mA 12517)) (Fin 12517) ℝ) :=
  (Eop 12517 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12517))

theorem tableFirstEvent_measurable (wr : WRet 12517) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12517} (hw : windowW wr) :
    (gaussMat (mA 12517) 12517 (2 / (12517 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12517)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12517) : Set (AHid 12517) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12517) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12517} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12517) 12517 (2 / (12517 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12517) (mA 12517) (tA 12517))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12517)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12517)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12517)) := (hvar g).1
  have hmax (g : Fin (Js 12517)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12517) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12517)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12517) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12517))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12517)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12517) (mA 12517) (tA 12517)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12517) :
    (nuA 12517).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12517

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12517
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12517 × AHid 12517) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12517)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12517) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12517)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12517)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12517)) :
    (retDist (paperCentres 12517)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12517

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12517 :
    BstLean.Part262.ActualRootCertificate 12517 BstLean.Part266.agent12517.root where
  dimension := by norm_num
  table_payment := Row12517.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12517.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12517.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12518
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12518 : ℝ) *
      √(tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12518 : ℝ) ^ 24 = (12518 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) ^ 24 =
      (tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12518 ≤ (2 * 12518 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) * √((42 / 10 : ℝ) / 12518) *
      energyCoefficient18 12518) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) ^ 18 =
      (tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12518) ^ 18 = ((42 / 10 : ℝ) / 12518) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12518) ^ 9 *
        (2 * 12518 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12518

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12518
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12518 (61 / 100) 162 (17 / (100 * 12518)) (26 / (10 * 12518))
    (statisticsConstant (paperBound256 12518)) √((42 / 10 : ℝ) / 12518) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12518) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12518 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12518 * ((162 : ℝ) ^ 2 / (12518 - 2))) *
      √((42 / 10 : ℝ) / 12518) * energyCoefficient18 12518) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12518 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12518 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12518 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12518

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12518
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12518) : Set (Matrix (Fin (mA 12518)) (Fin 12518) ℝ) :=
  {X | ∀ g : Fin (Js 12518),
    17 / (100 * (12518 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12518 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12518) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12518),
      {X | 17 / (100 * (12518 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12518 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12518} (hw : windowW wr) :
    (gaussMat (mA 12518) 12518 (2 / (12518 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12518,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12518 : ℝ)) ∨
      42 / (10 * (12518 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12518) : Set (Matrix (Fin (mA 12518)) (Fin 12518) ℝ) :=
  (Eop 12518 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12518))

theorem tableFirstEvent_measurable (wr : WRet 12518) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12518} (hw : windowW wr) :
    (gaussMat (mA 12518) 12518 (2 / (12518 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12518)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12518) : Set (AHid 12518) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12518) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12518} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12518) 12518 (2 / (12518 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12518) (mA 12518) (tA 12518))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12518)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12518)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12518)) := (hvar g).1
  have hmax (g : Fin (Js 12518)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12518) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12518)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12518) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12518))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12518)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12518) (mA 12518) (tA 12518)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12518) :
    (nuA 12518).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12518

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12518
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12518 × AHid 12518) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12518)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12518) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12518)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12518)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12518)) :
    (retDist (paperCentres 12518)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12518

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12518 :
    BstLean.Part262.ActualRootCertificate 12518 BstLean.Part266.agent12518.root where
  dimension := by norm_num
  table_payment := Row12518.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12518.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12518.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12519
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12519 : ℝ) *
      √(tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12519 : ℝ) ^ 24 = (12519 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) ^ 24 =
      (tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12519 ≤ (2 * 12519 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) * √((42 / 10 : ℝ) / 12519) *
      energyCoefficient18 12519) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) ^ 18 =
      (tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12519) ^ 18 = ((42 / 10 : ℝ) / 12519) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12519) ^ 9 *
        (2 * 12519 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12519

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12519
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12519 (61 / 100) 162 (17 / (100 * 12519)) (26 / (10 * 12519))
    (statisticsConstant (paperBound256 12519)) √((42 / 10 : ℝ) / 12519) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12519) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12519 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12519 * ((162 : ℝ) ^ 2 / (12519 - 2))) *
      √((42 / 10 : ℝ) / 12519) * energyCoefficient18 12519) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12519 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12519 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12519 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12519

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12519
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12519) : Set (Matrix (Fin (mA 12519)) (Fin 12519) ℝ) :=
  {X | ∀ g : Fin (Js 12519),
    17 / (100 * (12519 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12519 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12519) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12519),
      {X | 17 / (100 * (12519 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12519 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12519} (hw : windowW wr) :
    (gaussMat (mA 12519) 12519 (2 / (12519 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12519,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12519 : ℝ)) ∨
      42 / (10 * (12519 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12519) : Set (Matrix (Fin (mA 12519)) (Fin 12519) ℝ) :=
  (Eop 12519 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12519))

theorem tableFirstEvent_measurable (wr : WRet 12519) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12519} (hw : windowW wr) :
    (gaussMat (mA 12519) 12519 (2 / (12519 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12519)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12519) : Set (AHid 12519) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12519) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12519} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12519) 12519 (2 / (12519 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12519) (mA 12519) (tA 12519))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12519)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12519)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12519)) := (hvar g).1
  have hmax (g : Fin (Js 12519)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12519) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12519)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12519) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12519))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12519)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12519) (mA 12519) (tA 12519)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12519) :
    (nuA 12519).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12519

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12519
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12519 × AHid 12519) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12519)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12519) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12519)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12519)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12519)) :
    (retDist (paperCentres 12519)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12519

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12519 :
    BstLean.Part262.ActualRootCertificate 12519 BstLean.Part266.agent12519.root where
  dimension := by norm_num
  table_payment := Row12519.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12519.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12519.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12520
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12520 : ℝ) *
      √(tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12520 : ℝ) ^ 24 = (12520 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) ^ 24 =
      (tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12520 ≤ (2 * 12520 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) * √((42 / 10 : ℝ) / 12520) *
      energyCoefficient18 12520) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) ^ 18 =
      (tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12520) ^ 18 = ((42 / 10 : ℝ) / 12520) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12520) ^ 9 *
        (2 * 12520 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12520

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12520
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12520 (61 / 100) 162 (17 / (100 * 12520)) (26 / (10 * 12520))
    (statisticsConstant (paperBound256 12520)) √((42 / 10 : ℝ) / 12520) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12520) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12520 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12520 * ((162 : ℝ) ^ 2 / (12520 - 2))) *
      √((42 / 10 : ℝ) / 12520) * energyCoefficient18 12520) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12520 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12520 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12520 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12520

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12520
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12520) : Set (Matrix (Fin (mA 12520)) (Fin 12520) ℝ) :=
  {X | ∀ g : Fin (Js 12520),
    17 / (100 * (12520 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12520 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12520) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12520),
      {X | 17 / (100 * (12520 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12520 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12520} (hw : windowW wr) :
    (gaussMat (mA 12520) 12520 (2 / (12520 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12520,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12520 : ℝ)) ∨
      42 / (10 * (12520 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12520) : Set (Matrix (Fin (mA 12520)) (Fin 12520) ℝ) :=
  (Eop 12520 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12520))

theorem tableFirstEvent_measurable (wr : WRet 12520) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12520} (hw : windowW wr) :
    (gaussMat (mA 12520) 12520 (2 / (12520 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12520)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12520) : Set (AHid 12520) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12520) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12520} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12520) 12520 (2 / (12520 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12520) (mA 12520) (tA 12520))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12520)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12520)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12520)) := (hvar g).1
  have hmax (g : Fin (Js 12520)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12520) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12520)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12520) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12520))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12520)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12520) (mA 12520) (tA 12520)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12520) :
    (nuA 12520).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12520

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12520
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12520 × AHid 12520) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12520)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12520) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12520)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12520)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12520)) :
    (retDist (paperCentres 12520)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12520

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12520 :
    BstLean.Part262.ActualRootCertificate 12520 BstLean.Part266.agent12520.root where
  dimension := by norm_num
  table_payment := Row12520.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12520.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12520.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12521
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12521 : ℝ) *
      √(tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12521 : ℝ) ^ 24 = (12521 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) ^ 24 =
      (tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12521 ≤ (2 * 12521 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) * √((42 / 10 : ℝ) / 12521) *
      energyCoefficient18 12521) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) ^ 18 =
      (tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12521) ^ 18 = ((42 / 10 : ℝ) / 12521) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12521) ^ 9 *
        (2 * 12521 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12521

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12521
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12521 (61 / 100) 162 (17 / (100 * 12521)) (26 / (10 * 12521))
    (statisticsConstant (paperBound256 12521)) √((42 / 10 : ℝ) / 12521) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12521) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12521 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12521 * ((162 : ℝ) ^ 2 / (12521 - 2))) *
      √((42 / 10 : ℝ) / 12521) * energyCoefficient18 12521) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12521 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12521 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12521 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12521

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12521
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12521) : Set (Matrix (Fin (mA 12521)) (Fin 12521) ℝ) :=
  {X | ∀ g : Fin (Js 12521),
    17 / (100 * (12521 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12521 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12521) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12521),
      {X | 17 / (100 * (12521 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12521 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12521} (hw : windowW wr) :
    (gaussMat (mA 12521) 12521 (2 / (12521 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12521,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12521 : ℝ)) ∨
      42 / (10 * (12521 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12521) : Set (Matrix (Fin (mA 12521)) (Fin 12521) ℝ) :=
  (Eop 12521 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12521))

theorem tableFirstEvent_measurable (wr : WRet 12521) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12521} (hw : windowW wr) :
    (gaussMat (mA 12521) 12521 (2 / (12521 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12521)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12521) : Set (AHid 12521) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12521) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12521} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12521) 12521 (2 / (12521 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12521) (mA 12521) (tA 12521))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12521)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12521)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12521)) := (hvar g).1
  have hmax (g : Fin (Js 12521)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12521) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12521)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12521) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12521))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12521)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12521) (mA 12521) (tA 12521)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12521) :
    (nuA 12521).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12521

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12521
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12521 × AHid 12521) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12521)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12521) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12521)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12521)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12521)) :
    (retDist (paperCentres 12521)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12521

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12521 :
    BstLean.Part262.ActualRootCertificate 12521 BstLean.Part266.agent12521.root where
  dimension := by norm_num
  table_payment := Row12521.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12521.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12521.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12522
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12522 : ℝ) *
      √(tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12522 : ℝ) ^ 24 = (12522 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) ^ 24 =
      (tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12522 ≤ (2 * 12522 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) * √((42 / 10 : ℝ) / 12522) *
      energyCoefficient18 12522) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) ^ 18 =
      (tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12522) ^ 18 = ((42 / 10 : ℝ) / 12522) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12522) ^ 9 *
        (2 * 12522 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12522

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12522
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12522 (61 / 100) 162 (17 / (100 * 12522)) (26 / (10 * 12522))
    (statisticsConstant (paperBound256 12522)) √((42 / 10 : ℝ) / 12522) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12522) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12522 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12522 * ((162 : ℝ) ^ 2 / (12522 - 2))) *
      √((42 / 10 : ℝ) / 12522) * energyCoefficient18 12522) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12522 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12522 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12522 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12522

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12522
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12522) : Set (Matrix (Fin (mA 12522)) (Fin 12522) ℝ) :=
  {X | ∀ g : Fin (Js 12522),
    17 / (100 * (12522 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12522 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12522) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12522),
      {X | 17 / (100 * (12522 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12522 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12522} (hw : windowW wr) :
    (gaussMat (mA 12522) 12522 (2 / (12522 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12522,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12522 : ℝ)) ∨
      42 / (10 * (12522 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12522) : Set (Matrix (Fin (mA 12522)) (Fin 12522) ℝ) :=
  (Eop 12522 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12522))

theorem tableFirstEvent_measurable (wr : WRet 12522) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12522} (hw : windowW wr) :
    (gaussMat (mA 12522) 12522 (2 / (12522 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12522)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12522) : Set (AHid 12522) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12522) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12522} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12522) 12522 (2 / (12522 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12522) (mA 12522) (tA 12522))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12522)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12522)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12522)) := (hvar g).1
  have hmax (g : Fin (Js 12522)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12522) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12522)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12522) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12522))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12522)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12522) (mA 12522) (tA 12522)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12522) :
    (nuA 12522).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12522

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12522
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12522 × AHid 12522) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12522)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12522) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12522)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12522)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12522)) :
    (retDist (paperCentres 12522)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12522

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12522 :
    BstLean.Part262.ActualRootCertificate 12522 BstLean.Part266.agent12522.root where
  dimension := by norm_num
  table_payment := Row12522.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12522.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12522.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12523
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12523 : ℝ) *
      √(tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12523 : ℝ) ^ 24 = (12523 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) ^ 24 =
      (tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12523 ≤ (2 * 12523 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) * √((42 / 10 : ℝ) / 12523) *
      energyCoefficient18 12523) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) ^ 18 =
      (tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12523) ^ 18 = ((42 / 10 : ℝ) / 12523) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12523) ^ 9 *
        (2 * 12523 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12523

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12523
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12523 (61 / 100) 162 (17 / (100 * 12523)) (26 / (10 * 12523))
    (statisticsConstant (paperBound256 12523)) √((42 / 10 : ℝ) / 12523) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12523) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12523 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12523 * ((162 : ℝ) ^ 2 / (12523 - 2))) *
      √((42 / 10 : ℝ) / 12523) * energyCoefficient18 12523) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12523 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12523 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12523 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12523

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12523
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12523) : Set (Matrix (Fin (mA 12523)) (Fin 12523) ℝ) :=
  {X | ∀ g : Fin (Js 12523),
    17 / (100 * (12523 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12523 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12523) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12523),
      {X | 17 / (100 * (12523 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12523 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12523} (hw : windowW wr) :
    (gaussMat (mA 12523) 12523 (2 / (12523 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12523,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12523 : ℝ)) ∨
      42 / (10 * (12523 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12523) : Set (Matrix (Fin (mA 12523)) (Fin 12523) ℝ) :=
  (Eop 12523 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12523))

theorem tableFirstEvent_measurable (wr : WRet 12523) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12523} (hw : windowW wr) :
    (gaussMat (mA 12523) 12523 (2 / (12523 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12523)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12523) : Set (AHid 12523) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12523) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12523} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12523) 12523 (2 / (12523 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12523) (mA 12523) (tA 12523))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12523)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12523)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12523)) := (hvar g).1
  have hmax (g : Fin (Js 12523)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12523) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12523)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12523) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12523))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12523)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12523) (mA 12523) (tA 12523)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12523) :
    (nuA 12523).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12523

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12523
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12523 × AHid 12523) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12523)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12523) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12523)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12523)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12523)) :
    (retDist (paperCentres 12523)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12523

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12523 :
    BstLean.Part262.ActualRootCertificate 12523 BstLean.Part266.agent12523.root where
  dimension := by norm_num
  table_payment := Row12523.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12523.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12523.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12524
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12524 : ℝ) *
      √(tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12524 : ℝ) ^ 24 = (12524 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) ^ 24 =
      (tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12524 ≤ (2 * 12524 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) * √((42 / 10 : ℝ) / 12524) *
      energyCoefficient18 12524) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) ^ 18 =
      (tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12524) ^ 18 = ((42 / 10 : ℝ) / 12524) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12524) ^ 9 *
        (2 * 12524 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12524

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12524
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12524 (61 / 100) 162 (17 / (100 * 12524)) (26 / (10 * 12524))
    (statisticsConstant (paperBound256 12524)) √((42 / 10 : ℝ) / 12524) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12524) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12524 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 12524 * ((162 : ℝ) ^ 2 / (12524 - 2))) *
      √((42 / 10 : ℝ) / 12524) * energyCoefficient18 12524) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(12524 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12524 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12524 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12524

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12524
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12524) : Set (Matrix (Fin (mA 12524)) (Fin 12524) ℝ) :=
  {X | ∀ g : Fin (Js 12524),
    17 / (100 * (12524 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12524 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12524) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12524),
      {X | 17 / (100 * (12524 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12524 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12524} (hw : windowW wr) :
    (gaussMat (mA 12524) 12524 (2 / (12524 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12524,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12524 : ℝ)) ∨
      42 / (10 * (12524 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12524) : Set (Matrix (Fin (mA 12524)) (Fin 12524) ℝ) :=
  (Eop 12524 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12524))

theorem tableFirstEvent_measurable (wr : WRet 12524) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12524} (hw : windowW wr) :
    (gaussMat (mA 12524) 12524 (2 / (12524 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12524)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12524) : Set (AHid 12524) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12524) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12524} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12524) 12524 (2 / (12524 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12524) (mA 12524) (tA 12524))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12524)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12524)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 12524)) := (hvar g).1
  have hmax (g : Fin (Js 12524)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12524) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12524)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12524) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 162) (by norm_num : (0 : ℝ) < 17 / (100 * 12524))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12524)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12524) (mA 12524) (tA 12524)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12524) :
    (nuA 12524).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row12524

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12524
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12524 × AHid 12524) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12524)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12524) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12524)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12524)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12524)) :
    (retDist (paperCentres 12524)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12524

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12524 :
    BstLean.Part262.ActualRootCertificate 12524 BstLean.Part266.agent12524.root where
  dimension := by norm_num
  table_payment := Row12524.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12524.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12524.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266
