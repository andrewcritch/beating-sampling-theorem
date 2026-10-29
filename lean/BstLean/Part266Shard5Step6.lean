import BstLean.Part266Shard5Step5


/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12475 : ℝ) *
      √(tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12475 : ℝ) ^ 24 = (12475 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) ^ 24 =
      (tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12475 ≤ (2 * 12475 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) * √((42 / 10 : ℝ) / 12475) *
      energyCoefficient18 12475) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) ^ 18 =
      (tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12475) ^ 18 = ((42 / 10 : ℝ) / 12475) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12475) ^ 9 *
        (2 * 12475 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12475

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12475 (61 / 100) 161 (17 / (100 * 12475)) (26 / (10 * 12475))
    (statisticsConstant (paperBound256 12475)) √((42 / 10 : ℝ) / 12475) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12475) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12475 : ℕ))
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
    change (√(tA 12475 * ((161 : ℝ) ^ 2 / (12475 - 2))) *
      √((42 / 10 : ℝ) / 12475) * energyCoefficient18 12475) ^ 18 *
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
    exp (-(12475 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12475 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12475 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12475

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12475) : Set (Matrix (Fin (mA 12475)) (Fin 12475) ℝ) :=
  {X | ∀ g : Fin (Js 12475),
    17 / (100 * (12475 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12475 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12475) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12475),
      {X | 17 / (100 * (12475 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12475 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12475} (hw : windowW wr) :
    (gaussMat (mA 12475) 12475 (2 / (12475 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12475,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12475 : ℝ)) ∨
      42 / (10 * (12475 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12475) : Set (Matrix (Fin (mA 12475)) (Fin 12475) ℝ) :=
  (Eop 12475 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12475))

theorem tableFirstEvent_measurable (wr : WRet 12475) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12475} (hw : windowW wr) :
    (gaussMat (mA 12475) 12475 (2 / (12475 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12475)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12475) : Set (AHid 12475) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12475) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12475} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12475) 12475 (2 / (12475 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12475) (mA 12475) (tA 12475))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12475)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12475)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12475)) := (hvar g).1
  have hmax (g : Fin (Js 12475)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12475) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12475)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12475) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12475))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12475)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12475) (mA 12475) (tA 12475)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12475) :
    (nuA 12475).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12475

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12475 × AHid 12475) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12475)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12475) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12475)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12475)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12475)) :
    (retDist (paperCentres 12475)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12475

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12475 :
    BstLean.Part262.ActualRootCertificate 12475 BstLean.Part266.agent12475.root where
  dimension := by norm_num
  table_payment := Row12475.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12475.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12475.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12476 : ℝ) *
      √(tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12476 : ℝ) ^ 24 = (12476 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) ^ 24 =
      (tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12476 ≤ (2 * 12476 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) * √((42 / 10 : ℝ) / 12476) *
      energyCoefficient18 12476) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) ^ 18 =
      (tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12476) ^ 18 = ((42 / 10 : ℝ) / 12476) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12476) ^ 9 *
        (2 * 12476 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12476

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12476 (61 / 100) 161 (17 / (100 * 12476)) (26 / (10 * 12476))
    (statisticsConstant (paperBound256 12476)) √((42 / 10 : ℝ) / 12476) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12476) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12476 : ℕ))
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
    change (√(tA 12476 * ((161 : ℝ) ^ 2 / (12476 - 2))) *
      √((42 / 10 : ℝ) / 12476) * energyCoefficient18 12476) ^ 18 *
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
    exp (-(12476 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12476 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12476 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12476

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12476) : Set (Matrix (Fin (mA 12476)) (Fin 12476) ℝ) :=
  {X | ∀ g : Fin (Js 12476),
    17 / (100 * (12476 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12476 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12476) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12476),
      {X | 17 / (100 * (12476 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12476 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12476} (hw : windowW wr) :
    (gaussMat (mA 12476) 12476 (2 / (12476 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12476,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12476 : ℝ)) ∨
      42 / (10 * (12476 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12476) : Set (Matrix (Fin (mA 12476)) (Fin 12476) ℝ) :=
  (Eop 12476 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12476))

theorem tableFirstEvent_measurable (wr : WRet 12476) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12476} (hw : windowW wr) :
    (gaussMat (mA 12476) 12476 (2 / (12476 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12476)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12476) : Set (AHid 12476) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12476) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12476} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12476) 12476 (2 / (12476 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12476) (mA 12476) (tA 12476))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12476)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12476)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12476)) := (hvar g).1
  have hmax (g : Fin (Js 12476)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12476) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12476)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12476) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12476))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12476)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12476) (mA 12476) (tA 12476)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12476) :
    (nuA 12476).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12476

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12476 × AHid 12476) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12476)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12476) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12476)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12476)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12476)) :
    (retDist (paperCentres 12476)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12476

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12476 :
    BstLean.Part262.ActualRootCertificate 12476 BstLean.Part266.agent12476.root where
  dimension := by norm_num
  table_payment := Row12476.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12476.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12476.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12477 : ℝ) *
      √(tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12477 : ℝ) ^ 24 = (12477 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) ^ 24 =
      (tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12477 ≤ (2 * 12477 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) * √((42 / 10 : ℝ) / 12477) *
      energyCoefficient18 12477) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) ^ 18 =
      (tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12477) ^ 18 = ((42 / 10 : ℝ) / 12477) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12477) ^ 9 *
        (2 * 12477 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12477

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12477 (61 / 100) 161 (17 / (100 * 12477)) (26 / (10 * 12477))
    (statisticsConstant (paperBound256 12477)) √((42 / 10 : ℝ) / 12477) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12477) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12477 : ℕ))
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
    change (√(tA 12477 * ((161 : ℝ) ^ 2 / (12477 - 2))) *
      √((42 / 10 : ℝ) / 12477) * energyCoefficient18 12477) ^ 18 *
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
    exp (-(12477 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12477 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12477 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12477

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12477) : Set (Matrix (Fin (mA 12477)) (Fin 12477) ℝ) :=
  {X | ∀ g : Fin (Js 12477),
    17 / (100 * (12477 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12477 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12477) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12477),
      {X | 17 / (100 * (12477 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12477 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12477} (hw : windowW wr) :
    (gaussMat (mA 12477) 12477 (2 / (12477 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12477,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12477 : ℝ)) ∨
      42 / (10 * (12477 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12477) : Set (Matrix (Fin (mA 12477)) (Fin 12477) ℝ) :=
  (Eop 12477 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12477))

theorem tableFirstEvent_measurable (wr : WRet 12477) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12477} (hw : windowW wr) :
    (gaussMat (mA 12477) 12477 (2 / (12477 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12477)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12477) : Set (AHid 12477) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12477) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12477} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12477) 12477 (2 / (12477 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12477) (mA 12477) (tA 12477))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12477)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12477)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12477)) := (hvar g).1
  have hmax (g : Fin (Js 12477)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12477) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12477)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12477) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12477))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12477)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12477) (mA 12477) (tA 12477)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12477) :
    (nuA 12477).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12477

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12477 × AHid 12477) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12477)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12477) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12477)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12477)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12477)) :
    (retDist (paperCentres 12477)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12477

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12477 :
    BstLean.Part262.ActualRootCertificate 12477 BstLean.Part266.agent12477.root where
  dimension := by norm_num
  table_payment := Row12477.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12477.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12477.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12478 : ℝ) *
      √(tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12478 : ℝ) ^ 24 = (12478 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) ^ 24 =
      (tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12478 ≤ (2 * 12478 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) * √((42 / 10 : ℝ) / 12478) *
      energyCoefficient18 12478) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) ^ 18 =
      (tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12478) ^ 18 = ((42 / 10 : ℝ) / 12478) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12478) ^ 9 *
        (2 * 12478 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12478

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12478 (61 / 100) 161 (17 / (100 * 12478)) (26 / (10 * 12478))
    (statisticsConstant (paperBound256 12478)) √((42 / 10 : ℝ) / 12478) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12478) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12478 : ℕ))
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
    change (√(tA 12478 * ((161 : ℝ) ^ 2 / (12478 - 2))) *
      √((42 / 10 : ℝ) / 12478) * energyCoefficient18 12478) ^ 18 *
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
    exp (-(12478 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12478 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12478 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12478

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12478) : Set (Matrix (Fin (mA 12478)) (Fin 12478) ℝ) :=
  {X | ∀ g : Fin (Js 12478),
    17 / (100 * (12478 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12478 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12478) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12478),
      {X | 17 / (100 * (12478 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12478 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12478} (hw : windowW wr) :
    (gaussMat (mA 12478) 12478 (2 / (12478 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12478,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12478 : ℝ)) ∨
      42 / (10 * (12478 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12478) : Set (Matrix (Fin (mA 12478)) (Fin 12478) ℝ) :=
  (Eop 12478 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12478))

theorem tableFirstEvent_measurable (wr : WRet 12478) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12478} (hw : windowW wr) :
    (gaussMat (mA 12478) 12478 (2 / (12478 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12478)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12478) : Set (AHid 12478) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12478) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12478} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12478) 12478 (2 / (12478 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12478) (mA 12478) (tA 12478))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12478)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12478)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12478)) := (hvar g).1
  have hmax (g : Fin (Js 12478)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12478) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12478)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12478) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12478))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12478)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12478) (mA 12478) (tA 12478)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12478) :
    (nuA 12478).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12478

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12478 × AHid 12478) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12478)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12478) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12478)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12478)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12478)) :
    (retDist (paperCentres 12478)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12478

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12478 :
    BstLean.Part262.ActualRootCertificate 12478 BstLean.Part266.agent12478.root where
  dimension := by norm_num
  table_payment := Row12478.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12478.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12478.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12479 : ℝ) *
      √(tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12479 : ℝ) ^ 24 = (12479 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) ^ 24 =
      (tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12479 ≤ (2 * 12479 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) * √((42 / 10 : ℝ) / 12479) *
      energyCoefficient18 12479) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) ^ 18 =
      (tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12479) ^ 18 = ((42 / 10 : ℝ) / 12479) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12479) ^ 9 *
        (2 * 12479 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12479

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12479 (61 / 100) 161 (17 / (100 * 12479)) (26 / (10 * 12479))
    (statisticsConstant (paperBound256 12479)) √((42 / 10 : ℝ) / 12479) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12479) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12479 : ℕ))
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
    change (√(tA 12479 * ((161 : ℝ) ^ 2 / (12479 - 2))) *
      √((42 / 10 : ℝ) / 12479) * energyCoefficient18 12479) ^ 18 *
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
    exp (-(12479 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12479 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12479 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12479

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12479) : Set (Matrix (Fin (mA 12479)) (Fin 12479) ℝ) :=
  {X | ∀ g : Fin (Js 12479),
    17 / (100 * (12479 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12479 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12479) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12479),
      {X | 17 / (100 * (12479 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12479 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12479} (hw : windowW wr) :
    (gaussMat (mA 12479) 12479 (2 / (12479 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12479,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12479 : ℝ)) ∨
      42 / (10 * (12479 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12479) : Set (Matrix (Fin (mA 12479)) (Fin 12479) ℝ) :=
  (Eop 12479 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12479))

theorem tableFirstEvent_measurable (wr : WRet 12479) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12479} (hw : windowW wr) :
    (gaussMat (mA 12479) 12479 (2 / (12479 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12479)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12479) : Set (AHid 12479) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12479) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12479} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12479) 12479 (2 / (12479 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12479) (mA 12479) (tA 12479))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12479)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12479)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12479)) := (hvar g).1
  have hmax (g : Fin (Js 12479)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12479) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12479)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12479) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12479))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12479)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12479) (mA 12479) (tA 12479)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12479) :
    (nuA 12479).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12479

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12479 × AHid 12479) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12479)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12479) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12479)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12479)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12479)) :
    (retDist (paperCentres 12479)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12479

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12479 :
    BstLean.Part262.ActualRootCertificate 12479 BstLean.Part266.agent12479.root where
  dimension := by norm_num
  table_payment := Row12479.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12479.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12479.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12480 : ℝ) *
      √(tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12480 : ℝ) ^ 24 = (12480 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) ^ 24 =
      (tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12480 ≤ (2 * 12480 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) * √((42 / 10 : ℝ) / 12480) *
      energyCoefficient18 12480) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) ^ 18 =
      (tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12480) ^ 18 = ((42 / 10 : ℝ) / 12480) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12480) ^ 9 *
        (2 * 12480 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12480

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12480 (61 / 100) 161 (17 / (100 * 12480)) (26 / (10 * 12480))
    (statisticsConstant (paperBound256 12480)) √((42 / 10 : ℝ) / 12480) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12480) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12480 : ℕ))
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
    change (√(tA 12480 * ((161 : ℝ) ^ 2 / (12480 - 2))) *
      √((42 / 10 : ℝ) / 12480) * energyCoefficient18 12480) ^ 18 *
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
    exp (-(12480 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12480 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12480 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12480

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12480) : Set (Matrix (Fin (mA 12480)) (Fin 12480) ℝ) :=
  {X | ∀ g : Fin (Js 12480),
    17 / (100 * (12480 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12480 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12480) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12480),
      {X | 17 / (100 * (12480 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12480 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12480} (hw : windowW wr) :
    (gaussMat (mA 12480) 12480 (2 / (12480 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12480,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12480 : ℝ)) ∨
      42 / (10 * (12480 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12480) : Set (Matrix (Fin (mA 12480)) (Fin 12480) ℝ) :=
  (Eop 12480 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12480))

theorem tableFirstEvent_measurable (wr : WRet 12480) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12480} (hw : windowW wr) :
    (gaussMat (mA 12480) 12480 (2 / (12480 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12480)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12480) : Set (AHid 12480) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12480) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12480} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12480) 12480 (2 / (12480 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12480) (mA 12480) (tA 12480))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12480)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12480)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12480)) := (hvar g).1
  have hmax (g : Fin (Js 12480)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12480) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12480)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12480) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12480))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12480)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12480) (mA 12480) (tA 12480)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12480) :
    (nuA 12480).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12480

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12480 × AHid 12480) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12480)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12480) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12480)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12480)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12480)) :
    (retDist (paperCentres 12480)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12480

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12480 :
    BstLean.Part262.ActualRootCertificate 12480 BstLean.Part266.agent12480.root where
  dimension := by norm_num
  table_payment := Row12480.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12480.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12480.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12481 : ℝ) *
      √(tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12481 : ℝ) ^ 24 = (12481 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) ^ 24 =
      (tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12481 ≤ (2 * 12481 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) * √((42 / 10 : ℝ) / 12481) *
      energyCoefficient18 12481) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) ^ 18 =
      (tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12481) ^ 18 = ((42 / 10 : ℝ) / 12481) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12481) ^ 9 *
        (2 * 12481 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12481

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12481 (61 / 100) 161 (17 / (100 * 12481)) (26 / (10 * 12481))
    (statisticsConstant (paperBound256 12481)) √((42 / 10 : ℝ) / 12481) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12481) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12481 : ℕ))
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
    change (√(tA 12481 * ((161 : ℝ) ^ 2 / (12481 - 2))) *
      √((42 / 10 : ℝ) / 12481) * energyCoefficient18 12481) ^ 18 *
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
    exp (-(12481 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12481 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12481 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12481

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12481) : Set (Matrix (Fin (mA 12481)) (Fin 12481) ℝ) :=
  {X | ∀ g : Fin (Js 12481),
    17 / (100 * (12481 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12481 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12481) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12481),
      {X | 17 / (100 * (12481 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12481 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12481} (hw : windowW wr) :
    (gaussMat (mA 12481) 12481 (2 / (12481 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12481,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12481 : ℝ)) ∨
      42 / (10 * (12481 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12481) : Set (Matrix (Fin (mA 12481)) (Fin 12481) ℝ) :=
  (Eop 12481 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12481))

theorem tableFirstEvent_measurable (wr : WRet 12481) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12481} (hw : windowW wr) :
    (gaussMat (mA 12481) 12481 (2 / (12481 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12481)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12481) : Set (AHid 12481) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12481) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12481} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12481) 12481 (2 / (12481 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12481) (mA 12481) (tA 12481))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12481)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12481)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12481)) := (hvar g).1
  have hmax (g : Fin (Js 12481)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12481) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12481)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12481) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12481))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12481)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12481) (mA 12481) (tA 12481)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12481) :
    (nuA 12481).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12481

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12481 × AHid 12481) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12481)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12481) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12481)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12481)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12481)) :
    (retDist (paperCentres 12481)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12481

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12481 :
    BstLean.Part262.ActualRootCertificate 12481 BstLean.Part266.agent12481.root where
  dimension := by norm_num
  table_payment := Row12481.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12481.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12481.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12482 : ℝ) *
      √(tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12482 : ℝ) ^ 24 = (12482 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) ^ 24 =
      (tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12482 ≤ (2 * 12482 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) * √((42 / 10 : ℝ) / 12482) *
      energyCoefficient18 12482) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) ^ 18 =
      (tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12482) ^ 18 = ((42 / 10 : ℝ) / 12482) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12482) ^ 9 *
        (2 * 12482 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12482

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12482 (61 / 100) 161 (17 / (100 * 12482)) (26 / (10 * 12482))
    (statisticsConstant (paperBound256 12482)) √((42 / 10 : ℝ) / 12482) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12482) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12482 : ℕ))
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
    change (√(tA 12482 * ((161 : ℝ) ^ 2 / (12482 - 2))) *
      √((42 / 10 : ℝ) / 12482) * energyCoefficient18 12482) ^ 18 *
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
    exp (-(12482 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12482 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12482 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12482

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12482) : Set (Matrix (Fin (mA 12482)) (Fin 12482) ℝ) :=
  {X | ∀ g : Fin (Js 12482),
    17 / (100 * (12482 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12482 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12482) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12482),
      {X | 17 / (100 * (12482 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12482 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12482} (hw : windowW wr) :
    (gaussMat (mA 12482) 12482 (2 / (12482 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12482,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12482 : ℝ)) ∨
      42 / (10 * (12482 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12482) : Set (Matrix (Fin (mA 12482)) (Fin 12482) ℝ) :=
  (Eop 12482 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12482))

theorem tableFirstEvent_measurable (wr : WRet 12482) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12482} (hw : windowW wr) :
    (gaussMat (mA 12482) 12482 (2 / (12482 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12482)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12482) : Set (AHid 12482) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12482) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12482} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12482) 12482 (2 / (12482 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12482) (mA 12482) (tA 12482))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12482)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12482)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12482)) := (hvar g).1
  have hmax (g : Fin (Js 12482)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12482) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12482)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12482) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12482))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12482)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12482) (mA 12482) (tA 12482)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12482) :
    (nuA 12482).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12482

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12482 × AHid 12482) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12482)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12482) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12482)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12482)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12482)) :
    (retDist (paperCentres 12482)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12482

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12482 :
    BstLean.Part262.ActualRootCertificate 12482 BstLean.Part266.agent12482.root where
  dimension := by norm_num
  table_payment := Row12482.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12482.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12482.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12483 : ℝ) *
      √(tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12483 : ℝ) ^ 24 = (12483 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) ^ 24 =
      (tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12483 ≤ (2 * 12483 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) * √((42 / 10 : ℝ) / 12483) *
      energyCoefficient18 12483) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) ^ 18 =
      (tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12483) ^ 18 = ((42 / 10 : ℝ) / 12483) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12483) ^ 9 *
        (2 * 12483 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12483

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12483 (61 / 100) 161 (17 / (100 * 12483)) (26 / (10 * 12483))
    (statisticsConstant (paperBound256 12483)) √((42 / 10 : ℝ) / 12483) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12483) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12483 : ℕ))
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
    change (√(tA 12483 * ((161 : ℝ) ^ 2 / (12483 - 2))) *
      √((42 / 10 : ℝ) / 12483) * energyCoefficient18 12483) ^ 18 *
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
    exp (-(12483 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12483 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12483 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12483

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12483) : Set (Matrix (Fin (mA 12483)) (Fin 12483) ℝ) :=
  {X | ∀ g : Fin (Js 12483),
    17 / (100 * (12483 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12483 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12483) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12483),
      {X | 17 / (100 * (12483 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12483 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12483} (hw : windowW wr) :
    (gaussMat (mA 12483) 12483 (2 / (12483 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12483,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12483 : ℝ)) ∨
      42 / (10 * (12483 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12483) : Set (Matrix (Fin (mA 12483)) (Fin 12483) ℝ) :=
  (Eop 12483 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12483))

theorem tableFirstEvent_measurable (wr : WRet 12483) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12483} (hw : windowW wr) :
    (gaussMat (mA 12483) 12483 (2 / (12483 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12483)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12483) : Set (AHid 12483) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12483) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12483} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12483) 12483 (2 / (12483 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12483) (mA 12483) (tA 12483))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12483)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12483)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12483)) := (hvar g).1
  have hmax (g : Fin (Js 12483)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12483) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12483)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12483) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12483))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12483)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12483) (mA 12483) (tA 12483)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12483) :
    (nuA 12483).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12483

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12483 × AHid 12483) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12483)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12483) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12483)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12483)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12483)) :
    (retDist (paperCentres 12483)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12483

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12483 :
    BstLean.Part262.ActualRootCertificate 12483 BstLean.Part266.agent12483.root where
  dimension := by norm_num
  table_payment := Row12483.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12483.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12483.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12484 : ℝ) *
      √(tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12484 : ℝ) ^ 24 = (12484 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) ^ 24 =
      (tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12484 ≤ (2 * 12484 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) * √((42 / 10 : ℝ) / 12484) *
      energyCoefficient18 12484) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) ^ 18 =
      (tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12484) ^ 18 = ((42 / 10 : ℝ) / 12484) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12484) ^ 9 *
        (2 * 12484 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12484

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12484 (61 / 100) 161 (17 / (100 * 12484)) (26 / (10 * 12484))
    (statisticsConstant (paperBound256 12484)) √((42 / 10 : ℝ) / 12484) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12484) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12484 : ℕ))
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
    change (√(tA 12484 * ((161 : ℝ) ^ 2 / (12484 - 2))) *
      √((42 / 10 : ℝ) / 12484) * energyCoefficient18 12484) ^ 18 *
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
    exp (-(12484 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12484 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12484 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12484

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12484) : Set (Matrix (Fin (mA 12484)) (Fin 12484) ℝ) :=
  {X | ∀ g : Fin (Js 12484),
    17 / (100 * (12484 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12484 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12484) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12484),
      {X | 17 / (100 * (12484 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12484 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12484} (hw : windowW wr) :
    (gaussMat (mA 12484) 12484 (2 / (12484 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12484,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12484 : ℝ)) ∨
      42 / (10 * (12484 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12484) : Set (Matrix (Fin (mA 12484)) (Fin 12484) ℝ) :=
  (Eop 12484 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12484))

theorem tableFirstEvent_measurable (wr : WRet 12484) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12484} (hw : windowW wr) :
    (gaussMat (mA 12484) 12484 (2 / (12484 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12484)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12484) : Set (AHid 12484) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12484) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12484} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12484) 12484 (2 / (12484 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12484) (mA 12484) (tA 12484))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12484)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12484)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12484)) := (hvar g).1
  have hmax (g : Fin (Js 12484)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12484) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12484)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12484) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12484))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12484)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12484) (mA 12484) (tA 12484)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12484) :
    (nuA 12484).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12484

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12484 × AHid 12484) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12484)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12484) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12484)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12484)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12484)) :
    (retDist (paperCentres 12484)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12484

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12484 :
    BstLean.Part262.ActualRootCertificate 12484 BstLean.Part266.agent12484.root where
  dimension := by norm_num
  table_payment := Row12484.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12484.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12484.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12485 : ℝ) *
      √(tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12485 : ℝ) ^ 24 = (12485 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) ^ 24 =
      (tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12485 ≤ (2 * 12485 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) * √((42 / 10 : ℝ) / 12485) *
      energyCoefficient18 12485) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) ^ 18 =
      (tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12485) ^ 18 = ((42 / 10 : ℝ) / 12485) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12485) ^ 9 *
        (2 * 12485 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12485

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12485 (61 / 100) 161 (17 / (100 * 12485)) (26 / (10 * 12485))
    (statisticsConstant (paperBound256 12485)) √((42 / 10 : ℝ) / 12485) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12485) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12485 : ℕ))
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
    change (√(tA 12485 * ((161 : ℝ) ^ 2 / (12485 - 2))) *
      √((42 / 10 : ℝ) / 12485) * energyCoefficient18 12485) ^ 18 *
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
    exp (-(12485 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12485 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12485 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12485

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12485) : Set (Matrix (Fin (mA 12485)) (Fin 12485) ℝ) :=
  {X | ∀ g : Fin (Js 12485),
    17 / (100 * (12485 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12485 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12485) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12485),
      {X | 17 / (100 * (12485 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12485 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12485} (hw : windowW wr) :
    (gaussMat (mA 12485) 12485 (2 / (12485 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12485,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12485 : ℝ)) ∨
      42 / (10 * (12485 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12485) : Set (Matrix (Fin (mA 12485)) (Fin 12485) ℝ) :=
  (Eop 12485 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12485))

theorem tableFirstEvent_measurable (wr : WRet 12485) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12485} (hw : windowW wr) :
    (gaussMat (mA 12485) 12485 (2 / (12485 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12485)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12485) : Set (AHid 12485) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12485) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12485} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12485) 12485 (2 / (12485 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12485) (mA 12485) (tA 12485))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12485)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12485)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12485)) := (hvar g).1
  have hmax (g : Fin (Js 12485)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12485) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12485)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12485) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12485))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12485)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12485) (mA 12485) (tA 12485)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12485) :
    (nuA 12485).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12485

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12485 × AHid 12485) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12485)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12485) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12485)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12485)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12485)) :
    (retDist (paperCentres 12485)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12485

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12485 :
    BstLean.Part262.ActualRootCertificate 12485 BstLean.Part266.agent12485.root where
  dimension := by norm_num
  table_payment := Row12485.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12485.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12485.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12486 : ℝ) *
      √(tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12486 : ℝ) ^ 24 = (12486 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) ^ 24 =
      (tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12486 ≤ (2 * 12486 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) * √((42 / 10 : ℝ) / 12486) *
      energyCoefficient18 12486) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) ^ 18 =
      (tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12486) ^ 18 = ((42 / 10 : ℝ) / 12486) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12486) ^ 9 *
        (2 * 12486 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12486

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12486 (61 / 100) 161 (17 / (100 * 12486)) (26 / (10 * 12486))
    (statisticsConstant (paperBound256 12486)) √((42 / 10 : ℝ) / 12486) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12486) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12486 : ℕ))
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
    change (√(tA 12486 * ((161 : ℝ) ^ 2 / (12486 - 2))) *
      √((42 / 10 : ℝ) / 12486) * energyCoefficient18 12486) ^ 18 *
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
    exp (-(12486 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12486 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12486 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12486

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12486) : Set (Matrix (Fin (mA 12486)) (Fin 12486) ℝ) :=
  {X | ∀ g : Fin (Js 12486),
    17 / (100 * (12486 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12486 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12486) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12486),
      {X | 17 / (100 * (12486 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12486 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12486} (hw : windowW wr) :
    (gaussMat (mA 12486) 12486 (2 / (12486 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12486,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12486 : ℝ)) ∨
      42 / (10 * (12486 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12486) : Set (Matrix (Fin (mA 12486)) (Fin 12486) ℝ) :=
  (Eop 12486 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12486))

theorem tableFirstEvent_measurable (wr : WRet 12486) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12486} (hw : windowW wr) :
    (gaussMat (mA 12486) 12486 (2 / (12486 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12486)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12486) : Set (AHid 12486) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12486) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12486} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12486) 12486 (2 / (12486 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12486) (mA 12486) (tA 12486))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12486)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12486)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12486)) := (hvar g).1
  have hmax (g : Fin (Js 12486)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12486) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12486)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12486) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12486))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12486)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12486) (mA 12486) (tA 12486)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12486) :
    (nuA 12486).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12486

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12486 × AHid 12486) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12486)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12486) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12486)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12486)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12486)) :
    (retDist (paperCentres 12486)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12486

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12486 :
    BstLean.Part262.ActualRootCertificate 12486 BstLean.Part266.agent12486.root where
  dimension := by norm_num
  table_payment := Row12486.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12486.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12486.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12487 : ℝ) *
      √(tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12487 : ℝ) ^ 24 = (12487 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) ^ 24 =
      (tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12487 ≤ (2 * 12487 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) * √((42 / 10 : ℝ) / 12487) *
      energyCoefficient18 12487) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) ^ 18 =
      (tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12487) ^ 18 = ((42 / 10 : ℝ) / 12487) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12487) ^ 9 *
        (2 * 12487 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12487

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12487 (61 / 100) 161 (17 / (100 * 12487)) (26 / (10 * 12487))
    (statisticsConstant (paperBound256 12487)) √((42 / 10 : ℝ) / 12487) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12487) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12487 : ℕ))
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
    change (√(tA 12487 * ((161 : ℝ) ^ 2 / (12487 - 2))) *
      √((42 / 10 : ℝ) / 12487) * energyCoefficient18 12487) ^ 18 *
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
    exp (-(12487 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12487 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12487 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12487

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12487) : Set (Matrix (Fin (mA 12487)) (Fin 12487) ℝ) :=
  {X | ∀ g : Fin (Js 12487),
    17 / (100 * (12487 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12487 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12487) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12487),
      {X | 17 / (100 * (12487 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12487 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12487} (hw : windowW wr) :
    (gaussMat (mA 12487) 12487 (2 / (12487 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12487,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12487 : ℝ)) ∨
      42 / (10 * (12487 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12487) : Set (Matrix (Fin (mA 12487)) (Fin 12487) ℝ) :=
  (Eop 12487 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12487))

theorem tableFirstEvent_measurable (wr : WRet 12487) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12487} (hw : windowW wr) :
    (gaussMat (mA 12487) 12487 (2 / (12487 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12487)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12487) : Set (AHid 12487) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12487) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12487} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12487) 12487 (2 / (12487 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12487) (mA 12487) (tA 12487))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12487)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12487)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12487)) := (hvar g).1
  have hmax (g : Fin (Js 12487)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12487) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12487)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12487) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12487))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12487)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12487) (mA 12487) (tA 12487)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12487) :
    (nuA 12487).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12487

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12487 × AHid 12487) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12487)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12487) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12487)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12487)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12487)) :
    (retDist (paperCentres 12487)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12487

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12487 :
    BstLean.Part262.ActualRootCertificate 12487 BstLean.Part266.agent12487.root where
  dimension := by norm_num
  table_payment := Row12487.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12487.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12487.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12488 : ℝ) *
      √(tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12488 : ℝ) ^ 24 = (12488 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) ^ 24 =
      (tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12488 ≤ (2 * 12488 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) * √((42 / 10 : ℝ) / 12488) *
      energyCoefficient18 12488) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) ^ 18 =
      (tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12488) ^ 18 = ((42 / 10 : ℝ) / 12488) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12488) ^ 9 *
        (2 * 12488 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12488

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12488 (61 / 100) 161 (17 / (100 * 12488)) (26 / (10 * 12488))
    (statisticsConstant (paperBound256 12488)) √((42 / 10 : ℝ) / 12488) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12488) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12488 : ℕ))
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
    change (√(tA 12488 * ((161 : ℝ) ^ 2 / (12488 - 2))) *
      √((42 / 10 : ℝ) / 12488) * energyCoefficient18 12488) ^ 18 *
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
    exp (-(12488 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12488 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12488 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12488

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12488) : Set (Matrix (Fin (mA 12488)) (Fin 12488) ℝ) :=
  {X | ∀ g : Fin (Js 12488),
    17 / (100 * (12488 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12488 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12488) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12488),
      {X | 17 / (100 * (12488 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12488 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12488} (hw : windowW wr) :
    (gaussMat (mA 12488) 12488 (2 / (12488 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12488,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12488 : ℝ)) ∨
      42 / (10 * (12488 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12488) : Set (Matrix (Fin (mA 12488)) (Fin 12488) ℝ) :=
  (Eop 12488 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12488))

theorem tableFirstEvent_measurable (wr : WRet 12488) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12488} (hw : windowW wr) :
    (gaussMat (mA 12488) 12488 (2 / (12488 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12488)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12488) : Set (AHid 12488) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12488) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12488} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12488) 12488 (2 / (12488 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12488) (mA 12488) (tA 12488))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12488)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12488)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12488)) := (hvar g).1
  have hmax (g : Fin (Js 12488)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12488) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12488)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12488) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12488))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12488)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12488) (mA 12488) (tA 12488)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12488) :
    (nuA 12488).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12488

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12488 × AHid 12488) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12488)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12488) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12488)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12488)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12488)) :
    (retDist (paperCentres 12488)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12488

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12488 :
    BstLean.Part262.ActualRootCertificate 12488 BstLean.Part266.agent12488.root where
  dimension := by norm_num
  table_payment := Row12488.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12488.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12488.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12489 : ℝ) *
      √(tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12489 : ℝ) ^ 24 = (12489 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) ^ 24 =
      (tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12489 ≤ (2 * 12489 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) * √((42 / 10 : ℝ) / 12489) *
      energyCoefficient18 12489) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) ^ 18 =
      (tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12489) ^ 18 = ((42 / 10 : ℝ) / 12489) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12489) ^ 9 *
        (2 * 12489 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12489

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12489 (61 / 100) 161 (17 / (100 * 12489)) (26 / (10 * 12489))
    (statisticsConstant (paperBound256 12489)) √((42 / 10 : ℝ) / 12489) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12489) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12489 : ℕ))
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
    change (√(tA 12489 * ((161 : ℝ) ^ 2 / (12489 - 2))) *
      √((42 / 10 : ℝ) / 12489) * energyCoefficient18 12489) ^ 18 *
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
    exp (-(12489 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12489 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12489 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12489

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12489) : Set (Matrix (Fin (mA 12489)) (Fin 12489) ℝ) :=
  {X | ∀ g : Fin (Js 12489),
    17 / (100 * (12489 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12489 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12489) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12489),
      {X | 17 / (100 * (12489 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12489 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12489} (hw : windowW wr) :
    (gaussMat (mA 12489) 12489 (2 / (12489 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12489,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12489 : ℝ)) ∨
      42 / (10 * (12489 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12489) : Set (Matrix (Fin (mA 12489)) (Fin 12489) ℝ) :=
  (Eop 12489 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12489))

theorem tableFirstEvent_measurable (wr : WRet 12489) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12489} (hw : windowW wr) :
    (gaussMat (mA 12489) 12489 (2 / (12489 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12489)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12489) : Set (AHid 12489) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12489) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12489} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12489) 12489 (2 / (12489 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12489) (mA 12489) (tA 12489))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12489)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12489)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12489)) := (hvar g).1
  have hmax (g : Fin (Js 12489)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12489) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12489)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12489) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12489))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12489)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12489) (mA 12489) (tA 12489)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12489) :
    (nuA 12489).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12489

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12489 × AHid 12489) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12489)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12489) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12489)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12489)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12489)) :
    (retDist (paperCentres 12489)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12489

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12489 :
    BstLean.Part262.ActualRootCertificate 12489 BstLean.Part266.agent12489.root where
  dimension := by norm_num
  table_payment := Row12489.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12489.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12489.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12490 : ℝ) *
      √(tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12490 : ℝ) ^ 24 = (12490 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) ^ 24 =
      (tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12490 ≤ (2 * 12490 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) * √((42 / 10 : ℝ) / 12490) *
      energyCoefficient18 12490) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) ^ 18 =
      (tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12490) ^ 18 = ((42 / 10 : ℝ) / 12490) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12490) ^ 9 *
        (2 * 12490 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12490

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12490 (61 / 100) 161 (17 / (100 * 12490)) (26 / (10 * 12490))
    (statisticsConstant (paperBound256 12490)) √((42 / 10 : ℝ) / 12490) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12490) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12490 : ℕ))
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
    change (√(tA 12490 * ((161 : ℝ) ^ 2 / (12490 - 2))) *
      √((42 / 10 : ℝ) / 12490) * energyCoefficient18 12490) ^ 18 *
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
    exp (-(12490 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12490 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12490 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12490

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12490) : Set (Matrix (Fin (mA 12490)) (Fin 12490) ℝ) :=
  {X | ∀ g : Fin (Js 12490),
    17 / (100 * (12490 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12490 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12490) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12490),
      {X | 17 / (100 * (12490 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12490 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12490} (hw : windowW wr) :
    (gaussMat (mA 12490) 12490 (2 / (12490 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12490,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12490 : ℝ)) ∨
      42 / (10 * (12490 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12490) : Set (Matrix (Fin (mA 12490)) (Fin 12490) ℝ) :=
  (Eop 12490 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12490))

theorem tableFirstEvent_measurable (wr : WRet 12490) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12490} (hw : windowW wr) :
    (gaussMat (mA 12490) 12490 (2 / (12490 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12490)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12490) : Set (AHid 12490) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12490) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12490} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12490) 12490 (2 / (12490 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12490) (mA 12490) (tA 12490))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12490)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12490)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12490)) := (hvar g).1
  have hmax (g : Fin (Js 12490)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12490) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12490)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12490) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12490))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12490)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12490) (mA 12490) (tA 12490)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12490) :
    (nuA 12490).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12490

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12490 × AHid 12490) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12490)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12490) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12490)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12490)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12490)) :
    (retDist (paperCentres 12490)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12490

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12490 :
    BstLean.Part262.ActualRootCertificate 12490 BstLean.Part266.agent12490.root where
  dimension := by norm_num
  table_payment := Row12490.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12490.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12490.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12491 : ℝ) *
      √(tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12491 : ℝ) ^ 24 = (12491 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) ^ 24 =
      (tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12491 ≤ (2 * 12491 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) * √((42 / 10 : ℝ) / 12491) *
      energyCoefficient18 12491) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) ^ 18 =
      (tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12491) ^ 18 = ((42 / 10 : ℝ) / 12491) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12491) ^ 9 *
        (2 * 12491 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12491

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12491 (61 / 100) 161 (17 / (100 * 12491)) (26 / (10 * 12491))
    (statisticsConstant (paperBound256 12491)) √((42 / 10 : ℝ) / 12491) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12491) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12491 : ℕ))
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
    change (√(tA 12491 * ((161 : ℝ) ^ 2 / (12491 - 2))) *
      √((42 / 10 : ℝ) / 12491) * energyCoefficient18 12491) ^ 18 *
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
    exp (-(12491 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12491 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12491 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12491

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12491) : Set (Matrix (Fin (mA 12491)) (Fin 12491) ℝ) :=
  {X | ∀ g : Fin (Js 12491),
    17 / (100 * (12491 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12491 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12491) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12491),
      {X | 17 / (100 * (12491 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12491 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12491} (hw : windowW wr) :
    (gaussMat (mA 12491) 12491 (2 / (12491 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12491,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12491 : ℝ)) ∨
      42 / (10 * (12491 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12491) : Set (Matrix (Fin (mA 12491)) (Fin 12491) ℝ) :=
  (Eop 12491 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12491))

theorem tableFirstEvent_measurable (wr : WRet 12491) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12491} (hw : windowW wr) :
    (gaussMat (mA 12491) 12491 (2 / (12491 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12491)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12491) : Set (AHid 12491) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12491) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12491} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12491) 12491 (2 / (12491 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12491) (mA 12491) (tA 12491))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12491)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12491)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12491)) := (hvar g).1
  have hmax (g : Fin (Js 12491)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12491) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12491)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12491) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12491))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12491)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12491) (mA 12491) (tA 12491)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12491) :
    (nuA 12491).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12491

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12491 × AHid 12491) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12491)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12491) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12491)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12491)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12491)) :
    (retDist (paperCentres 12491)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12491

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12491 :
    BstLean.Part262.ActualRootCertificate 12491 BstLean.Part266.agent12491.root where
  dimension := by norm_num
  table_payment := Row12491.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12491.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12491.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12492 : ℝ) *
      √(tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12492 : ℝ) ^ 24 = (12492 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) ^ 24 =
      (tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12492 ≤ (2 * 12492 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) * √((42 / 10 : ℝ) / 12492) *
      energyCoefficient18 12492) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) ^ 18 =
      (tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12492) ^ 18 = ((42 / 10 : ℝ) / 12492) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12492) ^ 9 *
        (2 * 12492 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12492

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12492 (61 / 100) 161 (17 / (100 * 12492)) (26 / (10 * 12492))
    (statisticsConstant (paperBound256 12492)) √((42 / 10 : ℝ) / 12492) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12492) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12492 : ℕ))
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
    change (√(tA 12492 * ((161 : ℝ) ^ 2 / (12492 - 2))) *
      √((42 / 10 : ℝ) / 12492) * energyCoefficient18 12492) ^ 18 *
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
    exp (-(12492 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12492 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12492 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12492

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12492) : Set (Matrix (Fin (mA 12492)) (Fin 12492) ℝ) :=
  {X | ∀ g : Fin (Js 12492),
    17 / (100 * (12492 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12492 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12492) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12492),
      {X | 17 / (100 * (12492 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12492 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12492} (hw : windowW wr) :
    (gaussMat (mA 12492) 12492 (2 / (12492 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12492,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12492 : ℝ)) ∨
      42 / (10 * (12492 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12492) : Set (Matrix (Fin (mA 12492)) (Fin 12492) ℝ) :=
  (Eop 12492 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12492))

theorem tableFirstEvent_measurable (wr : WRet 12492) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12492} (hw : windowW wr) :
    (gaussMat (mA 12492) 12492 (2 / (12492 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12492)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12492) : Set (AHid 12492) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12492) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12492} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12492) 12492 (2 / (12492 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12492) (mA 12492) (tA 12492))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12492)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12492)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12492)) := (hvar g).1
  have hmax (g : Fin (Js 12492)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12492) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12492)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12492) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12492))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12492)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12492) (mA 12492) (tA 12492)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12492) :
    (nuA 12492).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12492

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12492 × AHid 12492) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12492)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12492) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12492)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12492)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12492)) :
    (retDist (paperCentres 12492)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12492

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12492 :
    BstLean.Part262.ActualRootCertificate 12492 BstLean.Part266.agent12492.root where
  dimension := by norm_num
  table_payment := Row12492.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12492.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12492.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12493 : ℝ) *
      √(tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12493 : ℝ) ^ 24 = (12493 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) ^ 24 =
      (tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12493 ≤ (2 * 12493 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) * √((42 / 10 : ℝ) / 12493) *
      energyCoefficient18 12493) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) ^ 18 =
      (tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12493) ^ 18 = ((42 / 10 : ℝ) / 12493) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12493) ^ 9 *
        (2 * 12493 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12493

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12493 (61 / 100) 161 (17 / (100 * 12493)) (26 / (10 * 12493))
    (statisticsConstant (paperBound256 12493)) √((42 / 10 : ℝ) / 12493) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12493) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12493 : ℕ))
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
    change (√(tA 12493 * ((161 : ℝ) ^ 2 / (12493 - 2))) *
      √((42 / 10 : ℝ) / 12493) * energyCoefficient18 12493) ^ 18 *
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
    exp (-(12493 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12493 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12493 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12493

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12493) : Set (Matrix (Fin (mA 12493)) (Fin 12493) ℝ) :=
  {X | ∀ g : Fin (Js 12493),
    17 / (100 * (12493 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12493 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12493) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12493),
      {X | 17 / (100 * (12493 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12493 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12493} (hw : windowW wr) :
    (gaussMat (mA 12493) 12493 (2 / (12493 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12493,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12493 : ℝ)) ∨
      42 / (10 * (12493 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12493) : Set (Matrix (Fin (mA 12493)) (Fin 12493) ℝ) :=
  (Eop 12493 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12493))

theorem tableFirstEvent_measurable (wr : WRet 12493) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12493} (hw : windowW wr) :
    (gaussMat (mA 12493) 12493 (2 / (12493 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12493)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12493) : Set (AHid 12493) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12493) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12493} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12493) 12493 (2 / (12493 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12493) (mA 12493) (tA 12493))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12493)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12493)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12493)) := (hvar g).1
  have hmax (g : Fin (Js 12493)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12493) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12493)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12493) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12493))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12493)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12493) (mA 12493) (tA 12493)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12493) :
    (nuA 12493).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12493

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12493 × AHid 12493) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12493)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12493) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12493)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12493)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12493)) :
    (retDist (paperCentres 12493)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12493

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12493 :
    BstLean.Part262.ActualRootCertificate 12493 BstLean.Part266.agent12493.root where
  dimension := by norm_num
  table_payment := Row12493.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12493.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12493.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12494 : ℝ) *
      √(tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12494 : ℝ) ^ 24 = (12494 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) ^ 24 =
      (tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12494 ≤ (2 * 12494 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) * √((42 / 10 : ℝ) / 12494) *
      energyCoefficient18 12494) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) ^ 18 =
      (tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12494) ^ 18 = ((42 / 10 : ℝ) / 12494) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12494) ^ 9 *
        (2 * 12494 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12494

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12494 (61 / 100) 161 (17 / (100 * 12494)) (26 / (10 * 12494))
    (statisticsConstant (paperBound256 12494)) √((42 / 10 : ℝ) / 12494) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12494) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12494 : ℕ))
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
    change (√(tA 12494 * ((161 : ℝ) ^ 2 / (12494 - 2))) *
      √((42 / 10 : ℝ) / 12494) * energyCoefficient18 12494) ^ 18 *
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
    exp (-(12494 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12494 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12494 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12494

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12494) : Set (Matrix (Fin (mA 12494)) (Fin 12494) ℝ) :=
  {X | ∀ g : Fin (Js 12494),
    17 / (100 * (12494 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12494 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12494) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12494),
      {X | 17 / (100 * (12494 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12494 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12494} (hw : windowW wr) :
    (gaussMat (mA 12494) 12494 (2 / (12494 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12494,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12494 : ℝ)) ∨
      42 / (10 * (12494 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12494) : Set (Matrix (Fin (mA 12494)) (Fin 12494) ℝ) :=
  (Eop 12494 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12494))

theorem tableFirstEvent_measurable (wr : WRet 12494) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12494} (hw : windowW wr) :
    (gaussMat (mA 12494) 12494 (2 / (12494 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12494)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12494) : Set (AHid 12494) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12494) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12494} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12494) 12494 (2 / (12494 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12494) (mA 12494) (tA 12494))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12494)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12494)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12494)) := (hvar g).1
  have hmax (g : Fin (Js 12494)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12494) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12494)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12494) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12494))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12494)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12494) (mA 12494) (tA 12494)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12494) :
    (nuA 12494).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12494

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12494 × AHid 12494) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12494)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12494) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12494)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12494)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12494)) :
    (retDist (paperCentres 12494)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12494

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12494 :
    BstLean.Part262.ActualRootCertificate 12494 BstLean.Part266.agent12494.root where
  dimension := by norm_num
  table_payment := Row12494.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12494.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12494.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12495 : ℝ) *
      √(tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12495 : ℝ) ^ 24 = (12495 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) ^ 24 =
      (tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12495 ≤ (2 * 12495 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) * √((42 / 10 : ℝ) / 12495) *
      energyCoefficient18 12495) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) ^ 18 =
      (tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12495) ^ 18 = ((42 / 10 : ℝ) / 12495) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12495) ^ 9 *
        (2 * 12495 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12495

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12495 (61 / 100) 161 (17 / (100 * 12495)) (26 / (10 * 12495))
    (statisticsConstant (paperBound256 12495)) √((42 / 10 : ℝ) / 12495) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12495) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12495 : ℕ))
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
    change (√(tA 12495 * ((161 : ℝ) ^ 2 / (12495 - 2))) *
      √((42 / 10 : ℝ) / 12495) * energyCoefficient18 12495) ^ 18 *
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
    exp (-(12495 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12495 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12495 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12495

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12495) : Set (Matrix (Fin (mA 12495)) (Fin 12495) ℝ) :=
  {X | ∀ g : Fin (Js 12495),
    17 / (100 * (12495 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12495 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12495) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12495),
      {X | 17 / (100 * (12495 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12495 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12495} (hw : windowW wr) :
    (gaussMat (mA 12495) 12495 (2 / (12495 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12495,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12495 : ℝ)) ∨
      42 / (10 * (12495 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12495) : Set (Matrix (Fin (mA 12495)) (Fin 12495) ℝ) :=
  (Eop 12495 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12495))

theorem tableFirstEvent_measurable (wr : WRet 12495) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12495} (hw : windowW wr) :
    (gaussMat (mA 12495) 12495 (2 / (12495 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12495)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12495) : Set (AHid 12495) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12495) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12495} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12495) 12495 (2 / (12495 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12495) (mA 12495) (tA 12495))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12495)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12495)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12495)) := (hvar g).1
  have hmax (g : Fin (Js 12495)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12495) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12495)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12495) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12495))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12495)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12495) (mA 12495) (tA 12495)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12495) :
    (nuA 12495).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12495

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12495 × AHid 12495) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12495)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12495) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12495)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12495)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12495)) :
    (retDist (paperCentres 12495)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12495

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12495 :
    BstLean.Part262.ActualRootCertificate 12495 BstLean.Part266.agent12495.root where
  dimension := by norm_num
  table_payment := Row12495.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12495.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12495.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12496 : ℝ) *
      √(tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12496 : ℝ) ^ 24 = (12496 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) ^ 24 =
      (tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12496 ≤ (2 * 12496 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) * √((42 / 10 : ℝ) / 12496) *
      energyCoefficient18 12496) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) ^ 18 =
      (tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12496) ^ 18 = ((42 / 10 : ℝ) / 12496) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12496) ^ 9 *
        (2 * 12496 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12496

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12496 (61 / 100) 161 (17 / (100 * 12496)) (26 / (10 * 12496))
    (statisticsConstant (paperBound256 12496)) √((42 / 10 : ℝ) / 12496) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12496) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12496 : ℕ))
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
    change (√(tA 12496 * ((161 : ℝ) ^ 2 / (12496 - 2))) *
      √((42 / 10 : ℝ) / 12496) * energyCoefficient18 12496) ^ 18 *
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
    exp (-(12496 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12496 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12496 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12496

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12496) : Set (Matrix (Fin (mA 12496)) (Fin 12496) ℝ) :=
  {X | ∀ g : Fin (Js 12496),
    17 / (100 * (12496 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12496 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12496) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12496),
      {X | 17 / (100 * (12496 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12496 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12496} (hw : windowW wr) :
    (gaussMat (mA 12496) 12496 (2 / (12496 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12496,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12496 : ℝ)) ∨
      42 / (10 * (12496 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12496) : Set (Matrix (Fin (mA 12496)) (Fin 12496) ℝ) :=
  (Eop 12496 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12496))

theorem tableFirstEvent_measurable (wr : WRet 12496) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12496} (hw : windowW wr) :
    (gaussMat (mA 12496) 12496 (2 / (12496 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12496)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12496) : Set (AHid 12496) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12496) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12496} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12496) 12496 (2 / (12496 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12496) (mA 12496) (tA 12496))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12496)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12496)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12496)) := (hvar g).1
  have hmax (g : Fin (Js 12496)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12496) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12496)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12496) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12496))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12496)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12496) (mA 12496) (tA 12496)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12496) :
    (nuA 12496).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12496

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12496 × AHid 12496) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12496)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12496) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12496)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12496)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12496)) :
    (retDist (paperCentres 12496)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12496

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12496 :
    BstLean.Part262.ActualRootCertificate 12496 BstLean.Part266.agent12496.root where
  dimension := by norm_num
  table_payment := Row12496.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12496.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12496.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12497 : ℝ) *
      √(tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12497 : ℝ) ^ 24 = (12497 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) ^ 24 =
      (tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12497 ≤ (2 * 12497 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) * √((42 / 10 : ℝ) / 12497) *
      energyCoefficient18 12497) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) ^ 18 =
      (tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12497) ^ 18 = ((42 / 10 : ℝ) / 12497) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12497) ^ 9 *
        (2 * 12497 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12497

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12497 (61 / 100) 161 (17 / (100 * 12497)) (26 / (10 * 12497))
    (statisticsConstant (paperBound256 12497)) √((42 / 10 : ℝ) / 12497) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12497) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12497 : ℕ))
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
    change (√(tA 12497 * ((161 : ℝ) ^ 2 / (12497 - 2))) *
      √((42 / 10 : ℝ) / 12497) * energyCoefficient18 12497) ^ 18 *
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
    exp (-(12497 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12497 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12497 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12497

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12497) : Set (Matrix (Fin (mA 12497)) (Fin 12497) ℝ) :=
  {X | ∀ g : Fin (Js 12497),
    17 / (100 * (12497 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12497 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12497) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12497),
      {X | 17 / (100 * (12497 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12497 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12497} (hw : windowW wr) :
    (gaussMat (mA 12497) 12497 (2 / (12497 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12497,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12497 : ℝ)) ∨
      42 / (10 * (12497 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12497) : Set (Matrix (Fin (mA 12497)) (Fin 12497) ℝ) :=
  (Eop 12497 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12497))

theorem tableFirstEvent_measurable (wr : WRet 12497) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12497} (hw : windowW wr) :
    (gaussMat (mA 12497) 12497 (2 / (12497 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12497)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12497) : Set (AHid 12497) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12497) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12497} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12497) 12497 (2 / (12497 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12497) (mA 12497) (tA 12497))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12497)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12497)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12497)) := (hvar g).1
  have hmax (g : Fin (Js 12497)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12497) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12497)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12497) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12497))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12497)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12497) (mA 12497) (tA 12497)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12497) :
    (nuA 12497).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12497

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12497 × AHid 12497) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12497)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12497) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12497)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12497)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12497)) :
    (retDist (paperCentres 12497)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12497

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12497 :
    BstLean.Part262.ActualRootCertificate 12497 BstLean.Part266.agent12497.root where
  dimension := by norm_num
  table_payment := Row12497.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12497.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12497.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12498 : ℝ) *
      √(tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12498 : ℝ) ^ 24 = (12498 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) ^ 24 =
      (tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12498 ≤ (2 * 12498 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) * √((42 / 10 : ℝ) / 12498) *
      energyCoefficient18 12498) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) ^ 18 =
      (tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12498) ^ 18 = ((42 / 10 : ℝ) / 12498) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12498) ^ 9 *
        (2 * 12498 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12498

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12498 (61 / 100) 161 (17 / (100 * 12498)) (26 / (10 * 12498))
    (statisticsConstant (paperBound256 12498)) √((42 / 10 : ℝ) / 12498) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12498) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12498 : ℕ))
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
    change (√(tA 12498 * ((161 : ℝ) ^ 2 / (12498 - 2))) *
      √((42 / 10 : ℝ) / 12498) * energyCoefficient18 12498) ^ 18 *
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
    exp (-(12498 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12498 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12498 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12498

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12498) : Set (Matrix (Fin (mA 12498)) (Fin 12498) ℝ) :=
  {X | ∀ g : Fin (Js 12498),
    17 / (100 * (12498 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12498 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12498) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12498),
      {X | 17 / (100 * (12498 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12498 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12498} (hw : windowW wr) :
    (gaussMat (mA 12498) 12498 (2 / (12498 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12498,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12498 : ℝ)) ∨
      42 / (10 * (12498 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12498) : Set (Matrix (Fin (mA 12498)) (Fin 12498) ℝ) :=
  (Eop 12498 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12498))

theorem tableFirstEvent_measurable (wr : WRet 12498) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12498} (hw : windowW wr) :
    (gaussMat (mA 12498) 12498 (2 / (12498 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12498)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12498) : Set (AHid 12498) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12498) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12498} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12498) 12498 (2 / (12498 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12498) (mA 12498) (tA 12498))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12498)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12498)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12498)) := (hvar g).1
  have hmax (g : Fin (Js 12498)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12498) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12498)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12498) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12498))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12498)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12498) (mA 12498) (tA 12498)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12498) :
    (nuA 12498).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12498

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12498 × AHid 12498) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12498)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12498) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12498)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12498)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12498)) :
    (retDist (paperCentres 12498)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12498

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12498 :
    BstLean.Part262.ActualRootCertificate 12498 BstLean.Part266.agent12498.root where
  dimension := by norm_num
  table_payment := Row12498.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12498.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12498.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12499 : ℝ) *
      √(tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12499 : ℝ) ^ 24 = (12499 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) ^ 24 =
      (tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12499 ≤ (2 * 12499 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) * √((42 / 10 : ℝ) / 12499) *
      energyCoefficient18 12499) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) ^ 18 =
      (tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12499) ^ 18 = ((42 / 10 : ℝ) / 12499) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12499) ^ 9 *
        (2 * 12499 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12499

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12499 (61 / 100) 161 (17 / (100 * 12499)) (26 / (10 * 12499))
    (statisticsConstant (paperBound256 12499)) √((42 / 10 : ℝ) / 12499) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12499) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12499 : ℕ))
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
    change (√(tA 12499 * ((161 : ℝ) ^ 2 / (12499 - 2))) *
      √((42 / 10 : ℝ) / 12499) * energyCoefficient18 12499) ^ 18 *
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
    exp (-(12499 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12499 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12499 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12499

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12499) : Set (Matrix (Fin (mA 12499)) (Fin 12499) ℝ) :=
  {X | ∀ g : Fin (Js 12499),
    17 / (100 * (12499 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12499 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12499) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12499),
      {X | 17 / (100 * (12499 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12499 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12499} (hw : windowW wr) :
    (gaussMat (mA 12499) 12499 (2 / (12499 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12499,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12499 : ℝ)) ∨
      42 / (10 * (12499 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12499) : Set (Matrix (Fin (mA 12499)) (Fin 12499) ℝ) :=
  (Eop 12499 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12499))

theorem tableFirstEvent_measurable (wr : WRet 12499) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12499} (hw : windowW wr) :
    (gaussMat (mA 12499) 12499 (2 / (12499 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12499)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12499) : Set (AHid 12499) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12499) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12499} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12499) 12499 (2 / (12499 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12499) (mA 12499) (tA 12499))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12499)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12499)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12499)) := (hvar g).1
  have hmax (g : Fin (Js 12499)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12499) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12499)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12499) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 161) (by norm_num : (0 : ℝ) < 17 / (100 * 12499))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12499)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12499) (mA 12499) (tA 12499)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12499) :
    (nuA 12499).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12499

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12499 × AHid 12499) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12499)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12499) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12499)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12499)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12499)) :
    (retDist (paperCentres 12499)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12499

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12499 :
    BstLean.Part262.ActualRootCertificate 12499 BstLean.Part266.agent12499.root where
  dimension := by norm_num
  table_payment := Row12499.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12499.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12499.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266
