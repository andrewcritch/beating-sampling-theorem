import BstLean.Part266Shard26Step5


/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13000
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13000 : ℝ) *
      √(tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13000 : ℝ) ^ 24 = (13000 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) ^ 24 =
      (tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13000 ≤ (2 * 13000 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) * √((42 / 10 : ℝ) / 13000) *
      energyCoefficient18 13000) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) ^ 18 =
      (tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13000) ^ 18 = ((42 / 10 : ℝ) / 13000) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13000) ^ 9 *
        (2 * 13000 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13000

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13000
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13000 (61 / 100) 165 (17 / (100 * 13000)) (26 / (10 * 13000))
    (statisticsConstant (paperBound256 13000)) √((42 / 10 : ℝ) / 13000) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13000) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13000 : ℕ))
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
    change (√(tA 13000 * ((165 : ℝ) ^ 2 / (13000 - 2))) *
      √((42 / 10 : ℝ) / 13000) * energyCoefficient18 13000) ^ 18 *
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
    exp (-(13000 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13000 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13000 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13000

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13000
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13000) : Set (Matrix (Fin (mA 13000)) (Fin 13000) ℝ) :=
  {X | ∀ g : Fin (Js 13000),
    17 / (100 * (13000 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13000 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13000) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13000),
      {X | 17 / (100 * (13000 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13000 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13000} (hw : windowW wr) :
    (gaussMat (mA 13000) 13000 (2 / (13000 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13000,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13000 : ℝ)) ∨
      42 / (10 * (13000 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13000) : Set (Matrix (Fin (mA 13000)) (Fin 13000) ℝ) :=
  (Eop 13000 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13000))

theorem tableFirstEvent_measurable (wr : WRet 13000) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13000} (hw : windowW wr) :
    (gaussMat (mA 13000) 13000 (2 / (13000 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13000)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13000) : Set (AHid 13000) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13000) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13000} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13000) 13000 (2 / (13000 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13000) (mA 13000) (tA 13000))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13000)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13000)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13000)) := (hvar g).1
  have hmax (g : Fin (Js 13000)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13000) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13000)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13000) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13000))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13000)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13000) (mA 13000) (tA 13000)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13000) :
    (nuA 13000).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13000

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13000
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13000 × AHid 13000) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13000)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13000) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13000)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13000)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13000)) :
    (retDist (paperCentres 13000)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13000

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13000 :
    BstLean.Part262.ActualRootCertificate 13000 BstLean.Part266.agent13000.root where
  dimension := by norm_num
  table_payment := Row13000.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13000.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13000.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13001
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13001 : ℝ) *
      √(tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13001 : ℝ) ^ 24 = (13001 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) ^ 24 =
      (tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13001 ≤ (2 * 13001 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) * √((42 / 10 : ℝ) / 13001) *
      energyCoefficient18 13001) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) ^ 18 =
      (tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13001) ^ 18 = ((42 / 10 : ℝ) / 13001) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13001) ^ 9 *
        (2 * 13001 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13001

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13001
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13001 (61 / 100) 165 (17 / (100 * 13001)) (26 / (10 * 13001))
    (statisticsConstant (paperBound256 13001)) √((42 / 10 : ℝ) / 13001) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13001) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13001 : ℕ))
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
    change (√(tA 13001 * ((165 : ℝ) ^ 2 / (13001 - 2))) *
      √((42 / 10 : ℝ) / 13001) * energyCoefficient18 13001) ^ 18 *
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
    exp (-(13001 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13001 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13001 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13001

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13001
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13001) : Set (Matrix (Fin (mA 13001)) (Fin 13001) ℝ) :=
  {X | ∀ g : Fin (Js 13001),
    17 / (100 * (13001 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13001 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13001) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13001),
      {X | 17 / (100 * (13001 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13001 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13001} (hw : windowW wr) :
    (gaussMat (mA 13001) 13001 (2 / (13001 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13001,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13001 : ℝ)) ∨
      42 / (10 * (13001 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13001) : Set (Matrix (Fin (mA 13001)) (Fin 13001) ℝ) :=
  (Eop 13001 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13001))

theorem tableFirstEvent_measurable (wr : WRet 13001) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13001} (hw : windowW wr) :
    (gaussMat (mA 13001) 13001 (2 / (13001 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13001)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13001) : Set (AHid 13001) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13001) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13001} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13001) 13001 (2 / (13001 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13001) (mA 13001) (tA 13001))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13001)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13001)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13001)) := (hvar g).1
  have hmax (g : Fin (Js 13001)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13001) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13001)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13001) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13001))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13001)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13001) (mA 13001) (tA 13001)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13001) :
    (nuA 13001).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13001

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13001
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13001 × AHid 13001) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13001)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13001) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13001)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13001)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13001)) :
    (retDist (paperCentres 13001)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13001

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13001 :
    BstLean.Part262.ActualRootCertificate 13001 BstLean.Part266.agent13001.root where
  dimension := by norm_num
  table_payment := Row13001.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13001.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13001.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13002
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13002 : ℝ) *
      √(tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13002 : ℝ) ^ 24 = (13002 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) ^ 24 =
      (tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13002 ≤ (2 * 13002 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) * √((42 / 10 : ℝ) / 13002) *
      energyCoefficient18 13002) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) ^ 18 =
      (tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13002) ^ 18 = ((42 / 10 : ℝ) / 13002) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13002) ^ 9 *
        (2 * 13002 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13002

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13002
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13002 (61 / 100) 165 (17 / (100 * 13002)) (26 / (10 * 13002))
    (statisticsConstant (paperBound256 13002)) √((42 / 10 : ℝ) / 13002) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13002) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13002 : ℕ))
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
    change (√(tA 13002 * ((165 : ℝ) ^ 2 / (13002 - 2))) *
      √((42 / 10 : ℝ) / 13002) * energyCoefficient18 13002) ^ 18 *
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
    exp (-(13002 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13002 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13002 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13002

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13002
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13002) : Set (Matrix (Fin (mA 13002)) (Fin 13002) ℝ) :=
  {X | ∀ g : Fin (Js 13002),
    17 / (100 * (13002 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13002 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13002) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13002),
      {X | 17 / (100 * (13002 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13002 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13002} (hw : windowW wr) :
    (gaussMat (mA 13002) 13002 (2 / (13002 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13002,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13002 : ℝ)) ∨
      42 / (10 * (13002 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13002) : Set (Matrix (Fin (mA 13002)) (Fin 13002) ℝ) :=
  (Eop 13002 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13002))

theorem tableFirstEvent_measurable (wr : WRet 13002) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13002} (hw : windowW wr) :
    (gaussMat (mA 13002) 13002 (2 / (13002 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13002)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13002) : Set (AHid 13002) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13002) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13002} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13002) 13002 (2 / (13002 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13002) (mA 13002) (tA 13002))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13002)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13002)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13002)) := (hvar g).1
  have hmax (g : Fin (Js 13002)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13002) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13002)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13002) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13002))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13002)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13002) (mA 13002) (tA 13002)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13002) :
    (nuA 13002).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13002

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13002
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13002 × AHid 13002) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13002)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13002) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13002)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13002)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13002)) :
    (retDist (paperCentres 13002)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13002

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13002 :
    BstLean.Part262.ActualRootCertificate 13002 BstLean.Part266.agent13002.root where
  dimension := by norm_num
  table_payment := Row13002.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13002.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13002.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13003
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13003 : ℝ) *
      √(tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13003 : ℝ) ^ 24 = (13003 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) ^ 24 =
      (tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13003 ≤ (2 * 13003 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) * √((42 / 10 : ℝ) / 13003) *
      energyCoefficient18 13003) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) ^ 18 =
      (tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13003) ^ 18 = ((42 / 10 : ℝ) / 13003) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13003) ^ 9 *
        (2 * 13003 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13003

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13003
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13003 (61 / 100) 165 (17 / (100 * 13003)) (26 / (10 * 13003))
    (statisticsConstant (paperBound256 13003)) √((42 / 10 : ℝ) / 13003) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13003) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13003 : ℕ))
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
    change (√(tA 13003 * ((165 : ℝ) ^ 2 / (13003 - 2))) *
      √((42 / 10 : ℝ) / 13003) * energyCoefficient18 13003) ^ 18 *
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
    exp (-(13003 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13003 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13003 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13003

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13003
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13003) : Set (Matrix (Fin (mA 13003)) (Fin 13003) ℝ) :=
  {X | ∀ g : Fin (Js 13003),
    17 / (100 * (13003 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13003 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13003) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13003),
      {X | 17 / (100 * (13003 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13003 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13003} (hw : windowW wr) :
    (gaussMat (mA 13003) 13003 (2 / (13003 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13003,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13003 : ℝ)) ∨
      42 / (10 * (13003 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13003) : Set (Matrix (Fin (mA 13003)) (Fin 13003) ℝ) :=
  (Eop 13003 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13003))

theorem tableFirstEvent_measurable (wr : WRet 13003) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13003} (hw : windowW wr) :
    (gaussMat (mA 13003) 13003 (2 / (13003 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13003)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13003) : Set (AHid 13003) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13003) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13003} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13003) 13003 (2 / (13003 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13003) (mA 13003) (tA 13003))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13003)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13003)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13003)) := (hvar g).1
  have hmax (g : Fin (Js 13003)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13003) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13003)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13003) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13003))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13003)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13003) (mA 13003) (tA 13003)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13003) :
    (nuA 13003).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13003

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13003
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13003 × AHid 13003) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13003)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13003) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13003)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13003)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13003)) :
    (retDist (paperCentres 13003)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13003

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13003 :
    BstLean.Part262.ActualRootCertificate 13003 BstLean.Part266.agent13003.root where
  dimension := by norm_num
  table_payment := Row13003.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13003.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13003.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13004
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13004 : ℝ) *
      √(tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13004 : ℝ) ^ 24 = (13004 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) ^ 24 =
      (tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13004 ≤ (2 * 13004 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) * √((42 / 10 : ℝ) / 13004) *
      energyCoefficient18 13004) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) ^ 18 =
      (tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13004) ^ 18 = ((42 / 10 : ℝ) / 13004) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13004) ^ 9 *
        (2 * 13004 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13004

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13004
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13004 (61 / 100) 165 (17 / (100 * 13004)) (26 / (10 * 13004))
    (statisticsConstant (paperBound256 13004)) √((42 / 10 : ℝ) / 13004) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13004) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13004 : ℕ))
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
    change (√(tA 13004 * ((165 : ℝ) ^ 2 / (13004 - 2))) *
      √((42 / 10 : ℝ) / 13004) * energyCoefficient18 13004) ^ 18 *
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
    exp (-(13004 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13004 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13004 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13004

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13004
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13004) : Set (Matrix (Fin (mA 13004)) (Fin 13004) ℝ) :=
  {X | ∀ g : Fin (Js 13004),
    17 / (100 * (13004 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13004 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13004) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13004),
      {X | 17 / (100 * (13004 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13004 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13004} (hw : windowW wr) :
    (gaussMat (mA 13004) 13004 (2 / (13004 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13004,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13004 : ℝ)) ∨
      42 / (10 * (13004 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13004) : Set (Matrix (Fin (mA 13004)) (Fin 13004) ℝ) :=
  (Eop 13004 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13004))

theorem tableFirstEvent_measurable (wr : WRet 13004) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13004} (hw : windowW wr) :
    (gaussMat (mA 13004) 13004 (2 / (13004 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13004)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13004) : Set (AHid 13004) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13004) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13004} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13004) 13004 (2 / (13004 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13004) (mA 13004) (tA 13004))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13004)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13004)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13004)) := (hvar g).1
  have hmax (g : Fin (Js 13004)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13004) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13004)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13004) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13004))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13004)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13004) (mA 13004) (tA 13004)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13004) :
    (nuA 13004).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13004

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13004
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13004 × AHid 13004) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13004)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13004) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13004)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13004)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13004)) :
    (retDist (paperCentres 13004)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13004

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13004 :
    BstLean.Part262.ActualRootCertificate 13004 BstLean.Part266.agent13004.root where
  dimension := by norm_num
  table_payment := Row13004.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13004.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13004.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13005
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13005 : ℝ) *
      √(tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13005 : ℝ) ^ 24 = (13005 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) ^ 24 =
      (tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13005 ≤ (2 * 13005 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) * √((42 / 10 : ℝ) / 13005) *
      energyCoefficient18 13005) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) ^ 18 =
      (tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13005) ^ 18 = ((42 / 10 : ℝ) / 13005) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13005) ^ 9 *
        (2 * 13005 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13005

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13005
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13005 (61 / 100) 165 (17 / (100 * 13005)) (26 / (10 * 13005))
    (statisticsConstant (paperBound256 13005)) √((42 / 10 : ℝ) / 13005) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13005) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13005 : ℕ))
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
    change (√(tA 13005 * ((165 : ℝ) ^ 2 / (13005 - 2))) *
      √((42 / 10 : ℝ) / 13005) * energyCoefficient18 13005) ^ 18 *
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
    exp (-(13005 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13005 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13005 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13005

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13005
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13005) : Set (Matrix (Fin (mA 13005)) (Fin 13005) ℝ) :=
  {X | ∀ g : Fin (Js 13005),
    17 / (100 * (13005 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13005 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13005) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13005),
      {X | 17 / (100 * (13005 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13005 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13005} (hw : windowW wr) :
    (gaussMat (mA 13005) 13005 (2 / (13005 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13005,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13005 : ℝ)) ∨
      42 / (10 * (13005 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13005) : Set (Matrix (Fin (mA 13005)) (Fin 13005) ℝ) :=
  (Eop 13005 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13005))

theorem tableFirstEvent_measurable (wr : WRet 13005) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13005} (hw : windowW wr) :
    (gaussMat (mA 13005) 13005 (2 / (13005 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13005)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13005) : Set (AHid 13005) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13005) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13005} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13005) 13005 (2 / (13005 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13005) (mA 13005) (tA 13005))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13005)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13005)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13005)) := (hvar g).1
  have hmax (g : Fin (Js 13005)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13005) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13005)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13005) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13005))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13005)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13005) (mA 13005) (tA 13005)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13005) :
    (nuA 13005).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13005

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13005
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13005 × AHid 13005) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13005)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13005) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13005)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13005)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13005)) :
    (retDist (paperCentres 13005)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13005

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13005 :
    BstLean.Part262.ActualRootCertificate 13005 BstLean.Part266.agent13005.root where
  dimension := by norm_num
  table_payment := Row13005.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13005.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13005.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13006
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13006 : ℝ) *
      √(tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13006 : ℝ) ^ 24 = (13006 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) ^ 24 =
      (tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13006 ≤ (2 * 13006 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) * √((42 / 10 : ℝ) / 13006) *
      energyCoefficient18 13006) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) ^ 18 =
      (tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13006) ^ 18 = ((42 / 10 : ℝ) / 13006) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13006) ^ 9 *
        (2 * 13006 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13006

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13006
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13006 (61 / 100) 165 (17 / (100 * 13006)) (26 / (10 * 13006))
    (statisticsConstant (paperBound256 13006)) √((42 / 10 : ℝ) / 13006) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13006) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13006 : ℕ))
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
    change (√(tA 13006 * ((165 : ℝ) ^ 2 / (13006 - 2))) *
      √((42 / 10 : ℝ) / 13006) * energyCoefficient18 13006) ^ 18 *
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
    exp (-(13006 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13006 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13006 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13006

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13006
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13006) : Set (Matrix (Fin (mA 13006)) (Fin 13006) ℝ) :=
  {X | ∀ g : Fin (Js 13006),
    17 / (100 * (13006 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13006 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13006) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13006),
      {X | 17 / (100 * (13006 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13006 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13006} (hw : windowW wr) :
    (gaussMat (mA 13006) 13006 (2 / (13006 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13006,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13006 : ℝ)) ∨
      42 / (10 * (13006 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13006) : Set (Matrix (Fin (mA 13006)) (Fin 13006) ℝ) :=
  (Eop 13006 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13006))

theorem tableFirstEvent_measurable (wr : WRet 13006) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13006} (hw : windowW wr) :
    (gaussMat (mA 13006) 13006 (2 / (13006 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13006)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13006) : Set (AHid 13006) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13006) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13006} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13006) 13006 (2 / (13006 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13006) (mA 13006) (tA 13006))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13006)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13006)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13006)) := (hvar g).1
  have hmax (g : Fin (Js 13006)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13006) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13006)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13006) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13006))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13006)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13006) (mA 13006) (tA 13006)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13006) :
    (nuA 13006).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13006

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13006
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13006 × AHid 13006) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13006)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13006) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13006)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13006)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13006)) :
    (retDist (paperCentres 13006)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13006

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13006 :
    BstLean.Part262.ActualRootCertificate 13006 BstLean.Part266.agent13006.root where
  dimension := by norm_num
  table_payment := Row13006.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13006.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13006.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13007
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13007 : ℝ) *
      √(tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13007 : ℝ) ^ 24 = (13007 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) ^ 24 =
      (tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13007 ≤ (2 * 13007 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) * √((42 / 10 : ℝ) / 13007) *
      energyCoefficient18 13007) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) ^ 18 =
      (tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13007) ^ 18 = ((42 / 10 : ℝ) / 13007) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13007) ^ 9 *
        (2 * 13007 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13007

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13007
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13007 (61 / 100) 165 (17 / (100 * 13007)) (26 / (10 * 13007))
    (statisticsConstant (paperBound256 13007)) √((42 / 10 : ℝ) / 13007) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13007) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13007 : ℕ))
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
    change (√(tA 13007 * ((165 : ℝ) ^ 2 / (13007 - 2))) *
      √((42 / 10 : ℝ) / 13007) * energyCoefficient18 13007) ^ 18 *
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
    exp (-(13007 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13007 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13007 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13007

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13007
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13007) : Set (Matrix (Fin (mA 13007)) (Fin 13007) ℝ) :=
  {X | ∀ g : Fin (Js 13007),
    17 / (100 * (13007 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13007 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13007) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13007),
      {X | 17 / (100 * (13007 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13007 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13007} (hw : windowW wr) :
    (gaussMat (mA 13007) 13007 (2 / (13007 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13007,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13007 : ℝ)) ∨
      42 / (10 * (13007 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13007) : Set (Matrix (Fin (mA 13007)) (Fin 13007) ℝ) :=
  (Eop 13007 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13007))

theorem tableFirstEvent_measurable (wr : WRet 13007) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13007} (hw : windowW wr) :
    (gaussMat (mA 13007) 13007 (2 / (13007 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13007)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13007) : Set (AHid 13007) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13007) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13007} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13007) 13007 (2 / (13007 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13007) (mA 13007) (tA 13007))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13007)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13007)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13007)) := (hvar g).1
  have hmax (g : Fin (Js 13007)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13007) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13007)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13007) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13007))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13007)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13007) (mA 13007) (tA 13007)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13007) :
    (nuA 13007).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13007

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13007
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13007 × AHid 13007) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13007)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13007) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13007)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13007)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13007)) :
    (retDist (paperCentres 13007)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13007

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13007 :
    BstLean.Part262.ActualRootCertificate 13007 BstLean.Part266.agent13007.root where
  dimension := by norm_num
  table_payment := Row13007.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13007.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13007.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13008
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13008 : ℝ) *
      √(tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13008 : ℝ) ^ 24 = (13008 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) ^ 24 =
      (tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13008 ≤ (2 * 13008 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) * √((42 / 10 : ℝ) / 13008) *
      energyCoefficient18 13008) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) ^ 18 =
      (tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13008) ^ 18 = ((42 / 10 : ℝ) / 13008) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13008) ^ 9 *
        (2 * 13008 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13008

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13008
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13008 (61 / 100) 165 (17 / (100 * 13008)) (26 / (10 * 13008))
    (statisticsConstant (paperBound256 13008)) √((42 / 10 : ℝ) / 13008) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13008) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13008 : ℕ))
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
    change (√(tA 13008 * ((165 : ℝ) ^ 2 / (13008 - 2))) *
      √((42 / 10 : ℝ) / 13008) * energyCoefficient18 13008) ^ 18 *
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
    exp (-(13008 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13008 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13008 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13008

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13008
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13008) : Set (Matrix (Fin (mA 13008)) (Fin 13008) ℝ) :=
  {X | ∀ g : Fin (Js 13008),
    17 / (100 * (13008 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13008 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13008) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13008),
      {X | 17 / (100 * (13008 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13008 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13008} (hw : windowW wr) :
    (gaussMat (mA 13008) 13008 (2 / (13008 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13008,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13008 : ℝ)) ∨
      42 / (10 * (13008 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13008) : Set (Matrix (Fin (mA 13008)) (Fin 13008) ℝ) :=
  (Eop 13008 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13008))

theorem tableFirstEvent_measurable (wr : WRet 13008) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13008} (hw : windowW wr) :
    (gaussMat (mA 13008) 13008 (2 / (13008 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13008)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13008) : Set (AHid 13008) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13008) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13008} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13008) 13008 (2 / (13008 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13008) (mA 13008) (tA 13008))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13008)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13008)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13008)) := (hvar g).1
  have hmax (g : Fin (Js 13008)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13008) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13008)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13008) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13008))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13008)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13008) (mA 13008) (tA 13008)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13008) :
    (nuA 13008).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13008

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13008
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13008 × AHid 13008) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13008)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13008) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13008)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13008)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13008)) :
    (retDist (paperCentres 13008)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13008

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13008 :
    BstLean.Part262.ActualRootCertificate 13008 BstLean.Part266.agent13008.root where
  dimension := by norm_num
  table_payment := Row13008.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13008.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13008.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13009
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13009 : ℝ) *
      √(tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13009 : ℝ) ^ 24 = (13009 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) ^ 24 =
      (tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13009 ≤ (2 * 13009 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) * √((42 / 10 : ℝ) / 13009) *
      energyCoefficient18 13009) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) ^ 18 =
      (tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13009) ^ 18 = ((42 / 10 : ℝ) / 13009) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13009) ^ 9 *
        (2 * 13009 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13009

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13009
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13009 (61 / 100) 165 (17 / (100 * 13009)) (26 / (10 * 13009))
    (statisticsConstant (paperBound256 13009)) √((42 / 10 : ℝ) / 13009) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13009) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13009 : ℕ))
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
    change (√(tA 13009 * ((165 : ℝ) ^ 2 / (13009 - 2))) *
      √((42 / 10 : ℝ) / 13009) * energyCoefficient18 13009) ^ 18 *
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
    exp (-(13009 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13009 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13009 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13009

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13009
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13009) : Set (Matrix (Fin (mA 13009)) (Fin 13009) ℝ) :=
  {X | ∀ g : Fin (Js 13009),
    17 / (100 * (13009 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13009 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13009) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13009),
      {X | 17 / (100 * (13009 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13009 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13009} (hw : windowW wr) :
    (gaussMat (mA 13009) 13009 (2 / (13009 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13009,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13009 : ℝ)) ∨
      42 / (10 * (13009 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13009) : Set (Matrix (Fin (mA 13009)) (Fin 13009) ℝ) :=
  (Eop 13009 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13009))

theorem tableFirstEvent_measurable (wr : WRet 13009) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13009} (hw : windowW wr) :
    (gaussMat (mA 13009) 13009 (2 / (13009 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13009)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13009) : Set (AHid 13009) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13009) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13009} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13009) 13009 (2 / (13009 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13009) (mA 13009) (tA 13009))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13009)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13009)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13009)) := (hvar g).1
  have hmax (g : Fin (Js 13009)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13009) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13009)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13009) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13009))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13009)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13009) (mA 13009) (tA 13009)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13009) :
    (nuA 13009).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13009

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13009
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13009 × AHid 13009) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13009)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13009) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13009)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13009)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13009)) :
    (retDist (paperCentres 13009)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13009

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13009 :
    BstLean.Part262.ActualRootCertificate 13009 BstLean.Part266.agent13009.root where
  dimension := by norm_num
  table_payment := Row13009.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13009.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13009.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13010
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13010 : ℝ) *
      √(tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13010 : ℝ) ^ 24 = (13010 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) ^ 24 =
      (tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13010 ≤ (2 * 13010 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) * √((42 / 10 : ℝ) / 13010) *
      energyCoefficient18 13010) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) ^ 18 =
      (tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13010) ^ 18 = ((42 / 10 : ℝ) / 13010) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13010) ^ 9 *
        (2 * 13010 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13010

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13010
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13010 (61 / 100) 165 (17 / (100 * 13010)) (26 / (10 * 13010))
    (statisticsConstant (paperBound256 13010)) √((42 / 10 : ℝ) / 13010) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13010) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13010 : ℕ))
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
    change (√(tA 13010 * ((165 : ℝ) ^ 2 / (13010 - 2))) *
      √((42 / 10 : ℝ) / 13010) * energyCoefficient18 13010) ^ 18 *
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
    exp (-(13010 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13010 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13010 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13010

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13010
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13010) : Set (Matrix (Fin (mA 13010)) (Fin 13010) ℝ) :=
  {X | ∀ g : Fin (Js 13010),
    17 / (100 * (13010 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13010 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13010) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13010),
      {X | 17 / (100 * (13010 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13010 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13010} (hw : windowW wr) :
    (gaussMat (mA 13010) 13010 (2 / (13010 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13010,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13010 : ℝ)) ∨
      42 / (10 * (13010 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13010) : Set (Matrix (Fin (mA 13010)) (Fin 13010) ℝ) :=
  (Eop 13010 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13010))

theorem tableFirstEvent_measurable (wr : WRet 13010) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13010} (hw : windowW wr) :
    (gaussMat (mA 13010) 13010 (2 / (13010 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13010)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13010) : Set (AHid 13010) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13010) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13010} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13010) 13010 (2 / (13010 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13010) (mA 13010) (tA 13010))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13010)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13010)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13010)) := (hvar g).1
  have hmax (g : Fin (Js 13010)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13010) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13010)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13010) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13010))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13010)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13010) (mA 13010) (tA 13010)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13010) :
    (nuA 13010).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13010

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13010
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13010 × AHid 13010) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13010)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13010) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13010)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13010)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13010)) :
    (retDist (paperCentres 13010)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13010

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13010 :
    BstLean.Part262.ActualRootCertificate 13010 BstLean.Part266.agent13010.root where
  dimension := by norm_num
  table_payment := Row13010.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13010.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13010.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13011
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13011 : ℝ) *
      √(tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13011 : ℝ) ^ 24 = (13011 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) ^ 24 =
      (tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13011 ≤ (2 * 13011 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) * √((42 / 10 : ℝ) / 13011) *
      energyCoefficient18 13011) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) ^ 18 =
      (tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13011) ^ 18 = ((42 / 10 : ℝ) / 13011) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13011) ^ 9 *
        (2 * 13011 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13011

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13011
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13011 (61 / 100) 165 (17 / (100 * 13011)) (26 / (10 * 13011))
    (statisticsConstant (paperBound256 13011)) √((42 / 10 : ℝ) / 13011) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13011) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13011 : ℕ))
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
    change (√(tA 13011 * ((165 : ℝ) ^ 2 / (13011 - 2))) *
      √((42 / 10 : ℝ) / 13011) * energyCoefficient18 13011) ^ 18 *
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
    exp (-(13011 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13011 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13011 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13011

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13011
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13011) : Set (Matrix (Fin (mA 13011)) (Fin 13011) ℝ) :=
  {X | ∀ g : Fin (Js 13011),
    17 / (100 * (13011 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13011 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13011) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13011),
      {X | 17 / (100 * (13011 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13011 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13011} (hw : windowW wr) :
    (gaussMat (mA 13011) 13011 (2 / (13011 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13011,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13011 : ℝ)) ∨
      42 / (10 * (13011 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13011) : Set (Matrix (Fin (mA 13011)) (Fin 13011) ℝ) :=
  (Eop 13011 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13011))

theorem tableFirstEvent_measurable (wr : WRet 13011) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13011} (hw : windowW wr) :
    (gaussMat (mA 13011) 13011 (2 / (13011 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13011)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13011) : Set (AHid 13011) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13011) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13011} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13011) 13011 (2 / (13011 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13011) (mA 13011) (tA 13011))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13011)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13011)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13011)) := (hvar g).1
  have hmax (g : Fin (Js 13011)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13011) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13011)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13011) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13011))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13011)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13011) (mA 13011) (tA 13011)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13011) :
    (nuA 13011).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13011

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13011
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13011 × AHid 13011) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13011)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13011) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13011)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13011)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13011)) :
    (retDist (paperCentres 13011)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13011

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13011 :
    BstLean.Part262.ActualRootCertificate 13011 BstLean.Part266.agent13011.root where
  dimension := by norm_num
  table_payment := Row13011.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13011.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13011.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13012
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13012 : ℝ) *
      √(tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13012 : ℝ) ^ 24 = (13012 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) ^ 24 =
      (tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13012 ≤ (2 * 13012 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) * √((42 / 10 : ℝ) / 13012) *
      energyCoefficient18 13012) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) ^ 18 =
      (tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13012) ^ 18 = ((42 / 10 : ℝ) / 13012) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13012) ^ 9 *
        (2 * 13012 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13012

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13012
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13012 (61 / 100) 165 (17 / (100 * 13012)) (26 / (10 * 13012))
    (statisticsConstant (paperBound256 13012)) √((42 / 10 : ℝ) / 13012) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13012) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13012 : ℕ))
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
    change (√(tA 13012 * ((165 : ℝ) ^ 2 / (13012 - 2))) *
      √((42 / 10 : ℝ) / 13012) * energyCoefficient18 13012) ^ 18 *
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
    exp (-(13012 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13012 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13012 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13012

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13012
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13012) : Set (Matrix (Fin (mA 13012)) (Fin 13012) ℝ) :=
  {X | ∀ g : Fin (Js 13012),
    17 / (100 * (13012 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13012 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13012) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13012),
      {X | 17 / (100 * (13012 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13012 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13012} (hw : windowW wr) :
    (gaussMat (mA 13012) 13012 (2 / (13012 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13012,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13012 : ℝ)) ∨
      42 / (10 * (13012 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13012) : Set (Matrix (Fin (mA 13012)) (Fin 13012) ℝ) :=
  (Eop 13012 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13012))

theorem tableFirstEvent_measurable (wr : WRet 13012) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13012} (hw : windowW wr) :
    (gaussMat (mA 13012) 13012 (2 / (13012 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13012)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13012) : Set (AHid 13012) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13012) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13012} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13012) 13012 (2 / (13012 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13012) (mA 13012) (tA 13012))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13012)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13012)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13012)) := (hvar g).1
  have hmax (g : Fin (Js 13012)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13012) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13012)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13012) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13012))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13012)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13012) (mA 13012) (tA 13012)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13012) :
    (nuA 13012).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13012

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13012
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13012 × AHid 13012) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13012)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13012) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13012)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13012)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13012)) :
    (retDist (paperCentres 13012)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13012

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13012 :
    BstLean.Part262.ActualRootCertificate 13012 BstLean.Part266.agent13012.root where
  dimension := by norm_num
  table_payment := Row13012.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13012.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13012.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13013
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13013 : ℝ) *
      √(tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13013 : ℝ) ^ 24 = (13013 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) ^ 24 =
      (tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13013 ≤ (2 * 13013 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) * √((42 / 10 : ℝ) / 13013) *
      energyCoefficient18 13013) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) ^ 18 =
      (tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13013) ^ 18 = ((42 / 10 : ℝ) / 13013) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13013) ^ 9 *
        (2 * 13013 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13013

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13013
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13013 (61 / 100) 165 (17 / (100 * 13013)) (26 / (10 * 13013))
    (statisticsConstant (paperBound256 13013)) √((42 / 10 : ℝ) / 13013) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13013) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13013 : ℕ))
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
    change (√(tA 13013 * ((165 : ℝ) ^ 2 / (13013 - 2))) *
      √((42 / 10 : ℝ) / 13013) * energyCoefficient18 13013) ^ 18 *
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
    exp (-(13013 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13013 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13013 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13013

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13013
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13013) : Set (Matrix (Fin (mA 13013)) (Fin 13013) ℝ) :=
  {X | ∀ g : Fin (Js 13013),
    17 / (100 * (13013 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13013 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13013) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13013),
      {X | 17 / (100 * (13013 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13013 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13013} (hw : windowW wr) :
    (gaussMat (mA 13013) 13013 (2 / (13013 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13013,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13013 : ℝ)) ∨
      42 / (10 * (13013 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13013) : Set (Matrix (Fin (mA 13013)) (Fin 13013) ℝ) :=
  (Eop 13013 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13013))

theorem tableFirstEvent_measurable (wr : WRet 13013) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13013} (hw : windowW wr) :
    (gaussMat (mA 13013) 13013 (2 / (13013 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13013)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13013) : Set (AHid 13013) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13013) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13013} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13013) 13013 (2 / (13013 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13013) (mA 13013) (tA 13013))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13013)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13013)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13013)) := (hvar g).1
  have hmax (g : Fin (Js 13013)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13013) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13013)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13013) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13013))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13013)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13013) (mA 13013) (tA 13013)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13013) :
    (nuA 13013).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13013

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13013
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13013 × AHid 13013) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13013)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13013) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13013)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13013)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13013)) :
    (retDist (paperCentres 13013)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13013

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13013 :
    BstLean.Part262.ActualRootCertificate 13013 BstLean.Part266.agent13013.root where
  dimension := by norm_num
  table_payment := Row13013.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13013.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13013.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13014
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13014 : ℝ) *
      √(tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13014 : ℝ) ^ 24 = (13014 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) ^ 24 =
      (tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13014 ≤ (2 * 13014 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) * √((42 / 10 : ℝ) / 13014) *
      energyCoefficient18 13014) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) ^ 18 =
      (tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13014) ^ 18 = ((42 / 10 : ℝ) / 13014) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13014) ^ 9 *
        (2 * 13014 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13014

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13014
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13014 (61 / 100) 165 (17 / (100 * 13014)) (26 / (10 * 13014))
    (statisticsConstant (paperBound256 13014)) √((42 / 10 : ℝ) / 13014) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13014) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13014 : ℕ))
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
    change (√(tA 13014 * ((165 : ℝ) ^ 2 / (13014 - 2))) *
      √((42 / 10 : ℝ) / 13014) * energyCoefficient18 13014) ^ 18 *
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
    exp (-(13014 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13014 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13014 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13014

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13014
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13014) : Set (Matrix (Fin (mA 13014)) (Fin 13014) ℝ) :=
  {X | ∀ g : Fin (Js 13014),
    17 / (100 * (13014 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13014 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13014) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13014),
      {X | 17 / (100 * (13014 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13014 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13014} (hw : windowW wr) :
    (gaussMat (mA 13014) 13014 (2 / (13014 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13014,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13014 : ℝ)) ∨
      42 / (10 * (13014 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13014) : Set (Matrix (Fin (mA 13014)) (Fin 13014) ℝ) :=
  (Eop 13014 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13014))

theorem tableFirstEvent_measurable (wr : WRet 13014) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13014} (hw : windowW wr) :
    (gaussMat (mA 13014) 13014 (2 / (13014 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13014)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13014) : Set (AHid 13014) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13014) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13014} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13014) 13014 (2 / (13014 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13014) (mA 13014) (tA 13014))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13014)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13014)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13014)) := (hvar g).1
  have hmax (g : Fin (Js 13014)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13014) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13014)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13014) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13014))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13014)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13014) (mA 13014) (tA 13014)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13014) :
    (nuA 13014).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13014

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13014
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13014 × AHid 13014) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13014)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13014) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13014)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13014)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13014)) :
    (retDist (paperCentres 13014)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13014

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13014 :
    BstLean.Part262.ActualRootCertificate 13014 BstLean.Part266.agent13014.root where
  dimension := by norm_num
  table_payment := Row13014.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13014.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13014.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13015
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13015 : ℝ) *
      √(tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13015 : ℝ) ^ 24 = (13015 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) ^ 24 =
      (tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13015 ≤ (2 * 13015 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) * √((42 / 10 : ℝ) / 13015) *
      energyCoefficient18 13015) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) ^ 18 =
      (tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13015) ^ 18 = ((42 / 10 : ℝ) / 13015) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13015) ^ 9 *
        (2 * 13015 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13015

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13015
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13015 (61 / 100) 165 (17 / (100 * 13015)) (26 / (10 * 13015))
    (statisticsConstant (paperBound256 13015)) √((42 / 10 : ℝ) / 13015) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13015) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13015 : ℕ))
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
    change (√(tA 13015 * ((165 : ℝ) ^ 2 / (13015 - 2))) *
      √((42 / 10 : ℝ) / 13015) * energyCoefficient18 13015) ^ 18 *
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
    exp (-(13015 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13015 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13015 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13015

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13015
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13015) : Set (Matrix (Fin (mA 13015)) (Fin 13015) ℝ) :=
  {X | ∀ g : Fin (Js 13015),
    17 / (100 * (13015 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13015 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13015) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13015),
      {X | 17 / (100 * (13015 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13015 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13015} (hw : windowW wr) :
    (gaussMat (mA 13015) 13015 (2 / (13015 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13015,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13015 : ℝ)) ∨
      42 / (10 * (13015 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13015) : Set (Matrix (Fin (mA 13015)) (Fin 13015) ℝ) :=
  (Eop 13015 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13015))

theorem tableFirstEvent_measurable (wr : WRet 13015) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13015} (hw : windowW wr) :
    (gaussMat (mA 13015) 13015 (2 / (13015 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13015)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13015) : Set (AHid 13015) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13015) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13015} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13015) 13015 (2 / (13015 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13015) (mA 13015) (tA 13015))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13015)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13015)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13015)) := (hvar g).1
  have hmax (g : Fin (Js 13015)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13015) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13015)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13015) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13015))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13015)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13015) (mA 13015) (tA 13015)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13015) :
    (nuA 13015).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13015

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13015
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13015 × AHid 13015) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13015)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13015) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13015)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13015)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13015)) :
    (retDist (paperCentres 13015)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13015

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13015 :
    BstLean.Part262.ActualRootCertificate 13015 BstLean.Part266.agent13015.root where
  dimension := by norm_num
  table_payment := Row13015.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13015.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13015.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13016
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13016 : ℝ) *
      √(tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13016 : ℝ) ^ 24 = (13016 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) ^ 24 =
      (tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13016 ≤ (2 * 13016 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) * √((42 / 10 : ℝ) / 13016) *
      energyCoefficient18 13016) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) ^ 18 =
      (tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13016) ^ 18 = ((42 / 10 : ℝ) / 13016) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13016) ^ 9 *
        (2 * 13016 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13016

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13016
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13016 (61 / 100) 165 (17 / (100 * 13016)) (26 / (10 * 13016))
    (statisticsConstant (paperBound256 13016)) √((42 / 10 : ℝ) / 13016) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13016) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13016 : ℕ))
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
    change (√(tA 13016 * ((165 : ℝ) ^ 2 / (13016 - 2))) *
      √((42 / 10 : ℝ) / 13016) * energyCoefficient18 13016) ^ 18 *
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
    exp (-(13016 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13016 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13016 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13016

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13016
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13016) : Set (Matrix (Fin (mA 13016)) (Fin 13016) ℝ) :=
  {X | ∀ g : Fin (Js 13016),
    17 / (100 * (13016 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13016 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13016) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13016),
      {X | 17 / (100 * (13016 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13016 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13016} (hw : windowW wr) :
    (gaussMat (mA 13016) 13016 (2 / (13016 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13016,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13016 : ℝ)) ∨
      42 / (10 * (13016 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13016) : Set (Matrix (Fin (mA 13016)) (Fin 13016) ℝ) :=
  (Eop 13016 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13016))

theorem tableFirstEvent_measurable (wr : WRet 13016) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13016} (hw : windowW wr) :
    (gaussMat (mA 13016) 13016 (2 / (13016 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13016)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13016) : Set (AHid 13016) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13016) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13016} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13016) 13016 (2 / (13016 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13016) (mA 13016) (tA 13016))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13016)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13016)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13016)) := (hvar g).1
  have hmax (g : Fin (Js 13016)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13016) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13016)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13016) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13016))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13016)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13016) (mA 13016) (tA 13016)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13016) :
    (nuA 13016).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13016

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13016
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13016 × AHid 13016) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13016)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13016) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13016)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13016)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13016)) :
    (retDist (paperCentres 13016)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13016

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13016 :
    BstLean.Part262.ActualRootCertificate 13016 BstLean.Part266.agent13016.root where
  dimension := by norm_num
  table_payment := Row13016.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13016.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13016.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13017
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13017 : ℝ) *
      √(tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13017 : ℝ) ^ 24 = (13017 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) ^ 24 =
      (tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13017 ≤ (2 * 13017 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) * √((42 / 10 : ℝ) / 13017) *
      energyCoefficient18 13017) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) ^ 18 =
      (tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13017) ^ 18 = ((42 / 10 : ℝ) / 13017) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13017) ^ 9 *
        (2 * 13017 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13017

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13017
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13017 (61 / 100) 165 (17 / (100 * 13017)) (26 / (10 * 13017))
    (statisticsConstant (paperBound256 13017)) √((42 / 10 : ℝ) / 13017) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13017) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13017 : ℕ))
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
    change (√(tA 13017 * ((165 : ℝ) ^ 2 / (13017 - 2))) *
      √((42 / 10 : ℝ) / 13017) * energyCoefficient18 13017) ^ 18 *
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
    exp (-(13017 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13017 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13017 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13017

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13017
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13017) : Set (Matrix (Fin (mA 13017)) (Fin 13017) ℝ) :=
  {X | ∀ g : Fin (Js 13017),
    17 / (100 * (13017 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13017 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13017) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13017),
      {X | 17 / (100 * (13017 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13017 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13017} (hw : windowW wr) :
    (gaussMat (mA 13017) 13017 (2 / (13017 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13017,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13017 : ℝ)) ∨
      42 / (10 * (13017 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13017) : Set (Matrix (Fin (mA 13017)) (Fin 13017) ℝ) :=
  (Eop 13017 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13017))

theorem tableFirstEvent_measurable (wr : WRet 13017) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13017} (hw : windowW wr) :
    (gaussMat (mA 13017) 13017 (2 / (13017 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13017)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13017) : Set (AHid 13017) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13017) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13017} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13017) 13017 (2 / (13017 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13017) (mA 13017) (tA 13017))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13017)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13017)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13017)) := (hvar g).1
  have hmax (g : Fin (Js 13017)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13017) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13017)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13017) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13017))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13017)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13017) (mA 13017) (tA 13017)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13017) :
    (nuA 13017).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13017

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13017
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13017 × AHid 13017) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13017)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13017) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13017)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13017)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13017)) :
    (retDist (paperCentres 13017)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13017

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13017 :
    BstLean.Part262.ActualRootCertificate 13017 BstLean.Part266.agent13017.root where
  dimension := by norm_num
  table_payment := Row13017.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13017.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13017.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13018
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13018 : ℝ) *
      √(tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13018 : ℝ) ^ 24 = (13018 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) ^ 24 =
      (tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13018 ≤ (2 * 13018 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) * √((42 / 10 : ℝ) / 13018) *
      energyCoefficient18 13018) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) ^ 18 =
      (tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13018) ^ 18 = ((42 / 10 : ℝ) / 13018) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13018) ^ 9 *
        (2 * 13018 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13018

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13018
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13018 (61 / 100) 165 (17 / (100 * 13018)) (26 / (10 * 13018))
    (statisticsConstant (paperBound256 13018)) √((42 / 10 : ℝ) / 13018) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13018) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13018 : ℕ))
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
    change (√(tA 13018 * ((165 : ℝ) ^ 2 / (13018 - 2))) *
      √((42 / 10 : ℝ) / 13018) * energyCoefficient18 13018) ^ 18 *
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
    exp (-(13018 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13018 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13018 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13018

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13018
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13018) : Set (Matrix (Fin (mA 13018)) (Fin 13018) ℝ) :=
  {X | ∀ g : Fin (Js 13018),
    17 / (100 * (13018 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13018 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13018) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13018),
      {X | 17 / (100 * (13018 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13018 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13018} (hw : windowW wr) :
    (gaussMat (mA 13018) 13018 (2 / (13018 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13018,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13018 : ℝ)) ∨
      42 / (10 * (13018 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13018) : Set (Matrix (Fin (mA 13018)) (Fin 13018) ℝ) :=
  (Eop 13018 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13018))

theorem tableFirstEvent_measurable (wr : WRet 13018) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13018} (hw : windowW wr) :
    (gaussMat (mA 13018) 13018 (2 / (13018 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13018)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13018) : Set (AHid 13018) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13018) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13018} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13018) 13018 (2 / (13018 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13018) (mA 13018) (tA 13018))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13018)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13018)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13018)) := (hvar g).1
  have hmax (g : Fin (Js 13018)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13018) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13018)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13018) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13018))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13018)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13018) (mA 13018) (tA 13018)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13018) :
    (nuA 13018).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13018

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13018
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13018 × AHid 13018) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13018)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13018) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13018)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13018)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13018)) :
    (retDist (paperCentres 13018)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13018

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13018 :
    BstLean.Part262.ActualRootCertificate 13018 BstLean.Part266.agent13018.root where
  dimension := by norm_num
  table_payment := Row13018.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13018.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13018.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13019
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13019 : ℝ) *
      √(tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13019 : ℝ) ^ 24 = (13019 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) ^ 24 =
      (tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13019 ≤ (2 * 13019 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) * √((42 / 10 : ℝ) / 13019) *
      energyCoefficient18 13019) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) ^ 18 =
      (tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13019) ^ 18 = ((42 / 10 : ℝ) / 13019) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13019) ^ 9 *
        (2 * 13019 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13019

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13019
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13019 (61 / 100) 165 (17 / (100 * 13019)) (26 / (10 * 13019))
    (statisticsConstant (paperBound256 13019)) √((42 / 10 : ℝ) / 13019) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13019) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13019 : ℕ))
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
    change (√(tA 13019 * ((165 : ℝ) ^ 2 / (13019 - 2))) *
      √((42 / 10 : ℝ) / 13019) * energyCoefficient18 13019) ^ 18 *
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
    exp (-(13019 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13019 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13019 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13019

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13019
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13019) : Set (Matrix (Fin (mA 13019)) (Fin 13019) ℝ) :=
  {X | ∀ g : Fin (Js 13019),
    17 / (100 * (13019 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13019 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13019) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13019),
      {X | 17 / (100 * (13019 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13019 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13019} (hw : windowW wr) :
    (gaussMat (mA 13019) 13019 (2 / (13019 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13019,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13019 : ℝ)) ∨
      42 / (10 * (13019 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13019) : Set (Matrix (Fin (mA 13019)) (Fin 13019) ℝ) :=
  (Eop 13019 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13019))

theorem tableFirstEvent_measurable (wr : WRet 13019) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13019} (hw : windowW wr) :
    (gaussMat (mA 13019) 13019 (2 / (13019 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13019)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13019) : Set (AHid 13019) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13019) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13019} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13019) 13019 (2 / (13019 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13019) (mA 13019) (tA 13019))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13019)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13019)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13019)) := (hvar g).1
  have hmax (g : Fin (Js 13019)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13019) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13019)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13019) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13019))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13019)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13019) (mA 13019) (tA 13019)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13019) :
    (nuA 13019).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13019

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13019
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13019 × AHid 13019) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13019)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13019) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13019)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13019)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13019)) :
    (retDist (paperCentres 13019)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13019

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13019 :
    BstLean.Part262.ActualRootCertificate 13019 BstLean.Part266.agent13019.root where
  dimension := by norm_num
  table_payment := Row13019.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13019.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13019.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13020
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13020 : ℝ) *
      √(tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13020 : ℝ) ^ 24 = (13020 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) ^ 24 =
      (tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13020 ≤ (2 * 13020 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) * √((42 / 10 : ℝ) / 13020) *
      energyCoefficient18 13020) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) ^ 18 =
      (tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13020) ^ 18 = ((42 / 10 : ℝ) / 13020) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13020) ^ 9 *
        (2 * 13020 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13020

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13020
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13020 (61 / 100) 165 (17 / (100 * 13020)) (26 / (10 * 13020))
    (statisticsConstant (paperBound256 13020)) √((42 / 10 : ℝ) / 13020) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13020) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13020 : ℕ))
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
    change (√(tA 13020 * ((165 : ℝ) ^ 2 / (13020 - 2))) *
      √((42 / 10 : ℝ) / 13020) * energyCoefficient18 13020) ^ 18 *
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
    exp (-(13020 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13020 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13020 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13020

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13020
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13020) : Set (Matrix (Fin (mA 13020)) (Fin 13020) ℝ) :=
  {X | ∀ g : Fin (Js 13020),
    17 / (100 * (13020 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13020 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13020) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13020),
      {X | 17 / (100 * (13020 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13020 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13020} (hw : windowW wr) :
    (gaussMat (mA 13020) 13020 (2 / (13020 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13020,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13020 : ℝ)) ∨
      42 / (10 * (13020 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13020) : Set (Matrix (Fin (mA 13020)) (Fin 13020) ℝ) :=
  (Eop 13020 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13020))

theorem tableFirstEvent_measurable (wr : WRet 13020) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13020} (hw : windowW wr) :
    (gaussMat (mA 13020) 13020 (2 / (13020 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13020)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13020) : Set (AHid 13020) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13020) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13020} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13020) 13020 (2 / (13020 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13020) (mA 13020) (tA 13020))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13020)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13020)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13020)) := (hvar g).1
  have hmax (g : Fin (Js 13020)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13020) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13020)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13020) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13020))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13020)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13020) (mA 13020) (tA 13020)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13020) :
    (nuA 13020).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13020

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13020
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13020 × AHid 13020) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13020)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13020) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13020)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13020)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13020)) :
    (retDist (paperCentres 13020)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13020

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13020 :
    BstLean.Part262.ActualRootCertificate 13020 BstLean.Part266.agent13020.root where
  dimension := by norm_num
  table_payment := Row13020.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13020.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13020.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13021
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13021 : ℝ) *
      √(tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13021 : ℝ) ^ 24 = (13021 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) ^ 24 =
      (tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13021 ≤ (2 * 13021 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) * √((42 / 10 : ℝ) / 13021) *
      energyCoefficient18 13021) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) ^ 18 =
      (tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13021) ^ 18 = ((42 / 10 : ℝ) / 13021) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13021) ^ 9 *
        (2 * 13021 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13021

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13021
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13021 (61 / 100) 165 (17 / (100 * 13021)) (26 / (10 * 13021))
    (statisticsConstant (paperBound256 13021)) √((42 / 10 : ℝ) / 13021) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13021) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13021 : ℕ))
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
    change (√(tA 13021 * ((165 : ℝ) ^ 2 / (13021 - 2))) *
      √((42 / 10 : ℝ) / 13021) * energyCoefficient18 13021) ^ 18 *
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
    exp (-(13021 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13021 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13021 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13021

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13021
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13021) : Set (Matrix (Fin (mA 13021)) (Fin 13021) ℝ) :=
  {X | ∀ g : Fin (Js 13021),
    17 / (100 * (13021 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13021 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13021) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13021),
      {X | 17 / (100 * (13021 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13021 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13021} (hw : windowW wr) :
    (gaussMat (mA 13021) 13021 (2 / (13021 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13021,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13021 : ℝ)) ∨
      42 / (10 * (13021 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13021) : Set (Matrix (Fin (mA 13021)) (Fin 13021) ℝ) :=
  (Eop 13021 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13021))

theorem tableFirstEvent_measurable (wr : WRet 13021) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13021} (hw : windowW wr) :
    (gaussMat (mA 13021) 13021 (2 / (13021 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13021)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13021) : Set (AHid 13021) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13021) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13021} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13021) 13021 (2 / (13021 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13021) (mA 13021) (tA 13021))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13021)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13021)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13021)) := (hvar g).1
  have hmax (g : Fin (Js 13021)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13021) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13021)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13021) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13021))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13021)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13021) (mA 13021) (tA 13021)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13021) :
    (nuA 13021).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13021

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13021
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13021 × AHid 13021) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13021)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13021) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13021)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13021)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13021)) :
    (retDist (paperCentres 13021)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13021

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13021 :
    BstLean.Part262.ActualRootCertificate 13021 BstLean.Part266.agent13021.root where
  dimension := by norm_num
  table_payment := Row13021.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13021.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13021.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13022
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13022 : ℝ) *
      √(tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13022 : ℝ) ^ 24 = (13022 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) ^ 24 =
      (tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13022 ≤ (2 * 13022 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) * √((42 / 10 : ℝ) / 13022) *
      energyCoefficient18 13022) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) ^ 18 =
      (tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13022) ^ 18 = ((42 / 10 : ℝ) / 13022) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13022) ^ 9 *
        (2 * 13022 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13022

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13022
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13022 (61 / 100) 165 (17 / (100 * 13022)) (26 / (10 * 13022))
    (statisticsConstant (paperBound256 13022)) √((42 / 10 : ℝ) / 13022) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13022) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13022 : ℕ))
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
    change (√(tA 13022 * ((165 : ℝ) ^ 2 / (13022 - 2))) *
      √((42 / 10 : ℝ) / 13022) * energyCoefficient18 13022) ^ 18 *
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
    exp (-(13022 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13022 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13022 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13022

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13022
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13022) : Set (Matrix (Fin (mA 13022)) (Fin 13022) ℝ) :=
  {X | ∀ g : Fin (Js 13022),
    17 / (100 * (13022 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13022 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13022) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13022),
      {X | 17 / (100 * (13022 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13022 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13022} (hw : windowW wr) :
    (gaussMat (mA 13022) 13022 (2 / (13022 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13022,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13022 : ℝ)) ∨
      42 / (10 * (13022 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13022) : Set (Matrix (Fin (mA 13022)) (Fin 13022) ℝ) :=
  (Eop 13022 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13022))

theorem tableFirstEvent_measurable (wr : WRet 13022) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13022} (hw : windowW wr) :
    (gaussMat (mA 13022) 13022 (2 / (13022 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13022)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13022) : Set (AHid 13022) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13022) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13022} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13022) 13022 (2 / (13022 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13022) (mA 13022) (tA 13022))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13022)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13022)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13022)) := (hvar g).1
  have hmax (g : Fin (Js 13022)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13022) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13022)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13022) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13022))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13022)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13022) (mA 13022) (tA 13022)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13022) :
    (nuA 13022).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13022

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13022
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13022 × AHid 13022) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13022)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13022) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13022)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13022)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13022)) :
    (retDist (paperCentres 13022)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13022

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13022 :
    BstLean.Part262.ActualRootCertificate 13022 BstLean.Part266.agent13022.root where
  dimension := by norm_num
  table_payment := Row13022.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13022.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13022.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13023
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13023 : ℝ) *
      √(tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13023 : ℝ) ^ 24 = (13023 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) ^ 24 =
      (tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13023 ≤ (2 * 13023 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) * √((42 / 10 : ℝ) / 13023) *
      energyCoefficient18 13023) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) ^ 18 =
      (tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13023) ^ 18 = ((42 / 10 : ℝ) / 13023) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13023) ^ 9 *
        (2 * 13023 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13023

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13023
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13023 (61 / 100) 165 (17 / (100 * 13023)) (26 / (10 * 13023))
    (statisticsConstant (paperBound256 13023)) √((42 / 10 : ℝ) / 13023) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13023) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13023 : ℕ))
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
    change (√(tA 13023 * ((165 : ℝ) ^ 2 / (13023 - 2))) *
      √((42 / 10 : ℝ) / 13023) * energyCoefficient18 13023) ^ 18 *
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
    exp (-(13023 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13023 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13023 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13023

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13023
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13023) : Set (Matrix (Fin (mA 13023)) (Fin 13023) ℝ) :=
  {X | ∀ g : Fin (Js 13023),
    17 / (100 * (13023 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13023 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13023) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13023),
      {X | 17 / (100 * (13023 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13023 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13023} (hw : windowW wr) :
    (gaussMat (mA 13023) 13023 (2 / (13023 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13023,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13023 : ℝ)) ∨
      42 / (10 * (13023 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13023) : Set (Matrix (Fin (mA 13023)) (Fin 13023) ℝ) :=
  (Eop 13023 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13023))

theorem tableFirstEvent_measurable (wr : WRet 13023) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13023} (hw : windowW wr) :
    (gaussMat (mA 13023) 13023 (2 / (13023 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13023)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13023) : Set (AHid 13023) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13023) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13023} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13023) 13023 (2 / (13023 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13023) (mA 13023) (tA 13023))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13023)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13023)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13023)) := (hvar g).1
  have hmax (g : Fin (Js 13023)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13023) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13023)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13023) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13023))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13023)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13023) (mA 13023) (tA 13023)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13023) :
    (nuA 13023).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13023

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13023
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13023 × AHid 13023) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13023)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13023) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13023)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13023)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13023)) :
    (retDist (paperCentres 13023)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13023

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13023 :
    BstLean.Part262.ActualRootCertificate 13023 BstLean.Part266.agent13023.root where
  dimension := by norm_num
  table_payment := Row13023.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13023.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13023.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13024
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13024 : ℝ) *
      √(tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13024 : ℝ) ^ 24 = (13024 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) ^ 24 =
      (tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13024 ≤ (2 * 13024 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) * √((42 / 10 : ℝ) / 13024) *
      energyCoefficient18 13024) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) ^ 18 =
      (tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13024) ^ 18 = ((42 / 10 : ℝ) / 13024) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13024) ^ 9 *
        (2 * 13024 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row13024

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13024
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13024 (61 / 100) 165 (17 / (100 * 13024)) (26 / (10 * 13024))
    (statisticsConstant (paperBound256 13024)) √((42 / 10 : ℝ) / 13024) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13024) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13024 : ℕ))
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
    change (√(tA 13024 * ((165 : ℝ) ^ 2 / (13024 - 2))) *
      √((42 / 10 : ℝ) / 13024) * energyCoefficient18 13024) ^ 18 *
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
    exp (-(13024 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13024 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13024 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13024

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13024
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13024) : Set (Matrix (Fin (mA 13024)) (Fin 13024) ℝ) :=
  {X | ∀ g : Fin (Js 13024),
    17 / (100 * (13024 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13024 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13024) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13024),
      {X | 17 / (100 * (13024 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13024 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13024} (hw : windowW wr) :
    (gaussMat (mA 13024) 13024 (2 / (13024 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13024,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13024 : ℝ)) ∨
      42 / (10 * (13024 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13024) : Set (Matrix (Fin (mA 13024)) (Fin 13024) ℝ) :=
  (Eop 13024 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13024))

theorem tableFirstEvent_measurable (wr : WRet 13024) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13024} (hw : windowW wr) :
    (gaussMat (mA 13024) 13024 (2 / (13024 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13024)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13024) : Set (AHid 13024) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13024) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13024} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13024) 13024 (2 / (13024 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13024) (mA 13024) (tA 13024))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13024)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13024)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 13024)) := (hvar g).1
  have hmax (g : Fin (Js 13024)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13024) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13024)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13024) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 165) (by norm_num : (0 : ℝ) < 17 / (100 * 13024))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13024)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13024) (mA 13024) (tA 13024)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13024) :
    (nuA 13024).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row13024

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13024
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13024 × AHid 13024) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13024)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13024) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13024)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13024)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13024)) :
    (retDist (paperCentres 13024)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13024

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13024 :
    BstLean.Part262.ActualRootCertificate 13024 BstLean.Part266.agent13024.root where
  dimension := by norm_num
  table_payment := Row13024.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13024.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13024.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266
