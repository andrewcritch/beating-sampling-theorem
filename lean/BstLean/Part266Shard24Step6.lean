import BstLean.Part266Shard24Step5


/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12950
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12950 : ℝ) *
      √(tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12950 : ℝ) ^ 24 = (12950 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) ^ 24 =
      (tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12950 ≤ (2 * 12950 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) * √((42 / 10 : ℝ) / 12950) *
      energyCoefficient18 12950) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) ^ 18 =
      (tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12950) ^ 18 = ((42 / 10 : ℝ) / 12950) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12950) ^ 9 *
        (2 * 12950 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12950

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12950
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12950 (61 / 100) 164 (17 / (100 * 12950)) (26 / (10 * 12950))
    (statisticsConstant (paperBound256 12950)) √((42 / 10 : ℝ) / 12950) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12950) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12950 : ℕ))
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
    change (√(tA 12950 * ((164 : ℝ) ^ 2 / (12950 - 2))) *
      √((42 / 10 : ℝ) / 12950) * energyCoefficient18 12950) ^ 18 *
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
    exp (-(12950 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12950 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12950 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12950

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12950
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12950) : Set (Matrix (Fin (mA 12950)) (Fin 12950) ℝ) :=
  {X | ∀ g : Fin (Js 12950),
    17 / (100 * (12950 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12950 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12950) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12950),
      {X | 17 / (100 * (12950 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12950 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12950} (hw : windowW wr) :
    (gaussMat (mA 12950) 12950 (2 / (12950 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12950,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12950 : ℝ)) ∨
      42 / (10 * (12950 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12950) : Set (Matrix (Fin (mA 12950)) (Fin 12950) ℝ) :=
  (Eop 12950 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12950))

theorem tableFirstEvent_measurable (wr : WRet 12950) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12950} (hw : windowW wr) :
    (gaussMat (mA 12950) 12950 (2 / (12950 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12950)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12950) : Set (AHid 12950) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12950) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12950} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12950) 12950 (2 / (12950 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12950) (mA 12950) (tA 12950))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12950)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12950)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12950)) := (hvar g).1
  have hmax (g : Fin (Js 12950)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12950) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12950)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12950) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12950))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12950)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12950) (mA 12950) (tA 12950)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12950) :
    (nuA 12950).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12950

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12950
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12950 × AHid 12950) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12950)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12950) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12950)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12950)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12950)) :
    (retDist (paperCentres 12950)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12950

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12950 :
    BstLean.Part262.ActualRootCertificate 12950 BstLean.Part266.agent12950.root where
  dimension := by norm_num
  table_payment := Row12950.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12950.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12950.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12951
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12951 : ℝ) *
      √(tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12951 : ℝ) ^ 24 = (12951 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) ^ 24 =
      (tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12951 ≤ (2 * 12951 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) * √((42 / 10 : ℝ) / 12951) *
      energyCoefficient18 12951) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) ^ 18 =
      (tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12951) ^ 18 = ((42 / 10 : ℝ) / 12951) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12951) ^ 9 *
        (2 * 12951 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12951

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12951
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12951 (61 / 100) 164 (17 / (100 * 12951)) (26 / (10 * 12951))
    (statisticsConstant (paperBound256 12951)) √((42 / 10 : ℝ) / 12951) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12951) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12951 : ℕ))
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
    change (√(tA 12951 * ((164 : ℝ) ^ 2 / (12951 - 2))) *
      √((42 / 10 : ℝ) / 12951) * energyCoefficient18 12951) ^ 18 *
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
    exp (-(12951 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12951 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12951 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12951

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12951
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12951) : Set (Matrix (Fin (mA 12951)) (Fin 12951) ℝ) :=
  {X | ∀ g : Fin (Js 12951),
    17 / (100 * (12951 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12951 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12951) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12951),
      {X | 17 / (100 * (12951 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12951 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12951} (hw : windowW wr) :
    (gaussMat (mA 12951) 12951 (2 / (12951 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12951,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12951 : ℝ)) ∨
      42 / (10 * (12951 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12951) : Set (Matrix (Fin (mA 12951)) (Fin 12951) ℝ) :=
  (Eop 12951 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12951))

theorem tableFirstEvent_measurable (wr : WRet 12951) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12951} (hw : windowW wr) :
    (gaussMat (mA 12951) 12951 (2 / (12951 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12951)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12951) : Set (AHid 12951) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12951) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12951} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12951) 12951 (2 / (12951 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12951) (mA 12951) (tA 12951))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12951)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12951)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12951)) := (hvar g).1
  have hmax (g : Fin (Js 12951)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12951) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12951)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12951) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12951))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12951)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12951) (mA 12951) (tA 12951)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12951) :
    (nuA 12951).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12951

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12951
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12951 × AHid 12951) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12951)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12951) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12951)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12951)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12951)) :
    (retDist (paperCentres 12951)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12951

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12951 :
    BstLean.Part262.ActualRootCertificate 12951 BstLean.Part266.agent12951.root where
  dimension := by norm_num
  table_payment := Row12951.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12951.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12951.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12952
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12952 : ℝ) *
      √(tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12952 : ℝ) ^ 24 = (12952 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) ^ 24 =
      (tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12952 ≤ (2 * 12952 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) * √((42 / 10 : ℝ) / 12952) *
      energyCoefficient18 12952) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) ^ 18 =
      (tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12952) ^ 18 = ((42 / 10 : ℝ) / 12952) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12952) ^ 9 *
        (2 * 12952 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12952

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12952
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12952 (61 / 100) 164 (17 / (100 * 12952)) (26 / (10 * 12952))
    (statisticsConstant (paperBound256 12952)) √((42 / 10 : ℝ) / 12952) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12952) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12952 : ℕ))
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
    change (√(tA 12952 * ((164 : ℝ) ^ 2 / (12952 - 2))) *
      √((42 / 10 : ℝ) / 12952) * energyCoefficient18 12952) ^ 18 *
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
    exp (-(12952 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12952 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12952 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12952

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12952
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12952) : Set (Matrix (Fin (mA 12952)) (Fin 12952) ℝ) :=
  {X | ∀ g : Fin (Js 12952),
    17 / (100 * (12952 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12952 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12952) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12952),
      {X | 17 / (100 * (12952 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12952 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12952} (hw : windowW wr) :
    (gaussMat (mA 12952) 12952 (2 / (12952 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12952,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12952 : ℝ)) ∨
      42 / (10 * (12952 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12952) : Set (Matrix (Fin (mA 12952)) (Fin 12952) ℝ) :=
  (Eop 12952 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12952))

theorem tableFirstEvent_measurable (wr : WRet 12952) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12952} (hw : windowW wr) :
    (gaussMat (mA 12952) 12952 (2 / (12952 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12952)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12952) : Set (AHid 12952) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12952) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12952} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12952) 12952 (2 / (12952 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12952) (mA 12952) (tA 12952))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12952)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12952)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12952)) := (hvar g).1
  have hmax (g : Fin (Js 12952)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12952) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12952)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12952) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12952))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12952)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12952) (mA 12952) (tA 12952)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12952) :
    (nuA 12952).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12952

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12952
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12952 × AHid 12952) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12952)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12952) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12952)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12952)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12952)) :
    (retDist (paperCentres 12952)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12952

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12952 :
    BstLean.Part262.ActualRootCertificate 12952 BstLean.Part266.agent12952.root where
  dimension := by norm_num
  table_payment := Row12952.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12952.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12952.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12953
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12953 : ℝ) *
      √(tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12953 : ℝ) ^ 24 = (12953 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) ^ 24 =
      (tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12953 ≤ (2 * 12953 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) * √((42 / 10 : ℝ) / 12953) *
      energyCoefficient18 12953) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) ^ 18 =
      (tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12953) ^ 18 = ((42 / 10 : ℝ) / 12953) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12953) ^ 9 *
        (2 * 12953 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12953

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12953
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12953 (61 / 100) 164 (17 / (100 * 12953)) (26 / (10 * 12953))
    (statisticsConstant (paperBound256 12953)) √((42 / 10 : ℝ) / 12953) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12953) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12953 : ℕ))
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
    change (√(tA 12953 * ((164 : ℝ) ^ 2 / (12953 - 2))) *
      √((42 / 10 : ℝ) / 12953) * energyCoefficient18 12953) ^ 18 *
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
    exp (-(12953 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12953 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12953 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12953

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12953
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12953) : Set (Matrix (Fin (mA 12953)) (Fin 12953) ℝ) :=
  {X | ∀ g : Fin (Js 12953),
    17 / (100 * (12953 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12953 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12953) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12953),
      {X | 17 / (100 * (12953 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12953 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12953} (hw : windowW wr) :
    (gaussMat (mA 12953) 12953 (2 / (12953 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12953,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12953 : ℝ)) ∨
      42 / (10 * (12953 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12953) : Set (Matrix (Fin (mA 12953)) (Fin 12953) ℝ) :=
  (Eop 12953 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12953))

theorem tableFirstEvent_measurable (wr : WRet 12953) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12953} (hw : windowW wr) :
    (gaussMat (mA 12953) 12953 (2 / (12953 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12953)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12953) : Set (AHid 12953) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12953) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12953} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12953) 12953 (2 / (12953 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12953) (mA 12953) (tA 12953))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12953)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12953)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12953)) := (hvar g).1
  have hmax (g : Fin (Js 12953)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12953) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12953)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12953) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12953))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12953)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12953) (mA 12953) (tA 12953)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12953) :
    (nuA 12953).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12953

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12953
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12953 × AHid 12953) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12953)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12953) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12953)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12953)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12953)) :
    (retDist (paperCentres 12953)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12953

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12953 :
    BstLean.Part262.ActualRootCertificate 12953 BstLean.Part266.agent12953.root where
  dimension := by norm_num
  table_payment := Row12953.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12953.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12953.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12954
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12954 : ℝ) *
      √(tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12954 : ℝ) ^ 24 = (12954 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) ^ 24 =
      (tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12954 ≤ (2 * 12954 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) * √((42 / 10 : ℝ) / 12954) *
      energyCoefficient18 12954) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) ^ 18 =
      (tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12954) ^ 18 = ((42 / 10 : ℝ) / 12954) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12954) ^ 9 *
        (2 * 12954 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12954

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12954
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12954 (61 / 100) 164 (17 / (100 * 12954)) (26 / (10 * 12954))
    (statisticsConstant (paperBound256 12954)) √((42 / 10 : ℝ) / 12954) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12954) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12954 : ℕ))
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
    change (√(tA 12954 * ((164 : ℝ) ^ 2 / (12954 - 2))) *
      √((42 / 10 : ℝ) / 12954) * energyCoefficient18 12954) ^ 18 *
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
    exp (-(12954 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12954 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12954 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12954

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12954
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12954) : Set (Matrix (Fin (mA 12954)) (Fin 12954) ℝ) :=
  {X | ∀ g : Fin (Js 12954),
    17 / (100 * (12954 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12954 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12954) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12954),
      {X | 17 / (100 * (12954 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12954 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12954} (hw : windowW wr) :
    (gaussMat (mA 12954) 12954 (2 / (12954 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12954,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12954 : ℝ)) ∨
      42 / (10 * (12954 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12954) : Set (Matrix (Fin (mA 12954)) (Fin 12954) ℝ) :=
  (Eop 12954 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12954))

theorem tableFirstEvent_measurable (wr : WRet 12954) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12954} (hw : windowW wr) :
    (gaussMat (mA 12954) 12954 (2 / (12954 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12954)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12954) : Set (AHid 12954) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12954) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12954} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12954) 12954 (2 / (12954 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12954) (mA 12954) (tA 12954))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12954)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12954)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12954)) := (hvar g).1
  have hmax (g : Fin (Js 12954)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12954) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12954)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12954) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12954))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12954)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12954) (mA 12954) (tA 12954)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12954) :
    (nuA 12954).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12954

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12954
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12954 × AHid 12954) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12954)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12954) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12954)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12954)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12954)) :
    (retDist (paperCentres 12954)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12954

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12954 :
    BstLean.Part262.ActualRootCertificate 12954 BstLean.Part266.agent12954.root where
  dimension := by norm_num
  table_payment := Row12954.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12954.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12954.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12955
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12955 : ℝ) *
      √(tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12955 : ℝ) ^ 24 = (12955 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) ^ 24 =
      (tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12955 ≤ (2 * 12955 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) * √((42 / 10 : ℝ) / 12955) *
      energyCoefficient18 12955) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) ^ 18 =
      (tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12955) ^ 18 = ((42 / 10 : ℝ) / 12955) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12955) ^ 9 *
        (2 * 12955 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12955

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12955
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12955 (61 / 100) 164 (17 / (100 * 12955)) (26 / (10 * 12955))
    (statisticsConstant (paperBound256 12955)) √((42 / 10 : ℝ) / 12955) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12955) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12955 : ℕ))
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
    change (√(tA 12955 * ((164 : ℝ) ^ 2 / (12955 - 2))) *
      √((42 / 10 : ℝ) / 12955) * energyCoefficient18 12955) ^ 18 *
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
    exp (-(12955 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12955 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12955 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12955

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12955
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12955) : Set (Matrix (Fin (mA 12955)) (Fin 12955) ℝ) :=
  {X | ∀ g : Fin (Js 12955),
    17 / (100 * (12955 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12955 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12955) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12955),
      {X | 17 / (100 * (12955 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12955 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12955} (hw : windowW wr) :
    (gaussMat (mA 12955) 12955 (2 / (12955 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12955,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12955 : ℝ)) ∨
      42 / (10 * (12955 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12955) : Set (Matrix (Fin (mA 12955)) (Fin 12955) ℝ) :=
  (Eop 12955 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12955))

theorem tableFirstEvent_measurable (wr : WRet 12955) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12955} (hw : windowW wr) :
    (gaussMat (mA 12955) 12955 (2 / (12955 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12955)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12955) : Set (AHid 12955) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12955) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12955} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12955) 12955 (2 / (12955 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12955) (mA 12955) (tA 12955))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12955)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12955)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12955)) := (hvar g).1
  have hmax (g : Fin (Js 12955)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12955) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12955)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12955) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12955))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12955)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12955) (mA 12955) (tA 12955)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12955) :
    (nuA 12955).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12955

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12955
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12955 × AHid 12955) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12955)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12955) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12955)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12955)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12955)) :
    (retDist (paperCentres 12955)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12955

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12955 :
    BstLean.Part262.ActualRootCertificate 12955 BstLean.Part266.agent12955.root where
  dimension := by norm_num
  table_payment := Row12955.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12955.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12955.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12956
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12956 : ℝ) *
      √(tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12956 : ℝ) ^ 24 = (12956 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) ^ 24 =
      (tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12956 ≤ (2 * 12956 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) * √((42 / 10 : ℝ) / 12956) *
      energyCoefficient18 12956) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) ^ 18 =
      (tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12956) ^ 18 = ((42 / 10 : ℝ) / 12956) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12956) ^ 9 *
        (2 * 12956 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12956

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12956
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12956 (61 / 100) 164 (17 / (100 * 12956)) (26 / (10 * 12956))
    (statisticsConstant (paperBound256 12956)) √((42 / 10 : ℝ) / 12956) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12956) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12956 : ℕ))
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
    change (√(tA 12956 * ((164 : ℝ) ^ 2 / (12956 - 2))) *
      √((42 / 10 : ℝ) / 12956) * energyCoefficient18 12956) ^ 18 *
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
    exp (-(12956 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12956 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12956 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12956

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12956
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12956) : Set (Matrix (Fin (mA 12956)) (Fin 12956) ℝ) :=
  {X | ∀ g : Fin (Js 12956),
    17 / (100 * (12956 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12956 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12956) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12956),
      {X | 17 / (100 * (12956 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12956 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12956} (hw : windowW wr) :
    (gaussMat (mA 12956) 12956 (2 / (12956 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12956,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12956 : ℝ)) ∨
      42 / (10 * (12956 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12956) : Set (Matrix (Fin (mA 12956)) (Fin 12956) ℝ) :=
  (Eop 12956 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12956))

theorem tableFirstEvent_measurable (wr : WRet 12956) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12956} (hw : windowW wr) :
    (gaussMat (mA 12956) 12956 (2 / (12956 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12956)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12956) : Set (AHid 12956) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12956) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12956} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12956) 12956 (2 / (12956 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12956) (mA 12956) (tA 12956))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12956)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12956)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12956)) := (hvar g).1
  have hmax (g : Fin (Js 12956)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12956) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12956)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12956) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12956))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12956)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12956) (mA 12956) (tA 12956)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12956) :
    (nuA 12956).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12956

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12956
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12956 × AHid 12956) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12956)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12956) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12956)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12956)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12956)) :
    (retDist (paperCentres 12956)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12956

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12956 :
    BstLean.Part262.ActualRootCertificate 12956 BstLean.Part266.agent12956.root where
  dimension := by norm_num
  table_payment := Row12956.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12956.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12956.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12957
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12957 : ℝ) *
      √(tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12957 : ℝ) ^ 24 = (12957 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) ^ 24 =
      (tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12957 ≤ (2 * 12957 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) * √((42 / 10 : ℝ) / 12957) *
      energyCoefficient18 12957) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) ^ 18 =
      (tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12957) ^ 18 = ((42 / 10 : ℝ) / 12957) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12957) ^ 9 *
        (2 * 12957 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12957

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12957
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12957 (61 / 100) 164 (17 / (100 * 12957)) (26 / (10 * 12957))
    (statisticsConstant (paperBound256 12957)) √((42 / 10 : ℝ) / 12957) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12957) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12957 : ℕ))
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
    change (√(tA 12957 * ((164 : ℝ) ^ 2 / (12957 - 2))) *
      √((42 / 10 : ℝ) / 12957) * energyCoefficient18 12957) ^ 18 *
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
    exp (-(12957 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12957 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12957 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12957

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12957
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12957) : Set (Matrix (Fin (mA 12957)) (Fin 12957) ℝ) :=
  {X | ∀ g : Fin (Js 12957),
    17 / (100 * (12957 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12957 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12957) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12957),
      {X | 17 / (100 * (12957 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12957 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12957} (hw : windowW wr) :
    (gaussMat (mA 12957) 12957 (2 / (12957 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12957,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12957 : ℝ)) ∨
      42 / (10 * (12957 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12957) : Set (Matrix (Fin (mA 12957)) (Fin 12957) ℝ) :=
  (Eop 12957 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12957))

theorem tableFirstEvent_measurable (wr : WRet 12957) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12957} (hw : windowW wr) :
    (gaussMat (mA 12957) 12957 (2 / (12957 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12957)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12957) : Set (AHid 12957) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12957) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12957} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12957) 12957 (2 / (12957 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12957) (mA 12957) (tA 12957))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12957)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12957)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12957)) := (hvar g).1
  have hmax (g : Fin (Js 12957)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12957) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12957)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12957) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12957))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12957)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12957) (mA 12957) (tA 12957)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12957) :
    (nuA 12957).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12957

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12957
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12957 × AHid 12957) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12957)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12957) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12957)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12957)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12957)) :
    (retDist (paperCentres 12957)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12957

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12957 :
    BstLean.Part262.ActualRootCertificate 12957 BstLean.Part266.agent12957.root where
  dimension := by norm_num
  table_payment := Row12957.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12957.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12957.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12958
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12958 : ℝ) *
      √(tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12958 : ℝ) ^ 24 = (12958 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) ^ 24 =
      (tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12958 ≤ (2 * 12958 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) * √((42 / 10 : ℝ) / 12958) *
      energyCoefficient18 12958) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) ^ 18 =
      (tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12958) ^ 18 = ((42 / 10 : ℝ) / 12958) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12958) ^ 9 *
        (2 * 12958 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12958

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12958
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12958 (61 / 100) 164 (17 / (100 * 12958)) (26 / (10 * 12958))
    (statisticsConstant (paperBound256 12958)) √((42 / 10 : ℝ) / 12958) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12958) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12958 : ℕ))
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
    change (√(tA 12958 * ((164 : ℝ) ^ 2 / (12958 - 2))) *
      √((42 / 10 : ℝ) / 12958) * energyCoefficient18 12958) ^ 18 *
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
    exp (-(12958 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12958 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12958 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12958

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12958
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12958) : Set (Matrix (Fin (mA 12958)) (Fin 12958) ℝ) :=
  {X | ∀ g : Fin (Js 12958),
    17 / (100 * (12958 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12958 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12958) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12958),
      {X | 17 / (100 * (12958 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12958 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12958} (hw : windowW wr) :
    (gaussMat (mA 12958) 12958 (2 / (12958 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12958,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12958 : ℝ)) ∨
      42 / (10 * (12958 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12958) : Set (Matrix (Fin (mA 12958)) (Fin 12958) ℝ) :=
  (Eop 12958 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12958))

theorem tableFirstEvent_measurable (wr : WRet 12958) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12958} (hw : windowW wr) :
    (gaussMat (mA 12958) 12958 (2 / (12958 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12958)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12958) : Set (AHid 12958) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12958) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12958} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12958) 12958 (2 / (12958 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12958) (mA 12958) (tA 12958))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12958)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12958)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12958)) := (hvar g).1
  have hmax (g : Fin (Js 12958)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12958) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12958)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12958) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12958))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12958)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12958) (mA 12958) (tA 12958)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12958) :
    (nuA 12958).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12958

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12958
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12958 × AHid 12958) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12958)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12958) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12958)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12958)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12958)) :
    (retDist (paperCentres 12958)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12958

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12958 :
    BstLean.Part262.ActualRootCertificate 12958 BstLean.Part266.agent12958.root where
  dimension := by norm_num
  table_payment := Row12958.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12958.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12958.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12959
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12959 : ℝ) *
      √(tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12959 : ℝ) ^ 24 = (12959 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) ^ 24 =
      (tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12959 ≤ (2 * 12959 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) * √((42 / 10 : ℝ) / 12959) *
      energyCoefficient18 12959) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) ^ 18 =
      (tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12959) ^ 18 = ((42 / 10 : ℝ) / 12959) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12959) ^ 9 *
        (2 * 12959 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12959

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12959
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12959 (61 / 100) 164 (17 / (100 * 12959)) (26 / (10 * 12959))
    (statisticsConstant (paperBound256 12959)) √((42 / 10 : ℝ) / 12959) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12959) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12959 : ℕ))
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
    change (√(tA 12959 * ((164 : ℝ) ^ 2 / (12959 - 2))) *
      √((42 / 10 : ℝ) / 12959) * energyCoefficient18 12959) ^ 18 *
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
    exp (-(12959 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12959 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12959 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12959

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12959
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12959) : Set (Matrix (Fin (mA 12959)) (Fin 12959) ℝ) :=
  {X | ∀ g : Fin (Js 12959),
    17 / (100 * (12959 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12959 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12959) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12959),
      {X | 17 / (100 * (12959 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12959 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12959} (hw : windowW wr) :
    (gaussMat (mA 12959) 12959 (2 / (12959 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12959,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12959 : ℝ)) ∨
      42 / (10 * (12959 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12959) : Set (Matrix (Fin (mA 12959)) (Fin 12959) ℝ) :=
  (Eop 12959 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12959))

theorem tableFirstEvent_measurable (wr : WRet 12959) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12959} (hw : windowW wr) :
    (gaussMat (mA 12959) 12959 (2 / (12959 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12959)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12959) : Set (AHid 12959) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12959) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12959} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12959) 12959 (2 / (12959 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12959) (mA 12959) (tA 12959))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12959)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12959)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12959)) := (hvar g).1
  have hmax (g : Fin (Js 12959)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12959) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12959)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12959) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12959))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12959)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12959) (mA 12959) (tA 12959)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12959) :
    (nuA 12959).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12959

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12959
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12959 × AHid 12959) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12959)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12959) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12959)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12959)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12959)) :
    (retDist (paperCentres 12959)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12959

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12959 :
    BstLean.Part262.ActualRootCertificate 12959 BstLean.Part266.agent12959.root where
  dimension := by norm_num
  table_payment := Row12959.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12959.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12959.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12960
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12960 : ℝ) *
      √(tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12960 : ℝ) ^ 24 = (12960 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) ^ 24 =
      (tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12960 ≤ (2 * 12960 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) * √((42 / 10 : ℝ) / 12960) *
      energyCoefficient18 12960) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) ^ 18 =
      (tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12960) ^ 18 = ((42 / 10 : ℝ) / 12960) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12960) ^ 9 *
        (2 * 12960 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12960

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12960
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12960 (61 / 100) 164 (17 / (100 * 12960)) (26 / (10 * 12960))
    (statisticsConstant (paperBound256 12960)) √((42 / 10 : ℝ) / 12960) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12960) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12960 : ℕ))
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
    change (√(tA 12960 * ((164 : ℝ) ^ 2 / (12960 - 2))) *
      √((42 / 10 : ℝ) / 12960) * energyCoefficient18 12960) ^ 18 *
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
    exp (-(12960 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12960 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12960 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12960

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12960
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12960) : Set (Matrix (Fin (mA 12960)) (Fin 12960) ℝ) :=
  {X | ∀ g : Fin (Js 12960),
    17 / (100 * (12960 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12960 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12960) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12960),
      {X | 17 / (100 * (12960 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12960 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12960} (hw : windowW wr) :
    (gaussMat (mA 12960) 12960 (2 / (12960 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12960,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12960 : ℝ)) ∨
      42 / (10 * (12960 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12960) : Set (Matrix (Fin (mA 12960)) (Fin 12960) ℝ) :=
  (Eop 12960 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12960))

theorem tableFirstEvent_measurable (wr : WRet 12960) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12960} (hw : windowW wr) :
    (gaussMat (mA 12960) 12960 (2 / (12960 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12960)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12960) : Set (AHid 12960) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12960) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12960} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12960) 12960 (2 / (12960 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12960) (mA 12960) (tA 12960))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12960)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12960)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12960)) := (hvar g).1
  have hmax (g : Fin (Js 12960)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12960) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12960)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12960) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12960))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12960)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12960) (mA 12960) (tA 12960)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12960) :
    (nuA 12960).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12960

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12960
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12960 × AHid 12960) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12960)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12960) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12960)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12960)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12960)) :
    (retDist (paperCentres 12960)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12960

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12960 :
    BstLean.Part262.ActualRootCertificate 12960 BstLean.Part266.agent12960.root where
  dimension := by norm_num
  table_payment := Row12960.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12960.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12960.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12961
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12961 : ℝ) *
      √(tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12961 : ℝ) ^ 24 = (12961 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) ^ 24 =
      (tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12961 ≤ (2 * 12961 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) * √((42 / 10 : ℝ) / 12961) *
      energyCoefficient18 12961) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) ^ 18 =
      (tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12961) ^ 18 = ((42 / 10 : ℝ) / 12961) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12961) ^ 9 *
        (2 * 12961 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12961

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12961
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12961 (61 / 100) 164 (17 / (100 * 12961)) (26 / (10 * 12961))
    (statisticsConstant (paperBound256 12961)) √((42 / 10 : ℝ) / 12961) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12961) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12961 : ℕ))
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
    change (√(tA 12961 * ((164 : ℝ) ^ 2 / (12961 - 2))) *
      √((42 / 10 : ℝ) / 12961) * energyCoefficient18 12961) ^ 18 *
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
    exp (-(12961 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12961 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12961 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12961

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12961
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12961) : Set (Matrix (Fin (mA 12961)) (Fin 12961) ℝ) :=
  {X | ∀ g : Fin (Js 12961),
    17 / (100 * (12961 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12961 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12961) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12961),
      {X | 17 / (100 * (12961 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12961 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12961} (hw : windowW wr) :
    (gaussMat (mA 12961) 12961 (2 / (12961 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12961,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12961 : ℝ)) ∨
      42 / (10 * (12961 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12961) : Set (Matrix (Fin (mA 12961)) (Fin 12961) ℝ) :=
  (Eop 12961 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12961))

theorem tableFirstEvent_measurable (wr : WRet 12961) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12961} (hw : windowW wr) :
    (gaussMat (mA 12961) 12961 (2 / (12961 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12961)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12961) : Set (AHid 12961) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12961) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12961} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12961) 12961 (2 / (12961 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12961) (mA 12961) (tA 12961))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12961)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12961)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12961)) := (hvar g).1
  have hmax (g : Fin (Js 12961)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12961) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12961)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12961) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12961))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12961)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12961) (mA 12961) (tA 12961)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12961) :
    (nuA 12961).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12961

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12961
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12961 × AHid 12961) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12961)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12961) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12961)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12961)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12961)) :
    (retDist (paperCentres 12961)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12961

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12961 :
    BstLean.Part262.ActualRootCertificate 12961 BstLean.Part266.agent12961.root where
  dimension := by norm_num
  table_payment := Row12961.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12961.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12961.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12962
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12962 : ℝ) *
      √(tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12962 : ℝ) ^ 24 = (12962 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) ^ 24 =
      (tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12962 ≤ (2 * 12962 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) * √((42 / 10 : ℝ) / 12962) *
      energyCoefficient18 12962) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) ^ 18 =
      (tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12962) ^ 18 = ((42 / 10 : ℝ) / 12962) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12962) ^ 9 *
        (2 * 12962 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12962

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12962
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12962 (61 / 100) 164 (17 / (100 * 12962)) (26 / (10 * 12962))
    (statisticsConstant (paperBound256 12962)) √((42 / 10 : ℝ) / 12962) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12962) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12962 : ℕ))
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
    change (√(tA 12962 * ((164 : ℝ) ^ 2 / (12962 - 2))) *
      √((42 / 10 : ℝ) / 12962) * energyCoefficient18 12962) ^ 18 *
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
    exp (-(12962 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12962 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12962 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12962

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12962
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12962) : Set (Matrix (Fin (mA 12962)) (Fin 12962) ℝ) :=
  {X | ∀ g : Fin (Js 12962),
    17 / (100 * (12962 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12962 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12962) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12962),
      {X | 17 / (100 * (12962 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12962 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12962} (hw : windowW wr) :
    (gaussMat (mA 12962) 12962 (2 / (12962 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12962,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12962 : ℝ)) ∨
      42 / (10 * (12962 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12962) : Set (Matrix (Fin (mA 12962)) (Fin 12962) ℝ) :=
  (Eop 12962 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12962))

theorem tableFirstEvent_measurable (wr : WRet 12962) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12962} (hw : windowW wr) :
    (gaussMat (mA 12962) 12962 (2 / (12962 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12962)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12962) : Set (AHid 12962) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12962) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12962} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12962) 12962 (2 / (12962 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12962) (mA 12962) (tA 12962))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12962)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12962)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12962)) := (hvar g).1
  have hmax (g : Fin (Js 12962)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12962) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12962)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12962) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12962))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12962)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12962) (mA 12962) (tA 12962)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12962) :
    (nuA 12962).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12962

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12962
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12962 × AHid 12962) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12962)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12962) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12962)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12962)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12962)) :
    (retDist (paperCentres 12962)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12962

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12962 :
    BstLean.Part262.ActualRootCertificate 12962 BstLean.Part266.agent12962.root where
  dimension := by norm_num
  table_payment := Row12962.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12962.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12962.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12963
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12963 : ℝ) *
      √(tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12963 : ℝ) ^ 24 = (12963 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) ^ 24 =
      (tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12963 ≤ (2 * 12963 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) * √((42 / 10 : ℝ) / 12963) *
      energyCoefficient18 12963) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) ^ 18 =
      (tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12963) ^ 18 = ((42 / 10 : ℝ) / 12963) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12963) ^ 9 *
        (2 * 12963 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12963

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12963
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12963 (61 / 100) 164 (17 / (100 * 12963)) (26 / (10 * 12963))
    (statisticsConstant (paperBound256 12963)) √((42 / 10 : ℝ) / 12963) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12963) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12963 : ℕ))
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
    change (√(tA 12963 * ((164 : ℝ) ^ 2 / (12963 - 2))) *
      √((42 / 10 : ℝ) / 12963) * energyCoefficient18 12963) ^ 18 *
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
    exp (-(12963 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12963 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12963 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12963

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12963
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12963) : Set (Matrix (Fin (mA 12963)) (Fin 12963) ℝ) :=
  {X | ∀ g : Fin (Js 12963),
    17 / (100 * (12963 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12963 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12963) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12963),
      {X | 17 / (100 * (12963 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12963 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12963} (hw : windowW wr) :
    (gaussMat (mA 12963) 12963 (2 / (12963 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12963,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12963 : ℝ)) ∨
      42 / (10 * (12963 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12963) : Set (Matrix (Fin (mA 12963)) (Fin 12963) ℝ) :=
  (Eop 12963 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12963))

theorem tableFirstEvent_measurable (wr : WRet 12963) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12963} (hw : windowW wr) :
    (gaussMat (mA 12963) 12963 (2 / (12963 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12963)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12963) : Set (AHid 12963) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12963) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12963} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12963) 12963 (2 / (12963 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12963) (mA 12963) (tA 12963))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12963)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12963)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12963)) := (hvar g).1
  have hmax (g : Fin (Js 12963)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12963) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12963)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12963) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12963))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12963)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12963) (mA 12963) (tA 12963)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12963) :
    (nuA 12963).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12963

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12963
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12963 × AHid 12963) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12963)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12963) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12963)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12963)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12963)) :
    (retDist (paperCentres 12963)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12963

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12963 :
    BstLean.Part262.ActualRootCertificate 12963 BstLean.Part266.agent12963.root where
  dimension := by norm_num
  table_payment := Row12963.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12963.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12963.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12964
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12964 : ℝ) *
      √(tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12964 : ℝ) ^ 24 = (12964 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) ^ 24 =
      (tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12964 ≤ (2 * 12964 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) * √((42 / 10 : ℝ) / 12964) *
      energyCoefficient18 12964) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) ^ 18 =
      (tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12964) ^ 18 = ((42 / 10 : ℝ) / 12964) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12964) ^ 9 *
        (2 * 12964 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12964

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12964
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12964 (61 / 100) 164 (17 / (100 * 12964)) (26 / (10 * 12964))
    (statisticsConstant (paperBound256 12964)) √((42 / 10 : ℝ) / 12964) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12964) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12964 : ℕ))
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
    change (√(tA 12964 * ((164 : ℝ) ^ 2 / (12964 - 2))) *
      √((42 / 10 : ℝ) / 12964) * energyCoefficient18 12964) ^ 18 *
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
    exp (-(12964 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12964 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12964 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12964

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12964
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12964) : Set (Matrix (Fin (mA 12964)) (Fin 12964) ℝ) :=
  {X | ∀ g : Fin (Js 12964),
    17 / (100 * (12964 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12964 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12964) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12964),
      {X | 17 / (100 * (12964 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12964 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12964} (hw : windowW wr) :
    (gaussMat (mA 12964) 12964 (2 / (12964 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12964,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12964 : ℝ)) ∨
      42 / (10 * (12964 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12964) : Set (Matrix (Fin (mA 12964)) (Fin 12964) ℝ) :=
  (Eop 12964 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12964))

theorem tableFirstEvent_measurable (wr : WRet 12964) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12964} (hw : windowW wr) :
    (gaussMat (mA 12964) 12964 (2 / (12964 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12964)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12964) : Set (AHid 12964) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12964) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12964} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12964) 12964 (2 / (12964 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12964) (mA 12964) (tA 12964))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12964)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12964)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12964)) := (hvar g).1
  have hmax (g : Fin (Js 12964)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12964) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12964)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12964) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12964))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12964)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12964) (mA 12964) (tA 12964)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12964) :
    (nuA 12964).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12964

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12964
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12964 × AHid 12964) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12964)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12964) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12964)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12964)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12964)) :
    (retDist (paperCentres 12964)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12964

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12964 :
    BstLean.Part262.ActualRootCertificate 12964 BstLean.Part266.agent12964.root where
  dimension := by norm_num
  table_payment := Row12964.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12964.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12964.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12965
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12965 : ℝ) *
      √(tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12965 : ℝ) ^ 24 = (12965 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) ^ 24 =
      (tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12965 ≤ (2 * 12965 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) * √((42 / 10 : ℝ) / 12965) *
      energyCoefficient18 12965) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) ^ 18 =
      (tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12965) ^ 18 = ((42 / 10 : ℝ) / 12965) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12965) ^ 9 *
        (2 * 12965 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12965

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12965
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12965 (61 / 100) 164 (17 / (100 * 12965)) (26 / (10 * 12965))
    (statisticsConstant (paperBound256 12965)) √((42 / 10 : ℝ) / 12965) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12965) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12965 : ℕ))
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
    change (√(tA 12965 * ((164 : ℝ) ^ 2 / (12965 - 2))) *
      √((42 / 10 : ℝ) / 12965) * energyCoefficient18 12965) ^ 18 *
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
    exp (-(12965 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12965 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12965 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12965

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12965
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12965) : Set (Matrix (Fin (mA 12965)) (Fin 12965) ℝ) :=
  {X | ∀ g : Fin (Js 12965),
    17 / (100 * (12965 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12965 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12965) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12965),
      {X | 17 / (100 * (12965 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12965 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12965} (hw : windowW wr) :
    (gaussMat (mA 12965) 12965 (2 / (12965 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12965,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12965 : ℝ)) ∨
      42 / (10 * (12965 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12965) : Set (Matrix (Fin (mA 12965)) (Fin 12965) ℝ) :=
  (Eop 12965 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12965))

theorem tableFirstEvent_measurable (wr : WRet 12965) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12965} (hw : windowW wr) :
    (gaussMat (mA 12965) 12965 (2 / (12965 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12965)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12965) : Set (AHid 12965) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12965) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12965} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12965) 12965 (2 / (12965 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12965) (mA 12965) (tA 12965))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12965)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12965)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12965)) := (hvar g).1
  have hmax (g : Fin (Js 12965)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12965) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12965)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12965) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12965))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12965)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12965) (mA 12965) (tA 12965)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12965) :
    (nuA 12965).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12965

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12965
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12965 × AHid 12965) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12965)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12965) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12965)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12965)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12965)) :
    (retDist (paperCentres 12965)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12965

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12965 :
    BstLean.Part262.ActualRootCertificate 12965 BstLean.Part266.agent12965.root where
  dimension := by norm_num
  table_payment := Row12965.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12965.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12965.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12966
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12966 : ℝ) *
      √(tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12966 : ℝ) ^ 24 = (12966 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) ^ 24 =
      (tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12966 ≤ (2 * 12966 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) * √((42 / 10 : ℝ) / 12966) *
      energyCoefficient18 12966) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) ^ 18 =
      (tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12966) ^ 18 = ((42 / 10 : ℝ) / 12966) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12966) ^ 9 *
        (2 * 12966 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12966

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12966
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12966 (61 / 100) 164 (17 / (100 * 12966)) (26 / (10 * 12966))
    (statisticsConstant (paperBound256 12966)) √((42 / 10 : ℝ) / 12966) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12966) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12966 : ℕ))
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
    change (√(tA 12966 * ((164 : ℝ) ^ 2 / (12966 - 2))) *
      √((42 / 10 : ℝ) / 12966) * energyCoefficient18 12966) ^ 18 *
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
    exp (-(12966 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12966 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12966 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12966

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12966
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12966) : Set (Matrix (Fin (mA 12966)) (Fin 12966) ℝ) :=
  {X | ∀ g : Fin (Js 12966),
    17 / (100 * (12966 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12966 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12966) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12966),
      {X | 17 / (100 * (12966 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12966 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12966} (hw : windowW wr) :
    (gaussMat (mA 12966) 12966 (2 / (12966 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12966,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12966 : ℝ)) ∨
      42 / (10 * (12966 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12966) : Set (Matrix (Fin (mA 12966)) (Fin 12966) ℝ) :=
  (Eop 12966 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12966))

theorem tableFirstEvent_measurable (wr : WRet 12966) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12966} (hw : windowW wr) :
    (gaussMat (mA 12966) 12966 (2 / (12966 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12966)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12966) : Set (AHid 12966) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12966) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12966} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12966) 12966 (2 / (12966 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12966) (mA 12966) (tA 12966))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12966)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12966)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12966)) := (hvar g).1
  have hmax (g : Fin (Js 12966)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12966) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12966)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12966) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12966))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12966)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12966) (mA 12966) (tA 12966)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12966) :
    (nuA 12966).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12966

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12966
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12966 × AHid 12966) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12966)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12966) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12966)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12966)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12966)) :
    (retDist (paperCentres 12966)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12966

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12966 :
    BstLean.Part262.ActualRootCertificate 12966 BstLean.Part266.agent12966.root where
  dimension := by norm_num
  table_payment := Row12966.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12966.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12966.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12967
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12967 : ℝ) *
      √(tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12967 : ℝ) ^ 24 = (12967 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) ^ 24 =
      (tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12967 ≤ (2 * 12967 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) * √((42 / 10 : ℝ) / 12967) *
      energyCoefficient18 12967) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) ^ 18 =
      (tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12967) ^ 18 = ((42 / 10 : ℝ) / 12967) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12967) ^ 9 *
        (2 * 12967 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12967

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12967
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12967 (61 / 100) 164 (17 / (100 * 12967)) (26 / (10 * 12967))
    (statisticsConstant (paperBound256 12967)) √((42 / 10 : ℝ) / 12967) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12967) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12967 : ℕ))
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
    change (√(tA 12967 * ((164 : ℝ) ^ 2 / (12967 - 2))) *
      √((42 / 10 : ℝ) / 12967) * energyCoefficient18 12967) ^ 18 *
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
    exp (-(12967 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12967 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12967 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12967

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12967
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12967) : Set (Matrix (Fin (mA 12967)) (Fin 12967) ℝ) :=
  {X | ∀ g : Fin (Js 12967),
    17 / (100 * (12967 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12967 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12967) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12967),
      {X | 17 / (100 * (12967 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12967 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12967} (hw : windowW wr) :
    (gaussMat (mA 12967) 12967 (2 / (12967 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12967,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12967 : ℝ)) ∨
      42 / (10 * (12967 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12967) : Set (Matrix (Fin (mA 12967)) (Fin 12967) ℝ) :=
  (Eop 12967 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12967))

theorem tableFirstEvent_measurable (wr : WRet 12967) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12967} (hw : windowW wr) :
    (gaussMat (mA 12967) 12967 (2 / (12967 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12967)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12967) : Set (AHid 12967) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12967) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12967} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12967) 12967 (2 / (12967 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12967) (mA 12967) (tA 12967))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12967)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12967)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12967)) := (hvar g).1
  have hmax (g : Fin (Js 12967)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12967) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12967)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12967) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12967))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12967)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12967) (mA 12967) (tA 12967)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12967) :
    (nuA 12967).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12967

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12967
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12967 × AHid 12967) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12967)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12967) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12967)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12967)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12967)) :
    (retDist (paperCentres 12967)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12967

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12967 :
    BstLean.Part262.ActualRootCertificate 12967 BstLean.Part266.agent12967.root where
  dimension := by norm_num
  table_payment := Row12967.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12967.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12967.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12968
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12968 : ℝ) *
      √(tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12968 : ℝ) ^ 24 = (12968 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) ^ 24 =
      (tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12968 ≤ (2 * 12968 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) * √((42 / 10 : ℝ) / 12968) *
      energyCoefficient18 12968) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) ^ 18 =
      (tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12968) ^ 18 = ((42 / 10 : ℝ) / 12968) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12968) ^ 9 *
        (2 * 12968 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12968

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12968
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12968 (61 / 100) 164 (17 / (100 * 12968)) (26 / (10 * 12968))
    (statisticsConstant (paperBound256 12968)) √((42 / 10 : ℝ) / 12968) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12968) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12968 : ℕ))
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
    change (√(tA 12968 * ((164 : ℝ) ^ 2 / (12968 - 2))) *
      √((42 / 10 : ℝ) / 12968) * energyCoefficient18 12968) ^ 18 *
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
    exp (-(12968 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12968 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12968 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12968

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12968
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12968) : Set (Matrix (Fin (mA 12968)) (Fin 12968) ℝ) :=
  {X | ∀ g : Fin (Js 12968),
    17 / (100 * (12968 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12968 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12968) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12968),
      {X | 17 / (100 * (12968 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12968 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12968} (hw : windowW wr) :
    (gaussMat (mA 12968) 12968 (2 / (12968 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12968,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12968 : ℝ)) ∨
      42 / (10 * (12968 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12968) : Set (Matrix (Fin (mA 12968)) (Fin 12968) ℝ) :=
  (Eop 12968 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12968))

theorem tableFirstEvent_measurable (wr : WRet 12968) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12968} (hw : windowW wr) :
    (gaussMat (mA 12968) 12968 (2 / (12968 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12968)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12968) : Set (AHid 12968) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12968) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12968} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12968) 12968 (2 / (12968 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12968) (mA 12968) (tA 12968))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12968)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12968)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12968)) := (hvar g).1
  have hmax (g : Fin (Js 12968)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12968) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12968)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12968) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12968))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12968)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12968) (mA 12968) (tA 12968)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12968) :
    (nuA 12968).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12968

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12968
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12968 × AHid 12968) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12968)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12968) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12968)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12968)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12968)) :
    (retDist (paperCentres 12968)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12968

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12968 :
    BstLean.Part262.ActualRootCertificate 12968 BstLean.Part266.agent12968.root where
  dimension := by norm_num
  table_payment := Row12968.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12968.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12968.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12969
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12969 : ℝ) *
      √(tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12969 : ℝ) ^ 24 = (12969 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) ^ 24 =
      (tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12969 ≤ (2 * 12969 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) * √((42 / 10 : ℝ) / 12969) *
      energyCoefficient18 12969) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) ^ 18 =
      (tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12969) ^ 18 = ((42 / 10 : ℝ) / 12969) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12969) ^ 9 *
        (2 * 12969 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12969

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12969
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12969 (61 / 100) 164 (17 / (100 * 12969)) (26 / (10 * 12969))
    (statisticsConstant (paperBound256 12969)) √((42 / 10 : ℝ) / 12969) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12969) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12969 : ℕ))
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
    change (√(tA 12969 * ((164 : ℝ) ^ 2 / (12969 - 2))) *
      √((42 / 10 : ℝ) / 12969) * energyCoefficient18 12969) ^ 18 *
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
    exp (-(12969 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12969 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12969 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12969

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12969
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12969) : Set (Matrix (Fin (mA 12969)) (Fin 12969) ℝ) :=
  {X | ∀ g : Fin (Js 12969),
    17 / (100 * (12969 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12969 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12969) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12969),
      {X | 17 / (100 * (12969 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12969 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12969} (hw : windowW wr) :
    (gaussMat (mA 12969) 12969 (2 / (12969 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12969,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12969 : ℝ)) ∨
      42 / (10 * (12969 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12969) : Set (Matrix (Fin (mA 12969)) (Fin 12969) ℝ) :=
  (Eop 12969 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12969))

theorem tableFirstEvent_measurable (wr : WRet 12969) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12969} (hw : windowW wr) :
    (gaussMat (mA 12969) 12969 (2 / (12969 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12969)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12969) : Set (AHid 12969) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12969) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12969} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12969) 12969 (2 / (12969 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12969) (mA 12969) (tA 12969))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12969)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12969)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12969)) := (hvar g).1
  have hmax (g : Fin (Js 12969)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12969) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12969)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12969) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12969))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12969)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12969) (mA 12969) (tA 12969)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12969) :
    (nuA 12969).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12969

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12969
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12969 × AHid 12969) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12969)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12969) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12969)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12969)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12969)) :
    (retDist (paperCentres 12969)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12969

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12969 :
    BstLean.Part262.ActualRootCertificate 12969 BstLean.Part266.agent12969.root where
  dimension := by norm_num
  table_payment := Row12969.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12969.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12969.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12970
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12970 : ℝ) *
      √(tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12970 : ℝ) ^ 24 = (12970 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) ^ 24 =
      (tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12970 ≤ (2 * 12970 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) * √((42 / 10 : ℝ) / 12970) *
      energyCoefficient18 12970) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) ^ 18 =
      (tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12970) ^ 18 = ((42 / 10 : ℝ) / 12970) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12970) ^ 9 *
        (2 * 12970 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12970

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12970
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12970 (61 / 100) 164 (17 / (100 * 12970)) (26 / (10 * 12970))
    (statisticsConstant (paperBound256 12970)) √((42 / 10 : ℝ) / 12970) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12970) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12970 : ℕ))
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
    change (√(tA 12970 * ((164 : ℝ) ^ 2 / (12970 - 2))) *
      √((42 / 10 : ℝ) / 12970) * energyCoefficient18 12970) ^ 18 *
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
    exp (-(12970 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12970 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12970 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12970

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12970
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12970) : Set (Matrix (Fin (mA 12970)) (Fin 12970) ℝ) :=
  {X | ∀ g : Fin (Js 12970),
    17 / (100 * (12970 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12970 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12970) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12970),
      {X | 17 / (100 * (12970 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12970 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12970} (hw : windowW wr) :
    (gaussMat (mA 12970) 12970 (2 / (12970 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12970,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12970 : ℝ)) ∨
      42 / (10 * (12970 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12970) : Set (Matrix (Fin (mA 12970)) (Fin 12970) ℝ) :=
  (Eop 12970 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12970))

theorem tableFirstEvent_measurable (wr : WRet 12970) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12970} (hw : windowW wr) :
    (gaussMat (mA 12970) 12970 (2 / (12970 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12970)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12970) : Set (AHid 12970) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12970) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12970} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12970) 12970 (2 / (12970 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12970) (mA 12970) (tA 12970))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12970)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12970)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12970)) := (hvar g).1
  have hmax (g : Fin (Js 12970)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12970) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12970)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12970) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12970))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12970)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12970) (mA 12970) (tA 12970)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12970) :
    (nuA 12970).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12970

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12970
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12970 × AHid 12970) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12970)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12970) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12970)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12970)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12970)) :
    (retDist (paperCentres 12970)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12970

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12970 :
    BstLean.Part262.ActualRootCertificate 12970 BstLean.Part266.agent12970.root where
  dimension := by norm_num
  table_payment := Row12970.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12970.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12970.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12971
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12971 : ℝ) *
      √(tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12971 : ℝ) ^ 24 = (12971 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) ^ 24 =
      (tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12971 ≤ (2 * 12971 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) * √((42 / 10 : ℝ) / 12971) *
      energyCoefficient18 12971) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) ^ 18 =
      (tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12971) ^ 18 = ((42 / 10 : ℝ) / 12971) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12971) ^ 9 *
        (2 * 12971 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12971

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12971
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12971 (61 / 100) 164 (17 / (100 * 12971)) (26 / (10 * 12971))
    (statisticsConstant (paperBound256 12971)) √((42 / 10 : ℝ) / 12971) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12971) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12971 : ℕ))
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
    change (√(tA 12971 * ((164 : ℝ) ^ 2 / (12971 - 2))) *
      √((42 / 10 : ℝ) / 12971) * energyCoefficient18 12971) ^ 18 *
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
    exp (-(12971 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12971 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12971 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12971

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12971
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12971) : Set (Matrix (Fin (mA 12971)) (Fin 12971) ℝ) :=
  {X | ∀ g : Fin (Js 12971),
    17 / (100 * (12971 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12971 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12971) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12971),
      {X | 17 / (100 * (12971 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12971 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12971} (hw : windowW wr) :
    (gaussMat (mA 12971) 12971 (2 / (12971 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12971,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12971 : ℝ)) ∨
      42 / (10 * (12971 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12971) : Set (Matrix (Fin (mA 12971)) (Fin 12971) ℝ) :=
  (Eop 12971 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12971))

theorem tableFirstEvent_measurable (wr : WRet 12971) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12971} (hw : windowW wr) :
    (gaussMat (mA 12971) 12971 (2 / (12971 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12971)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12971) : Set (AHid 12971) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12971) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12971} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12971) 12971 (2 / (12971 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12971) (mA 12971) (tA 12971))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12971)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12971)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12971)) := (hvar g).1
  have hmax (g : Fin (Js 12971)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12971) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12971)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12971) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12971))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12971)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12971) (mA 12971) (tA 12971)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12971) :
    (nuA 12971).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12971

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12971
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12971 × AHid 12971) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12971)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12971) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12971)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12971)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12971)) :
    (retDist (paperCentres 12971)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12971

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12971 :
    BstLean.Part262.ActualRootCertificate 12971 BstLean.Part266.agent12971.root where
  dimension := by norm_num
  table_payment := Row12971.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12971.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12971.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12972
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12972 : ℝ) *
      √(tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12972 : ℝ) ^ 24 = (12972 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) ^ 24 =
      (tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12972 ≤ (2 * 12972 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) * √((42 / 10 : ℝ) / 12972) *
      energyCoefficient18 12972) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) ^ 18 =
      (tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12972) ^ 18 = ((42 / 10 : ℝ) / 12972) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12972) ^ 9 *
        (2 * 12972 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12972

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12972
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12972 (61 / 100) 164 (17 / (100 * 12972)) (26 / (10 * 12972))
    (statisticsConstant (paperBound256 12972)) √((42 / 10 : ℝ) / 12972) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12972) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12972 : ℕ))
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
    change (√(tA 12972 * ((164 : ℝ) ^ 2 / (12972 - 2))) *
      √((42 / 10 : ℝ) / 12972) * energyCoefficient18 12972) ^ 18 *
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
    exp (-(12972 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12972 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12972 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12972

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12972
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12972) : Set (Matrix (Fin (mA 12972)) (Fin 12972) ℝ) :=
  {X | ∀ g : Fin (Js 12972),
    17 / (100 * (12972 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12972 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12972) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12972),
      {X | 17 / (100 * (12972 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12972 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12972} (hw : windowW wr) :
    (gaussMat (mA 12972) 12972 (2 / (12972 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12972,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12972 : ℝ)) ∨
      42 / (10 * (12972 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12972) : Set (Matrix (Fin (mA 12972)) (Fin 12972) ℝ) :=
  (Eop 12972 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12972))

theorem tableFirstEvent_measurable (wr : WRet 12972) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12972} (hw : windowW wr) :
    (gaussMat (mA 12972) 12972 (2 / (12972 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12972)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12972) : Set (AHid 12972) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12972) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12972} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12972) 12972 (2 / (12972 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12972) (mA 12972) (tA 12972))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12972)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12972)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12972)) := (hvar g).1
  have hmax (g : Fin (Js 12972)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12972) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12972)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12972) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12972))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12972)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12972) (mA 12972) (tA 12972)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12972) :
    (nuA 12972).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12972

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12972
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12972 × AHid 12972) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12972)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12972) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12972)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12972)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12972)) :
    (retDist (paperCentres 12972)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12972

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12972 :
    BstLean.Part262.ActualRootCertificate 12972 BstLean.Part266.agent12972.root where
  dimension := by norm_num
  table_payment := Row12972.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12972.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12972.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12973
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12973 : ℝ) *
      √(tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12973 : ℝ) ^ 24 = (12973 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) ^ 24 =
      (tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12973 ≤ (2 * 12973 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) * √((42 / 10 : ℝ) / 12973) *
      energyCoefficient18 12973) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) ^ 18 =
      (tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12973) ^ 18 = ((42 / 10 : ℝ) / 12973) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12973) ^ 9 *
        (2 * 12973 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12973

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12973
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12973 (61 / 100) 164 (17 / (100 * 12973)) (26 / (10 * 12973))
    (statisticsConstant (paperBound256 12973)) √((42 / 10 : ℝ) / 12973) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12973) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12973 : ℕ))
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
    change (√(tA 12973 * ((164 : ℝ) ^ 2 / (12973 - 2))) *
      √((42 / 10 : ℝ) / 12973) * energyCoefficient18 12973) ^ 18 *
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
    exp (-(12973 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12973 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12973 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12973

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12973
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12973) : Set (Matrix (Fin (mA 12973)) (Fin 12973) ℝ) :=
  {X | ∀ g : Fin (Js 12973),
    17 / (100 * (12973 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12973 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12973) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12973),
      {X | 17 / (100 * (12973 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12973 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12973} (hw : windowW wr) :
    (gaussMat (mA 12973) 12973 (2 / (12973 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12973,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12973 : ℝ)) ∨
      42 / (10 * (12973 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12973) : Set (Matrix (Fin (mA 12973)) (Fin 12973) ℝ) :=
  (Eop 12973 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12973))

theorem tableFirstEvent_measurable (wr : WRet 12973) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12973} (hw : windowW wr) :
    (gaussMat (mA 12973) 12973 (2 / (12973 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12973)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12973) : Set (AHid 12973) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12973) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12973} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12973) 12973 (2 / (12973 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12973) (mA 12973) (tA 12973))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12973)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12973)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12973)) := (hvar g).1
  have hmax (g : Fin (Js 12973)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12973) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12973)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12973) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12973))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12973)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12973) (mA 12973) (tA 12973)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12973) :
    (nuA 12973).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12973

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12973
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12973 × AHid 12973) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12973)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12973) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12973)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12973)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12973)) :
    (retDist (paperCentres 12973)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12973

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12973 :
    BstLean.Part262.ActualRootCertificate 12973 BstLean.Part266.agent12973.root where
  dimension := by norm_num
  table_payment := Row12973.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12973.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12973.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row12974
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(12974 : ℝ) *
      √(tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(12974 : ℝ) ^ 24 = (12974 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) ^ 24 =
      (tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 12974 ≤ (2 * 12974 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
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
    (√(tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) * √((42 / 10 : ℝ) / 12974) *
      energyCoefficient18 12974) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) ^ 18 =
      (tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12974) ^ 18 = ((42 / 10 : ℝ) / 12974) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12974) ^ 9 *
        (2 * 12974 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
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

end BstLean.Part266.Row12974

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row12974
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 12974 (61 / 100) 164 (17 / (100 * 12974)) (26 / (10 * 12974))
    (statisticsConstant (paperBound256 12974)) √((42 / 10 : ℝ) / 12974) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 12974) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (12974 : ℕ))
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
    change (√(tA 12974 * ((164 : ℝ) ^ 2 / (12974 - 2))) *
      √((42 / 10 : ℝ) / 12974) * energyCoefficient18 12974) ^ 18 *
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
    exp (-(12974 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(12974 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(12974 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row12974

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row12974
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 12974) : Set (Matrix (Fin (mA 12974)) (Fin 12974) ℝ) :=
  {X | ∀ g : Fin (Js 12974),
    17 / (100 * (12974 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (12974 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 12974) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 12974),
      {X | 17 / (100 * (12974 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (12974 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 12974} (hw : windowW wr) :
    (gaussMat (mA 12974) 12974 (2 / (12974 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 12974,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12974 : ℝ)) ∨
      42 / (10 * (12974 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 12974) : Set (Matrix (Fin (mA 12974)) (Fin 12974) ℝ) :=
  (Eop 12974 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 12974))

theorem tableFirstEvent_measurable (wr : WRet 12974) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 12974} (hw : windowW wr) :
    (gaussMat (mA 12974) 12974 (2 / (12974 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12974)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 12974) : Set (AHid 12974) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 12974) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 12974} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 12974) 12974 (2 / (12974 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 12974) (mA 12974) (tA 12974))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 12974)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 12974)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
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
  have hmin (g : Fin (Js 12974)) := (hvar g).1
  have hmax (g : Fin (Js 12974)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 12974) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 12974)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 12974) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 164) (by norm_num : (0 : ℝ) < 17 / (100 * 12974))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 12974)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 12974) (mA 12974) (tA 12974)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 12974) :
    (nuA 12974).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
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

end BstLean.Part266.Row12974

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row12974
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 12974 × AHid 12974) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 12974)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 12974) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 12974)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 12974)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 12974)) :
    (retDist (paperCentres 12974)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row12974

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate12974 :
    BstLean.Part262.ActualRootCertificate 12974 BstLean.Part266.agent12974.root where
  dimension := by norm_num
  table_payment := Row12974.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row12974.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row12974.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266
