import BstLean.Part292TableEvents
import BstLean.Part292FourBand
import BstLean.Part252ProductCharge
import BstLean.Part276World
import BstLean.Part289Design

/-! Node 41: one uniform paid table supplier on the entire low band. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part171 BstLean.Part223
open BstLean.Part152 (opN)
open BstLean.Part280 (nodeMeasureN nodeMeasureN_mass)

theorem table_conditional_charge {n : ℕ} (hn : 8000 ≤ n) {wr : WRet n}
    (hw : tableWorldGuard wr) :
    ∀ᵐ A ∂gaussMat (mA n) n (2/(n : ℝ)), A ∈ firstMatrixEvent (by omega) wr →
      (gaussMat (mA n) (mA n) (tA n)) {M | (A,M) ∈ tableBadPair n wr} ≤
        ENNReal.ofReal ((∑ i, (momentCap i/tableAllowance i)^tableOrder i)+exp (-18)) := by
  have hn1 : 1 ≤ n := by omega
  have hc := BstLean.Part172.sg_wr_ne hn1 hw.1
  have hs (g : Fin (Js n)) : nodeS (mkR wr (0,0)) g.val^2 ≤ 1 := by
    linarith [(node_geometry_low hn hw (0,0) g.isLt).2.1]
  filter_upwards [paperNodes_kink_ae (by omega) wr Fin.val hs] with A hk
  intro hA
  have hop : OpB A (lowOperator n) := opB_of_opN _ hA.1.1.1
  have hm := originalFour_markov_band hn hw A hop hA.1.1.2 hA.1.2 hA.2 hk
  have hmR : (gaussMat (mA n) (mA n) (tA n)).real
      (tableBad (nodeMeasureN hn1 wr) (fun i g => originalFourErrors (mkR wr (A,0)) i g.val)) ≤
      ∑ i, (momentCap i/tableAllowance i)^tableOrder i :=
    ENNReal.toReal_le_of_le_ofReal
      (Finset.sum_nonneg fun i _ => pow_nonneg
        (div_nonneg (momentCap_nonneg i) (tableAllowance_pos i).le) _) hm
  have hsub : {M | (A,M) ∈ tableBadPair n wr} ⊆
      tableBad (nodeMeasureN hn1 wr) (fun i g => originalFourErrors (mkR wr (A,0)) i g.val) ∪
        {M | lowSecondOperator n < opN M} := by
    intro M hM
    by_contra hnM
    have hg : M ∉ tableBad (nodeMeasureN hn1 wr)
        (fun i g => originalFourErrors (mkR wr (A,0)) i g.val) := fun h => hnM (Or.inl h)
    have hop2 : opN M ≤ lowSecondOperator n := le_of_not_gt (fun h => hnM (Or.inr h))
    apply hM
    intro _
    refine ⟨tableCore_of_second_good hn1 (mkR wr (A,0)) M hg, hA.1.1.1, hop2, ?_⟩
    intro g
    exact variance_lower_low hn (mkR wr (A,M)) hc hA.1.1.2
      (node_geometry_low hn hw (A,M) g.isLt).1 (by exact hs g)
  have hr := (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add hmR (lowSecondOperator_paid hn)))
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hr

theorem table_world_charge {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882) (wr : WRet n) :
    (nuA n).real (tableBadPair n wr) ≤ tableCharge momentCap := by
  by_cases hw : tableWorldGuard wr
  · have h := BstLean.Part252.product_charge_ae _ _ (firstMatrixEvent_measurable hn hw)
      (tableBadPair_measurable wr) (by unfold firstMatrixCharge; positivity)
      (add_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg
        (div_nonneg (momentCap_nonneg i) (tableAllowance_pos i).le) _) (exp_pos _).le)
      (firstMatrixEvent_paid hn hn' hw) (table_conditional_charge hn hw)
    exact h.trans_eq (by unfold firstMatrixCharge tableCharge firstLayerCharge; ring)
  · have he : tableBadPair n wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    unfold tableCharge firstLayerCharge
    exact add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => pow_nonneg
      (div_nonneg (momentCap_nonneg i) (tableAllowance_pos i).le) _)

theorem tableSupplyBand_sharp {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882) :
    (retDist (paperCentres n)).real (tableEvent n)ᶜ < 699108/10^9 := by
  have hm : MeasurableSet {p : WRet n × AHid n | mkR p.1 p.2 ∈ tableEvent n} :=
    tableEvent_measurable.preimage measurable_mkR
  have hq : 0 ≤ tableCharge momentCap := by
    unfold tableCharge firstLayerCharge
    exact add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => pow_nonneg
      (div_nonneg (momentCap_nonneg i) (tableAllowance_pos i).le) _)
  have h := retDist_pair_charge (paperCentres n) hm hq (table_world_charge hn hn')
  have h' : (retDist (paperCentres n)).real (tableEvent n)ᶜ ≤ tableCharge momentCap := by
    convert h using 1
    congr 1
  exact h'.trans_lt tableCharge_cap

theorem tableSupplyBand {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882) :
    MeasurableSet (tableEvent n) ∧
      (retDist (paperCentres n)).real (tableEvent n)ᶜ ≤ 706/10^6 :=
  ⟨tableEvent_measurable, (tableSupplyBand_sharp hn hn').le.trans (by norm_num)⟩

theorem tableSupplyBand_stated {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882) :
    BstLean.Part289.scaleFloor n = 17/100 ∧
    MeasurableSet (tableEvent n) ∧
      (retDist (BstLean.Part289.statedDesign2 n).toCentres).real (tableEvent n)ᶜ ≤ 706/10^6 :=
  ⟨BstLean.Part289.scaleFloor_low (by omega), tableSupplyBand hn hn'⟩

end BstLean.Part292

/-- info: 'BstLean.Part292.tableSupplyBand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.tableSupplyBand
