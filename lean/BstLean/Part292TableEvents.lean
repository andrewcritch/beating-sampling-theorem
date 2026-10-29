import BstLean.Part292NodeEvent
import BstLean.Part292Operators
import BstLean.Part292TableCore
import BstLean.Part292TraceSupply

/-! Measurable retained table and odd-rule events; no residual last matrix is read. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170 BstLean.Part171
open BstLean.Part152 (opN)
open BstLean.Part153 (measurable_opN_A1)
open BstLean.Part280 (nodeMeasureN nodeMeasureN_mass)

def oddSupply {n : ℕ} (c : Ret n) : Prop :=
  opN (A1 c) ≤ lowOperator n ∧ opN (A2 c) ≤ lowSecondOperator n ∧
    ∀ g : Fin (Js n), (1-nodeS c g.val^2)*lowSigma n^2 ≤ vsig2 c (nodeS c g.val)

theorem oddSupply_measurable {n : ℕ} : MeasurableSet {c : Ret n | oddSupply c} := by
  have h1 : Measurable (fun c : Ret n => A1 c) := by unfold A1; fun_prop
  have h2 : Measurable (fun c : Ret n => A2 c) := by unfold A2; fun_prop
  have hv : MeasurableSet {c : Ret n | ∀ g : Fin (Js n),
      (1-nodeS c g.val^2)*lowSigma n^2 ≤ vsig2 c (nodeS c g.val)} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro g
    exact measurableSet_le
      ((measurable_const.sub ((measurable_nodeS g.val).pow_const 2)).mul_const _)
      (measurable_vsig2_comp measurable_id (measurable_nodeS g.val))
  exact (measurableSet_le (measurable_opN_A1.comp h1) measurable_const).inter
    ((measurableSet_le (measurable_opN_A1.comp h2) measurable_const).inter hv)

def tableEvent (n : ℕ) : Set (Ret n) :=
  {c | tableWorldGuard c.1 → tableCore c ∧ oddSupply c}

theorem tableEvent_retained_only {n : ℕ} (c : Ret n) :
    mkR c.1 c.2.1.1 ∈ tableEvent n ↔ c ∈ tableEvent n := Iff.rfl

theorem tableEvent_measurable {n : ℕ} : MeasurableSet (tableEvent n) := by
  have he : tableEvent n = {c : Ret n | tableWorldGuard c.1}ᶜ ∪
      ({c : Ret n | tableCore c} ∩ {c : Ret n | oddSupply c}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    exact imp_iff_not_or
  rw [he]
  exact (tableWorldGuard_measurable.preimage measurable_fst).compl.union
    (tableCore_measurable.inter oddSupply_measurable)

noncomputable def firstMatrixCharge : ℝ := 2*exp (-18)+2*exp (-12)+1/10000

def firstMatrixEvent {n : ℕ} (hn : 1 ≤ n) (wr : WRet n) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  (({A | opN A ≤ lowOperator n} ∩ traceLow (uHat (mkR wr (0,0)))) ∩
    traceHigh (uHat (mkR wr (0,0)))) ∩
    BstLean.Part239.node416Event wr (nodeMeasureN hn wr) Fin.val (517/200)

theorem firstMatrixEvent_measurable {n : ℕ} (hn : 8000 ≤ n) {wr : WRet n}
    (hw : tableWorldGuard wr) : MeasurableSet (firstMatrixEvent (by omega) wr) := by
  have hc := BstLean.Part172.sg_wr_ne (by omega : 1 ≤ n) hw.1
  have hs (g : Fin (Js n)) : nodeS (mkR wr (0,0)) g.val^2 ≤ 1 := by
    linarith [(node_geometry_low hn hw (0,0) g.isLt).2.1]
  exact (((measurableSet_le measurable_opN_A1 measurable_const).inter (traceLow_measurable _)).inter
    (traceHigh_measurable _)).inter
    (BstLean.Part239.node416Event_measurable (by omega) wr hc _ Fin.val hs (by norm_num))

theorem firstMatrixEvent_paid {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882) {wr : WRet n}
    (hw : tableWorldGuard wr) :
    (gaussMat (mA n) n (2/(n : ℝ))).real (firstMatrixEvent (by omega) wr)ᶜ ≤ firstMatrixCharge := by
  have hc := BstLean.Part172.sg_wr_ne (by omega : 1 ≤ n) hw.1
  have hu : normSq (uHat (mkR wr (0,0))) = 1 := normSq_uHat hc
  have hs (g : Fin (Js n)) : nodeS (mkR wr (0,0)) g.val^2 ≤ 1 := by
    linarith [(node_geometry_low hn hw (0,0) g.isLt).2.1]
  have hstat := node416_charge_band hn hn' wr hc (nodeMeasureN (by omega) wr)
    (nodeMeasureN_mass (by omega) wr).le Fin.val hs
  unfold firstMatrixEvent
  repeat rw [compl_inter]
  have hop : (gaussMat (mA n) n (2/(n : ℝ))).real {A | opN A ≤ lowOperator n}ᶜ ≤ exp (-18) := by
    simpa only [compl_setOf, not_le] using lowOperator_paid hn
  have h := ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add
      ((measureReal_union_le _ _).trans (add_le_add hop (traceLow_paid hn hu)))
      (traceHigh_paid hn hu))) hstat))
  exact h.trans_eq (by unfold firstMatrixCharge; ring)

def tableBadPair (n : ℕ) (wr : WRet n) : Set (AHid n) := {θ | mkR wr θ ∉ tableEvent n}

theorem tableBadPair_measurable {n : ℕ} (wr : WRet n) : MeasurableSet (tableBadPair n wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

end BstLean.Part292
