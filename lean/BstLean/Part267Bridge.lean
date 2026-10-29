import BstLean.Part264Source
import BstLean.Part262ActualInterface
import BstLean.Part259Family

/-! Actual source numerics supply the local interfaces of the actual root. -/
namespace BstLean.Part267
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part188 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)

noncomputable def root_from_sources {n : ℕ} (hn : n ∈ Icc 12225 12349)
    (R : BstLean.Part263.ScalarRow n)
    (N : ∀ {i : Fin 60}, 10 ≤ i.val ∧ i.val ≤ 52 →
      BstLean.Part264.CellSourceNumerics n (R.table i) R.M R.H R.xi)
    (hM : R.M ≤ 91/1000) (hH : R.H ≤ (2101/100)/n) (hxi : R.xi ≤ 4/100)
    (hE : ∀ i : Fin 60, 10 ≤ i.val ∧ i.val ≤ 52 → (R.table i).energy ≤ 702/1000)
    {root : ℝ} (C : BstLean.Part262.ActualRootCertificate n root)
    (t : ℝ) (c : Ret n)
    (hw : c ∈ BstLean.Part159.Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) : BstLean.Part243.RootInputs n t c root := by
  let i := Classical.choose (BstLean.Part264.local_cell hn R hw hc)
  have hi := (Classical.choose_spec (BstLean.Part264.local_cell hn R hw hc)).1
  have hm := (Classical.choose_spec (BstLean.Part264.local_cell hn R hw hc)).2
  have F := BstLean.Part264.network_from_numerics hn (N hi)
    (BstLean.Part263.scalarRow_cell_subset R i hm) hw hc
  have I : WFInterfaces (paperDesignP n) c (91/1000) ((2101/100)/n) (4/100) := by
    refine ⟨BstLean.Part219.directionMoment_mono F.interfaces.direction hM, ?_, ?_⟩
    · exact ⟨by positivity, F.interfaces.energy.2.1,
        F.interfaces.energy.2.2.trans (pow_le_pow_left₀ F.interfaces.energy.1 hH 32)⟩
    · refine ⟨by norm_num, F.interfaces.parallel.2.trans ?_⟩
      exact sqrt_le_sqrt (div_le_div_of_nonneg_right hxi (Nat.cast_nonneg n))
  exact C.inputs t c (BstLean.Part264.source_window hn hw hc) hc I
    (F.centre_energy.trans (hE i hi))

noncomputable def row_from_supplies {n : ℕ} (hn : n ∈ Icc 12225 12349)
    (a : AgentParameters) (C : MasterCertificate n (BstLean.Part260.worldParameters n) a)
    (K : BstLean.Part262.ActualRootCertificate n a.root)
    (event : Set (BstLean.Part160.AgFam n)) (cell : Fin 60 → Set ℝ) (caps : Fin 60 → ℝ)
    (hmeas : MeasurableSet event)
    (hpay : (retDist (paperCentres n)).real
      (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1/4000 : ℝ))
    (frame : ∀ {hW : ℝ} c, c ∈ goodSet
      (BstLean.Part159.Hof (BstLean.Part260.worldPackage n hn).hidden)
      (BstLean.Part262.sourceBase n ∩ BstLean.Part259.covarianceGood event)
      (HbarW (paperDesignP n)) hW →
      Nonempty (BstLean.Part259.LocalFrameInputs n event cell caps c a.frame))
    (root : ∀ t c, c ∈ BstLean.Part159.Hof (BstLean.Part260.worldPackage n hn).hidden →
      c ∈ BstLean.Part262.sourceBase n → Nonempty (BstLean.Part243.RootInputs n t c a.root))
    (payment : (1499145/10^9 : ℝ)+3/10000 ≤ a.charge)
    (compatible : a.charge ≤ C.retainedCharge) : BstLean.Part259.RowInputs n where
  dimension := by have := hn.1; omega
  worldParameters := BstLean.Part260.worldParameters n
  agentParameters := a
  world := BstLean.Part260.worldPackage n hn
  certificate := C
  covarianceEvent := event
  cell := cell
  caps := caps
  covariance_measurable := hmeas
  covariance_payment := hpay
  baseEvent := BstLean.Part262.sourceBase n
  base_measurable := BstLean.Part262.sourceBase_measurable (by have := hn.1; omega)
  baseCharge := 1499145/10^9
  base_payment := (BstLean.Part262.sourceBase_charge K.dimension K.table_payment _).trans (by norm_num)
  frame := fun c hc => frame c hc
  root := fun t c hc => root t c hc.1.1 hc.2.1
  payment := payment
  charge_compatible := compatible

end BstLean.Part267
