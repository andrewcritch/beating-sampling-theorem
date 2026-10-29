import BstLean.Part285IntervalResult
import BstLean.Part270SharpSupplies
import BstLean.Part270StatedSubsetBridge

/-! Part 285 interval roots in the interfaces used by row assembly.
The local supplies concern the retained network. The root and its sharp table
payment come from the interval certificates, with no per-row proof data. -/
namespace BstLean.Part285.Downstream
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part192 BstLean.Part196
open BstLean.Part280 BstLean.Part285.Interval

/-- The band root on every dimension in the downstream range. -/
noncomputable def bandRootInputs {n : ℕ} (hn : 13225 ≤ n) (hu : n ≤ 16199)
    (t : ℝ) (c : Ret n) (hw : WINDOW (paperDesignP n) c)
    (hg : m2Guard n c) (hc : c ∈ sharpSourceBase n (sharpTableN n))
    (I : WFInterfaces (paperDesignP n) c (912 / 10000) ((2101 / 100) / n) (4 / 100))
    (hE : centreEnergy (paperDesignP n) c ≤ 702 / 1000) :
    BstLean.Part243.RootInputs n t c (rootOnBand n) :=
  (sharpCertificate (by omega) hu).inputs t c hw hg hc I hE

/-- A larger root allowance preserves all analytic fields. -/
noncomputable def enlargeRoot {n : ℕ} {t r s : ℝ} {c : Ret n}
    (R : BstLean.Part243.RootInputs n t c r) (hrs : r ≤ s) :
    BstLean.Part243.RootInputs n t c s where
  split := R.split
  chi := R.chi
  biasFloor := R.biasFloor
  epsilon := R.epsilon
  vmax := R.vmax
  aw := R.aw
  af := R.af
  Hf := R.Hf
  Cv := R.Cv
  B := R.B
  mix := R.mix
  displacement := R.displacement
  window := R.window
  passes := R.passes
  fluctuation := R.fluctuation
  scalar := R.scalar.trans hrs

/-- The exact paid World window needed by the sharp-table route. -/
def PaidWindow (n : ℕ) (H : Set (Ret n)) : Prop :=
  ∀ c ∈ H, c ∈ BstLean.Part262.paidSourceBase n →
    WINDOW (paperDesignP n) c ∧ m2Guard n c

/-- Reuse the local supply produced by Part 286 on the sharp source event. -/
theorem sharpLocalSupply {n : ℕ} (hn : 13225 ≤ n) {H : Set (Ret n)}
    (L : BstLean.Part262.LocalRootSupply n H) (hw : PaidWindow n H) (tb : ℝ) :
    SharpLocalSupply n (intervalCaps tb) (sharpTableN n) (m2Guard n) H := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hH hc
    exact (hw c hH hc.1).1
  · intro c hH hc
    exact (hw c hH hc.1).2
  · intro c hH hc
    have hwin := hw c hH hc.1
    have hold := BstLean.Part270.old_source_of_sharp (by omega) hwin.1 hwin.2 hc
    have I := L.interfaces c hH hold
    refine ⟨BstLean.Part219.directionMoment_mono I.direction ?_, I.energy, I.parallel⟩
    norm_num [intervalCaps, m2Caps, BstLean.Part275.pilotCaps, BstLean.Part275.part262Caps]
  · intro c hH hc
    have hwin := hw c hH hc.1
    exact L.energy_cap c hH
      (BstLean.Part270.old_source_of_sharp (by omega) hwin.1 hwin.2 hc)

/-- A paid root supply at the band price, ready for a general row constructor. -/
noncomputable def bandBaseRootSupply {n : ℕ} (hn : 13225 ≤ n) (hu : n ≤ 16199)
    (H : Set (Ret n)) (L : BstLean.Part262.LocalRootSupply n H)
    (hw : PaidWindow n H) :
    BstLean.Part262.BaseRootSupply n H (rootOnBand n)
      (601 / 10 ^ 6 + capOnBand n) :=
  sharpBaseRootSupply (sharpCertificate (by omega) hu) H
    (sharpLocalSupply hn L hw _)

/-- The same root supply with the smaller table price at the actual dimension. -/
noncomputable def perNBaseRootSupply {n : ℕ} (hn : 13225 ≤ n) (hu : n ≤ 16199)
    (H : Set (Ret n)) (L : BstLean.Part262.LocalRootSupply n H)
    (hw : PaidWindow n H) :
    BstLean.Part262.BaseRootSupply n H (rootOnBand n)
      (601 / 10 ^ 6 + smallerTablePrice n) :=
  sharpBaseRootSupply (sharpCertificate_per_n (by omega) hu) H
    (sharpLocalSupply hn L hw _)

/-- Assemble a Part 259 row from the existing World, frame and local-source supplies.
The source event is a subset of the original event, and the charge uses the sharp price. -/
noncomputable def row_from_sharp_supplies {n : ℕ} (hn : 13225 ≤ n)
    {w : WorldParameters} (W : WorldPackage (paperProgram n) w)
    (a : AgentParameters) (C : MasterCertificate n w a) {r tb : ℝ}
    (K : SharpRootCertificate n r (intervalCaps tb) (sharpTableN n) (m2Guard n))
    (hr : r ≤ a.root)
    (event : Set (BstLean.Part160.AgFam n))
    (cell : Fin 60 → Set ℝ) (caps : Fin 60 → ℝ)
    (hmeas : MeasurableSet event)
    (hpay : (retDist (paperCentres n)).real
      (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ))
    (frame : ∀ {hW : ℝ} c, c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (BstLean.Part262.sourceBase n ∩ BstLean.Part259.covarianceGood event)
      (HbarW (paperDesignP n)) hW →
      Nonempty (BstLean.Part259.LocalFrameInputs n event cell caps c a.frame))
    (L : BstLean.Part262.LocalRootSupply n (BstLean.Part159.Hof W.hidden))
    (hw : PaidWindow n (BstLean.Part159.Hof W.hidden))
    (payment : (601 / 10 ^ 6 : ℝ) + tb + 3 / 10000 ≤ a.charge)
    (compatible : a.charge ≤ C.retainedCharge) : BstLean.Part259.RowInputs n where
  dimension := by omega
  worldParameters := w
  agentParameters := a
  world := W
  certificate := C
  covarianceEvent := event
  cell := cell
  caps := caps
  covariance_measurable := hmeas
  covariance_payment := hpay
  baseEvent := BstLean.Part270.fallbackBase n
  base_measurable := BstLean.Part270.fallbackBase_measurable (by omega)
  baseCharge := 601 / 10 ^ 6 + tb
  base_payment := by
    refine (BstLean.Part270.fallbackBase_charge (by omega) _ hw K.table_payment).trans ?_
    have hs : BstLean.Part275.sourceChargeFn n ≤ (601 / 10 ^ 6 : ℝ) := K.source_charge
    change BstLean.Part275.sourceChargeFn n + tb ≤ 601 / 10 ^ 6 + tb
    linarith only [hs]
  frame := by
    intro c hc
    exact frame c ⟨hc.1, hc.2.1.1, hc.2.2⟩
  root := by
    intro t c hc
    have hp : c ∈ BstLean.Part262.paidSourceBase n := by
      have hb := hc.2.1.1
      rw [BstLean.Part262.sourceBase_eq] at hb
      exact hb.1
    have S := sharpLocalSupply hn L hw tb
    have hb : c ∈ sharpSourceBase n (sharpTableN n) := ⟨hp, hc.2.1.2⟩
    exact ⟨enlargeRoot (K.inputs t c (S.window c hc.1.1 hb)
      (S.guard c hc.1.1 hb) hb (S.interfaces c hc.1.1 hb)
      (S.energy_cap c hc.1.1 hb)) hr⟩
  payment := payment
  charge_compatible := compatible

/-- Row assembly with the band root and band table price. The remaining arguments
are the covariance event, cells, frame, local supply, paid window, and ledger bounds. -/
noncomputable def row_from_band_supplies {n : ℕ} (hn : 13225 ≤ n) (hu : n ≤ 16199)
    {w : WorldParameters} (W : WorldPackage (paperProgram n) w)
    (a : AgentParameters) (C : MasterCertificate n w a) (hr : rootOnBand n ≤ a.root) :=
  row_from_sharp_supplies hn W a C (sharpCertificate (by omega) hu) hr

/-- Row assembly with the band root and the smaller per-dimension table price. -/
noncomputable def row_from_per_n_supplies {n : ℕ} (hn : 13225 ≤ n) (hu : n ≤ 16199)
    {w : WorldParameters} (W : WorldPackage (paperProgram n) w)
    (a : AgentParameters) (C : MasterCertificate n w a) (hr : rootOnBand n ≤ a.root) :=
  row_from_sharp_supplies hn W a C (sharpCertificate_per_n (by omega) hu) hr

/-- The root-input theorem, including the band's bottom-row requirement. -/
theorem root_inputs_on_interval {n : ℕ} (hn : 13225 ≤ n) (hu : n ≤ 16199)
    (t : ℝ) (c : Ret n) (hw : WINDOW (paperDesignP n) c)
    (hg : m2Guard n c) (hc : c ∈ sharpSourceBase n (sharpTableN n))
    (I : WFInterfaces (paperDesignP n) c (912 / 10000) ((2101 / 100) / n) (4 / 100))
    (hE : centreEnergy (paperDesignP n) c ≤ 702 / 1000) :
    rootOnBand n ≤ requirementOnBand n ∧
      Nonempty (BstLean.Part243.RootInputs n t c (rootOnBand n)) :=
  ⟨rootOnBand_le_requirement n (by omega) hu, ⟨bandRootInputs hn hu t c hw hg hc I hE⟩⟩

/-- The first downstream band has the largest selected root. -/
theorem rootOnBand_le_first {n : ℕ} (hn : 13225 ≤ n) :
    rootOnBand n ≤ Band13225.root := by
  by_cases h0 : n ≤ 13524
  · rw [(select13225 hn h0).1]
  by_cases h1 : n ≤ 13824
  · rw [(select13525 (by omega) h1).1]
    norm_num [Band13525.root, Band13225.root]
  by_cases h2 : n ≤ 14124
  · rw [(select13825 (by omega) h2).1]
    norm_num [Band13825.root, Band13225.root]
  by_cases h3 : n ≤ 14424
  · rw [(select14125 (by omega) h3).1]
    norm_num [Band14125.root, Band13225.root]
  by_cases h4 : n ≤ 14724
  · rw [(select14425 (by omega) h4).1]
    norm_num [Band14425.root, Band13225.root]
  by_cases h5 : n ≤ 15024
  · rw [(select14725 (by omega) h5).1]
    norm_num [Band14725.root, Band13225.root]
  by_cases h6 : n ≤ 15324
  · rw [(select15025 (by omega) h6).1]
    norm_num [Band15025.root, Band13225.root]
  by_cases h7 : n ≤ 15624
  · rw [(select15325 (by omega) h7).1]
    norm_num [Band15325.root, Band13225.root]
  by_cases h8 : n ≤ 15924
  · rw [(select15625 (by omega) h8).1]
    norm_num [Band15625.root, Band13225.root]
  have hlast : rootOnBand n = Band15925.root := by
    have e0 : ¬ n ≤ 12224 := by omega
    have e1 : ¬ n ≤ 12524 := by omega
    have e2 : ¬ n ≤ 12824 := by omega
    have e3 : ¬ n ≤ 13124 := by omega
    have e4 : ¬ n ≤ 13224 := by omega
    have e5 : ¬ n ≤ 13524 := by omega
    have e6 : ¬ n ≤ 13824 := by omega
    have e7 : ¬ n ≤ 14124 := by omega
    have e8 : ¬ n ≤ 14424 := by omega
    have e9 : ¬ n ≤ 14724 := by omega
    have e10 : ¬ n ≤ 15024 := by omega
    have e11 : ¬ n ≤ 15324 := by omega
    have e12 : ¬ n ≤ 15624 := by omega
    have e13 : ¬ n ≤ 15924 := by omega
    simp only [rootOnBand, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6, if_neg e7, if_neg e8, if_neg e9, if_neg e10, if_neg e11, if_neg e12, if_neg e13]
  rw [hlast]
  norm_num [Band15925.root, Band13225.root]

/-- A uniform upper bound for the smaller table price on the downstream interval. -/
theorem smallerTablePrice_le_5602 {n : ℕ} (hn : 13225 ≤ n) :
    smallerTablePrice n ≤ (5602 / 10 ^ 7 : ℝ) := by
  refine (smallerTablePrice_le_band n).trans ?_
  unfold bandTablePrice
  split_ifs <;> first | omega | norm_num

/-- The full retained charge fits the proposed uniform-master allowance .0015. -/
theorem retainedCharge_le_1500 {n : ℕ} (hn : 13225 ≤ n) :
    (601 / 10 ^ 6 : ℝ) + smallerTablePrice n + 3 / 10000 ≤ 3 / 2000 := by
  have h := smallerTablePrice_le_5602 hn
  linarith only [h]

/-- The Part 286 stated-program transfer with a subset base event, for both parities. -/
theorem stated_from_row {n : ℕ} (R : BstLean.Part259.RowInputs n) (hn : 13225 ≤ n)
    (hbase : R.baseEvent ⊆ BstLean.Part262.sourceBase n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  rcases Nat.even_or_odd n with he | ho
  · rw [BstLean.Part272.statedDesign_even (by omega) he]
    exact BstLean.Part259.classifier_from_row R t
  · refine BstLean.Part278.classifier_from_row_st R t
      (BstLean.Part278.oddRoot_row R (by omega) ho t (fun c hc => ?_))
    exact BstLean.Part270.sourceBase_three_events (hbase hc)

/-- The paid window follows from the standard variant-E hidden event and product bounds. -/
theorem paidWindow_of_world {n : ℕ} (hn : 13225 ≤ n)
    {w : WorldParameters} (W : WorldPackage (paperProgram n) w)
    (hhidden : ∀ c ∈ BstLean.Part159.Hof W.hidden,
      c.1.1 ∈ BstLean.Part227.hidden n (44945 / 10 ^ 6) (4 / 10000) (712 / 10000)
        (178 / 10 ^ 8) (1232 / 10 ^ 7))
    (hlo : (202225 / 100000 : ℝ) ≤ BstLean.Part227.productLower n (1232 / 10 ^ 7))
    (hhi : BstLean.Part227.productUpper n (1232 / 10 ^ 7) ≤ (202831 / 100000 : ℝ)) :
    PaidWindow n (BstLean.Part159.Hof W.hidden) :=
  BstLean.Part270.paid_window_of_world (by omega) W hhidden hlo hhi

end BstLean.Part285.Downstream
