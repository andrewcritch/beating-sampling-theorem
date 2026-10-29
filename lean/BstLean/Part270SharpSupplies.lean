import BstLean.Part270Bridge
import BstLean.Part280Interface
import BstLean.Part280Cert12224
import BstLean.Part264WorldSource

/-! Use a sharp root certificate with the existing onC44 frame and master.
The smaller source event retains the original base-payment allowance. -/
namespace BstLean.Part270
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part188 BstLean.Part192 BstLean.Part196

theorem old_table_of_sharp {n : ℕ} (hn : 1 ≤ n) {c : Ret n}
    (hw : BstLean.Part161.WINDOW (paperDesignP n) c)
    (hg : BstLean.Part280.m2Guard n c)
    (ht : c ∈ BstLean.Part280.sharpTableN n) :
    c ∈ BstLean.Part262.tableEvent n := by
  have h := ht (BstLean.Part280.tightG_of_window hn c hw hg)
  intro _
  exact ⟨h.1.trans (by norm_num [BstLean.Part276.tableF]),
    h.2.trans (by norm_num [BstLean.Part276.tableW])⟩

theorem old_source_of_sharp {n : ℕ} (hn : 1 ≤ n) {c : Ret n}
    (hw : BstLean.Part161.WINDOW (paperDesignP n) c)
    (hg : BstLean.Part280.m2Guard n c)
    (hc : c ∈ BstLean.Part280.sharpSourceBase n (BstLean.Part280.sharpTableN n)) :
    c ∈ BstLean.Part262.sourceBase n := by
  rw [BstLean.Part262.sourceBase_eq]
  exact ⟨hc.1, old_table_of_sharp hn hw hg hc.2⟩

def fallbackBase (n : ℕ) : Set (Ret n) :=
  BstLean.Part262.sourceBase n ∩ BstLean.Part280.sharpTableN n

theorem fallbackBase_subset (n : ℕ) :
    fallbackBase n ⊆ BstLean.Part262.sourceBase n := fun _ hc => hc.1

theorem fallbackBase_measurable {n : ℕ} (hn : 1 ≤ n) :
    MeasurableSet (fallbackBase n) :=
  (BstLean.Part262.sourceBase_measurable hn).inter
    BstLean.Part280.sharpTableN_measurable

theorem fallbackBase_charge {n : ℕ} (hn : 8000 ≤ n) (H : Set (Ret n))
    (hwindow : ∀ c ∈ H, c ∈ BstLean.Part262.paidSourceBase n →
      BstLean.Part161.WINDOW (paperDesignP n) c ∧ BstLean.Part280.m2Guard n c)
    {tb : ℝ} (htable : (retDist (paperCentres n)).real
      (BstLean.Part280.sharpTableN n)ᶜ ≤ tb) :
    (retDist (paperCentres n)).real (H ∩ (fallbackBase n)ᶜ) ≤
      BstLean.Part275.sourceChargeFn n + tb := by
  have hs : H ∩ (fallbackBase n)ᶜ ⊆
      H ∩ (BstLean.Part280.sharpSourceBase n (BstLean.Part280.sharpTableN n))ᶜ := by
    intro c hc
    refine ⟨hc.1, fun hb => ?_⟩
    have hw := hwindow c hc.1 hb.1
    exact hc.2 ⟨old_source_of_sharp (by omega) hw.1 hw.2 hb, hb.2⟩
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    (BstLean.Part280.sharpSourceBase_charge hn htable H)

noncomputable def fallbackCaps (tb : ℝ) : BstLean.Part275.RootCaps :=
  { BstLean.Part280.m2Caps with tableCharge := tb }

theorem paid_window_of_world {n : ℕ} (hn : 12225 ≤ n)
    {w : WorldParameters} (W : WorldPackage (paperProgram n) w)
    (hhidden : ∀ c ∈ BstLean.Part159.Hof W.hidden,
      c.1.1 ∈ BstLean.Part227.hidden n (44945/10^6) (4/10000) (712/10000)
        (178/10^8) (1232/10^7))
    (hlo : (202225/100000 : ℝ) ≤ BstLean.Part227.productLower n (1232/10^7))
    (hhi : BstLean.Part227.productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    (c : Ret n) (hw : c ∈ BstLean.Part159.Hof W.hidden)
    (hc : c ∈ BstLean.Part262.paidSourceBase n) :
    BstLean.Part161.WINDOW (paperDesignP n) c ∧ BstLean.Part280.m2Guard n c := by
  have ha : c ∈ BstLean.Part262.worldAngles n := hc.1.1.2
  have hg := hhidden c hw
  have hdim : 4096 ≤ n := by omega
  have hθ := BstLean.Part227.noise_window hdim (paperProgram n).design
    rfl (fun _ => rfl) hg.2 hg.1.1.2 hg.1.2
    (BstLean.Part227.window_guards (eB := 1232/10^7) hdim (by norm_num)).1
    (BstLean.Part227.window_guards (eB := 1232/10^7) hdim (by norm_num)).2.1.le
    (BstLean.Part227.window_guards (eB := 1232/10^7) hdim (by norm_num)).2.2
    (by norm_num) hlo hhi ha.1 ha.2
  have hl : (0.47199 : ℝ) ≤ BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) :=
    (le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1
  have hu : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ≤ (0.52358 : ℝ) :=
    hθ.2.trans ((BstLean.Part263.world_upper_le hn).trans (by norm_num))
  have hs : 0 < (paperDesignP n).tau0 c := by
    change 0 < (paperProgram n).design.tau0 c
    rw [W.scale_eq c]
    exact (W.scale_identity c.1.1 hw).1
  refine ⟨BstLean.Part252.window_of_theta (by omega) (paperDesignP n) c hs
    ⟨by linarith, by linarith⟩, ?_⟩
  exact hu.trans (by norm_num)

noncomputable def row_from_sharp_supplies {n : ℕ} (hn : 12225 ≤ n)
    {w : WorldParameters} (W : WorldPackage (paperProgram n) w)
    (a : AgentParameters) (C : MasterCertificate n w a) {r tb : ℝ}
    (K : BstLean.Part280.SharpRootCertificate n r (fallbackCaps tb)
      (BstLean.Part280.sharpTableN n) (BstLean.Part280.m2Guard n))
    (hr : r ≤ a.root)
    (hbasepay : (601 / 10 ^ 6 : ℝ) + tb ≤ 1499145 / 10 ^ 9)
    (event : Set (BstLean.Part160.AgFam n))
    (cell : Fin 60 → Set ℝ) (caps : Fin 60 → ℝ)
    (hmeas : MeasurableSet event)
    (hpay : (retDist (paperCentres n)).real
      (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1/4000 : ℝ))
    (frame : ∀ {hW : ℝ} c, c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (BstLean.Part262.sourceBase n ∩ BstLean.Part259.covarianceGood event)
      (HbarW (paperDesignP n)) hW →
      Nonempty (BstLean.Part259.LocalFrameInputs n event cell caps c a.frame))
    (L : BstLean.Part262.LocalRootSupply n (BstLean.Part159.Hof W.hidden))
    (hwindow : ∀ c ∈ BstLean.Part159.Hof W.hidden,
      c ∈ BstLean.Part262.paidSourceBase n →
      BstLean.Part161.WINDOW (paperDesignP n) c ∧ BstLean.Part280.m2Guard n c)
    (payment : (1499145/10^9 : ℝ)+3/10000 ≤ a.charge)
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
  baseEvent := fallbackBase n
  base_measurable := fallbackBase_measurable (by omega)
  baseCharge := 1499145 / 10 ^ 9
  base_payment := by
    refine (fallbackBase_charge (tb := tb) (by omega) _ hwindow K.table_payment).trans ?_
    have hs : BstLean.Part275.sourceChargeFn n ≤ (601 / 10 ^ 6 : ℝ) := K.source_charge
    linarith only [hs, hbasepay]
  frame := by
    intro c hc
    exact frame c ⟨hc.1, hc.2.1.1, hc.2.2⟩
  root := by
    intro t c hc
    have hp : c ∈ BstLean.Part262.paidSourceBase n := by
      have hb := hc.2.1.1
      rw [BstLean.Part262.sourceBase_eq] at hb
      exact hb.1
    have hw := hwindow c hc.1.1 hp
    have I := L.interfaces c hc.1.1 hc.2.1.1
    have I' : WFInterfaces (paperDesignP n) c (fallbackCaps tb).Mcap
        ((fallbackCaps tb).Hcap n) (fallbackCaps tb).xiCap := by
      refine ⟨BstLean.Part219.directionMoment_mono I.direction ?_, I.energy, I.parallel⟩
      norm_num [fallbackCaps, BstLean.Part280.m2Caps, BstLean.Part275.pilotCaps,
        BstLean.Part275.part262Caps]
    have R := K.inputs t c hw.1 hw.2 ⟨hp, hc.2.1.2⟩ I'
      (L.energy_cap c hc.1.1 hc.2.1.1)
    exact ⟨{
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
      scalar := R.scalar.trans hr }⟩
  payment := payment
  charge_compatible := compatible

end BstLean.Part270
