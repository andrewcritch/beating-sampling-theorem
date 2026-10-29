import BstLean.Part280Interface
import BstLean.Part275Actual12224
import BstLean.Part276Root
import BstLean.Part276World

/-! Part 280, task 1: the sharp root at n = 12224 without caller supplies.

The Part 276 object `Row12224.rootInputs` needs a `SharpRootSource`. This file supplies
every field from the Part 275 pilot:
* window, energy, output centre, `Eop`, `Eop2`, `vmax`, `Hf`, `Cv`: the pilot pass event
  inside the analytic base;
* the energy and location errors: the Part 276 sharp table event (aw = .15923,
  af = .05415);
* the removal, mixture and displacement terms: the pilot HQ route (`B = 0`,
  mixture root .0024, displacement 0) with the pilot low-mass bound.
The root is .0024 + .004072 + 1e-8 + 1e-20 ≤ .0074488 (the stored chain48q16 root). -/
namespace BstLean.Part280.Row12224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable abbrev P5 := BstLean.Part275.Row12224.hqSplit
noncomputable abbrev sharpAw : ℝ := BstLean.Part276.Row12224.sharpAw
noncomputable abbrev sharpAf : ℝ := BstLean.Part276.Row12224.sharpAf

/-- The stored chain48q16 root at 12224, rounded up. -/
noncomputable def rootTarget : ℝ := 74488 / 10 ^ 7

theorem sharp_squared_price :
    BstLean.Part241.squaredPrice 12224 BstLean.Part275.Row12224.chi
      BstLean.Part275.Row12224.biasFloor BstLean.Part275.Row12224.epsilon
      BstLean.Part275.Row12224.varianceMax sharpAw sharpAf
      BstLean.Part275.Row12224.locationNorm BstLean.Part275.Row12224.varianceNorm ≤
      (4072 / 10 ^ 6 : ℝ) ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass,
    BstLean.Part275.Row12224.chi, BstLean.Part275.Row12224.biasFloor,
    BstLean.Part275.Row12224.epsilon, BstLean.Part275.Row12224.varianceMax,
    sharpAw, sharpAf, BstLean.Part276.Row12224.sharpAw, BstLean.Part276.Row12224.sharpAf,
    BstLean.Part275.Row12224.locationNorm, BstLean.Part275.Row12224.varianceNorm,
    BstLean.Part275.Row12224.eta, BstLean.Part275.Row12224.mixtureFloor]

theorem sharp_bias_root :
    BstLean.Part241.biasRoot 12224 BstLean.Part275.Row12224.chi
      BstLean.Part275.Row12224.biasFloor BstLean.Part275.Row12224.epsilon
      BstLean.Part275.Row12224.varianceMax sharpAw sharpAf
      BstLean.Part275.Row12224.locationNorm BstLean.Part275.Row12224.varianceNorm ≤
      4072 / 10 ^ 6 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, sharp_squared_price⟩

/-- The pass inputs of the HQ split with the sharp energy and location errors. -/
theorem sharp_hq_passes {c : Ret 12224} (hw : WINDOW (paperDesignP 12224) c)
    (ha : c ∈ BstLean.Part275.Row12224.analyticBase)
    (hX : ∀ K, BstLean.Part276.Row12224.ExactTableMoments c K) :
    BstLean.Part241.PassInputs c (P5 c) BstLean.Part275.Row12224.chi
      BstLean.Part275.Row12224.biasFloor BstLean.Part275.Row12224.epsilon
      BstLean.Part275.Row12224.varianceMax sharpAw sharpAf
      BstLean.Part275.Row12224.locationNorm BstLean.Part275.Row12224.varianceNorm := by
  have he : 0 < eR c := by
    linarith [(BstLean.Part275.Row12224.centre_energy_range hw ha).1]
  have hc := BstLean.Part275.Row12224.analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12224) c (P5 c)) :=
    measurableSet_keptSet _ (P5 c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12224) c (P5 c) ⊆ bulkIx (paperDesignP 12224) c :=
    fun _ h => h.1
  have hfirst : A1 c ∈ BstLean.Part153.Eop 12224 := hc.1.1.2 hw.2.1
  have hsecond : c ∈ BstLean.Part164.Eop2 12224 := hc.1.2
  have htab := BstLean.Part276.Row12224.stored_table_moments c hw hfirst hsecond hK hsub
    (hX _)
  have hw8 : sharpAw ^ 8 ≤ BstLean.Part275.Row12224.energyError ^ 8 :=
    pow_le_pow_left₀ (by norm_num [sharpAw, BstLean.Part276.Row12224.sharpAw])
      (by norm_num [sharpAw, BstLean.Part276.Row12224.sharpAw,
        BstLean.Part275.Row12224.energyError]) 8
  have hf8 : sharpAf ^ 8 ≤ BstLean.Part275.Row12224.locationError ^ 8 :=
    pow_le_pow_left₀ (by norm_num [sharpAf, BstLean.Part276.Row12224.sharpAf])
      (by norm_num [sharpAf, BstLean.Part276.Row12224.sharpAf,
        BstLean.Part275.Row12224.locationError]) 8
  have hpm := BstLean.Part275.Row12224.pass_moments_of_events c hw he hc _
    (htab.1.trans hw8) (htab.2.trans hf8)
  have hm : PaperMoments c (keptIx (paperDesignP 12224) c (P5 c))
      BstLean.Part275.Row12224.varianceMax sharpAw sharpAf
      BstLean.Part275.Row12224.locationNorm BstLean.Part275.Row12224.varianceNorm :=
    ⟨hpm.variance, htab.1, htab.2, hpm.location4, hpm.location24, hpm.variance2⟩
  exact passInputs_of_paperMoments (by norm_num) c BstLean.Part275.Row12224.eta_pos
    BstLean.Part275.Row12224.eta_lt_one (sqrt_nonneg _) he
    BstLean.Part275.Row12224.bias_floor_ge
    (by norm_num [BstLean.Part275.Row12224.epsilon])
    BstLean.Part275.Row12224.bias_threshold_pos
    (by norm_num [sharpAw, BstLean.Part276.Row12224.sharpAw])
    (by norm_num [sharpAf, BstLean.Part276.Row12224.sharpAf])
    (by norm_num [BstLean.Part275.Row12224.locationNorm])
    (by norm_num [BstLean.Part275.Row12224.varianceNorm])
    BstLean.Part275.Row12224.row_split_floor.le
    (BstLean.Part275.Row12224.pass_centre_of_events c hc) hm

/-- `RootInputs` at 12224 with root .0074488 from membership and the low-mass bound. -/
noncomputable def sharpRootInputs {c : Ret 12224} (t : ℝ)
    (hw : WINDOW (paperDesignP 12224) c) (ha : c ∈ BstLean.Part275.Row12224.analyticBase)
    (hX : ∀ K, BstLean.Part276.Row12224.ExactTableMoments c K)
    (hp : c ∈ BstLean.Part252.positiveOutputEvent (paperCentres 12224))
    (hm : BstLean.Part275.Row12224.LowResidualMass c) :
    BstLean.Part243.RootInputs 12224 t c rootTarget where
  split := P5 c
  chi := BstLean.Part275.Row12224.chi
  biasFloor := BstLean.Part275.Row12224.biasFloor
  epsilon := BstLean.Part275.Row12224.epsilon
  vmax := BstLean.Part275.Row12224.varianceMax
  aw := sharpAw
  af := sharpAf
  Hf := BstLean.Part275.Row12224.locationNorm
  Cv := BstLean.Part275.Row12224.varianceNorm
  B := 0
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := sharp_hq_passes hw ha hX
  fluctuation := by simpa using BstLean.Part275.Row12224.hq_fluctuation t hw ha hp hm
  scalar := by
    have h := sharp_bias_root
    norm_num [rootTarget] at h ⊢
    linarith

end BstLean.Part280.Row12224

namespace BstLean.Part280
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188
open BstLean.Part275

/-- The M2 caps at 12224: the pilot caps (direction cap .0912, low-mass budget 4e-12)
with the sharp table charge 9/10000. -/
noncomputable def sharpCaps12224 : RootCaps := pilotCaps

/-- Task 1: the sharp root certificate at 12224, root .0074488, table event of Part 276
(guard θ ≤ .54, payment ≤ 9/10000), no row guard. -/
noncomputable def sharpCertificate12224 :
    SharpRootCertificate 12224 Row12224.rootTarget sharpCaps12224
      BstLean.Part276.sharpTable (fun _ => True) where
  dimension := by norm_num
  table_measurable := BstLean.Part276.sharpTable_measurable
  source_charge := sourceChargeFn_le_part262 (le_refl _)
  table_payment := by
    change _ ≤ (9 / 10000 : ℝ)
    exact BstLean.Part276.sharpTable_ret_charge
  inputs := by
    intro t c hw _ hc I hE
    have ha : c ∈ BstLean.Part275.Row12224.analyticBase := hc.1.1.1
    have hp : c ∈ BstLean.Part252.positiveOutputEvent (paperCentres 12224) := hc.1.1.2
    have he : 0 < eR c := by
      linarith [(BstLean.Part275.Row12224.centre_energy_range hw ha).1]
    have hm := low_mass_of_interfacesP (by norm_num) pilot_lowMass hw he I hE
    exact Row12224.sharpRootInputs t hw ha
      (BstLean.Part276.Row12224.exactTableMoments_of_sharp hw hc.2) hp hm

/-- Acceptance (task 1): `RootInputs 12224 t c .0074488` on the sharp source base, for
every local interface value at the pilot caps. -/
noncomputable def sharp_rootInputs12224 (t : ℝ) (c : Ret 12224)
    (hw : WINDOW (paperDesignP 12224) c)
    (hc : c ∈ sharpSourceBase 12224 BstLean.Part276.sharpTable)
    (I : WFInterfaces (paperDesignP 12224) c (912 / 10000) ((2101 / 100) / (12224 : ℕ))
      (4 / 100))
    (hE : centreEnergy (paperDesignP 12224) c ≤ 702 / 1000) :
    BstLean.Part243.RootInputs 12224 t c (74488 / 10 ^ 7) :=
  sharpCertificate12224.inputs t c hw trivial hc I hE

/-- The payment of the sharp source base at 12224: .000599145 + .0009. -/
theorem sharp_payment12224 (H : Set (Ret 12224)) :
    (retDist (paperCentres 12224)).real
      (H ∩ (sharpSourceBase 12224 BstLean.Part276.sharpTable)ᶜ) ≤ 1499145 / 10 ^ 9 := by
  have h := payment_of_sharp sharpCertificate12224 H
  have hc : sharpCaps12224.sourceCharge + sharpCaps12224.tableCharge = 1499145 / 10 ^ 9 := by
    norm_num [sharpCaps12224, pilotCaps, part262Caps]
  linarith

end BstLean.Part280
