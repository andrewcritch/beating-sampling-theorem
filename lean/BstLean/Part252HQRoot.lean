import BstLean.Part252HQPacket
import BstLean.Part252TableEvent
import BstLean.Part252PositiveOutput
import BstLean.Part180HQFl

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12225) : Prop :=
  ∫ a, (stdGauss (Fin (12225 - 1))).real
    {v | sgA (paperDesignP 12225) c a v < rowSigma} ∂muI 12225 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12225) : SplitData 12225 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12225)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12225).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12225} (t : ℝ)
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12225)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12225) t c (hqSplit c) (23 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12225) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12225} (hw : WINDOW (paperDesignP 12225) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12225) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12225) c (hqSplit c) ⊆ bulkIx (paperDesignP 12225) c :=
    fun _ h => h.1
  have htab := stored_table_moments c hw hc hK hsub
    (exactTableMoments_of_event hw ht _)
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (sqrt_nonneg _) he bias_floor_ge (by norm_num [epsilon]) bias_threshold_pos
    (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    (pass_centre_of_events c hc)
    (pass_moments_of_events c hw he hc _ htab.1 htab.2)

/-- Only the low-mass inequality remains pointwise; the table payment is a separate obligation. -/
noncomputable def hqRootInputs {c : Ret 12225} (t : ℝ)
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12225))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot where
  split := hqSplit c
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := 0
  mix := 23 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part243.rowRoot] at h ⊢
    linarith

end BstLean.Part252
