import BstLean.Part262ActualShard3Step3


/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12300
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12300) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12300) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12300} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12300) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12300} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12300} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12300 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12300 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12300} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12300) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12300 - 1))).real
      {v | sgA (paperDesignP 12300) c a v < rowSigma} ∂BstLean.Part161.muI 12300 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12300 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12300 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12300 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12300

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12300
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12300) : Prop :=
  ∫ a, (stdGauss (Fin (12300 - 1))).real
    {v | sgA (paperDesignP 12300) c a v < rowSigma} ∂muI 12300 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12300) : SplitData 12300 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12300}
    (hw : WINDOW (paperDesignP 12300) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12300)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12300).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12300} (t : ℝ)
    (hw : WINDOW (paperDesignP 12300) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12300)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12300) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12300) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12300} (hw : WINDOW (paperDesignP 12300) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12300) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12300) c (hqSplit c) ⊆ bulkIx (paperDesignP 12300) c :=
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
noncomputable def hqRootInputs {c : Ret 12300} (t : ℝ)
    (hw : WINDOW (paperDesignP 12300) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12300))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12300 t c BstLean.Part259.agent12300.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12300] at h ⊢
    linarith

end BstLean.Part262.Row12300

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12300
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12300) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12300) c (rowSplit c wl ws),
    ((12300 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12300 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12300) c (rowSplit c wl ws),
    ((12300 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12300 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12300 - 1)))
    (rowSplit c wl ws).good a ∂muI 12300 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12300) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12300 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12300) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12300 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12300) c (rowSplit c wl ws),
    hellG2 12300 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12300 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12300}
    (hw : WINDOW (paperDesignP 12300) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12300}
    (hw : WINDOW (paperDesignP 12300) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12300 t c BstLean.Part259.agent12300.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12300

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12300
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12300) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12300)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12300)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12300)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12300)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12300)

theorem paidBaseCertificate (H : Set (Ret 12300)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12300

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12300
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12300) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12300)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12300)} (h : TablePayment H) :
    (retDist (paperCentres 12300)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12300))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12300} (t : ℝ)
    (hw : WINDOW (paperDesignP 12300) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12300 t c BstLean.Part259.agent12300.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12300

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12300
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12300) (a : Ix 12300) : Fin (Js 12300) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12300) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12300) : Measure (Fin (Js 12300)) :=
  (muI 12300).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12300) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12300) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12300) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12300)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12300) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12300)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12300)
    (M : Matrix (Fin (mA 12300)) (Fin (mA 12300)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12300) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12300) (mA 12300) (tA 12300) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12300) (mA 12300) (tA 12300)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12300) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12300

/-! A first-layer variance payment from dimension 12300. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12300
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12300} (hw : windowW wr)
    (θ : AHid 12300) {g : ℕ} (hg : g < Js 12300) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12300 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12300 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12300 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12300 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12300 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12300 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12300)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12300} (hw : windowW wr) :
    (gaussMat (mA 12300) 12300 (2 / (12300 : ℝ))).real {X | ∃ g < Js 12300,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12300 : ℝ)) ∨
      42 / (10 * (12300 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12300

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12301
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12301) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12301) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12301} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12301) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12301} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12301} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12301 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12301 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12301} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12301) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12301 - 1))).real
      {v | sgA (paperDesignP 12301) c a v < rowSigma} ∂BstLean.Part161.muI 12301 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12301 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12301 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12301 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12301

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12301
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12301) : Prop :=
  ∫ a, (stdGauss (Fin (12301 - 1))).real
    {v | sgA (paperDesignP 12301) c a v < rowSigma} ∂muI 12301 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12301) : SplitData 12301 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12301}
    (hw : WINDOW (paperDesignP 12301) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12301)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12301).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12301} (t : ℝ)
    (hw : WINDOW (paperDesignP 12301) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12301)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12301) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12301) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12301} (hw : WINDOW (paperDesignP 12301) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12301) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12301) c (hqSplit c) ⊆ bulkIx (paperDesignP 12301) c :=
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
noncomputable def hqRootInputs {c : Ret 12301} (t : ℝ)
    (hw : WINDOW (paperDesignP 12301) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12301))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12301 t c BstLean.Part259.agent12301.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12301] at h ⊢
    linarith

end BstLean.Part262.Row12301

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12301
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12301) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12301) c (rowSplit c wl ws),
    ((12301 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12301 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12301) c (rowSplit c wl ws),
    ((12301 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12301 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12301 - 1)))
    (rowSplit c wl ws).good a ∂muI 12301 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12301) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12301 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12301) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12301 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12301) c (rowSplit c wl ws),
    hellG2 12301 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12301 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12301}
    (hw : WINDOW (paperDesignP 12301) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12301}
    (hw : WINDOW (paperDesignP 12301) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12301 t c BstLean.Part259.agent12301.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12301

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12301
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12301) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12301)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12301)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12301)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12301)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12301)

theorem paidBaseCertificate (H : Set (Ret 12301)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12301

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12301
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12301) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12301)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12301)} (h : TablePayment H) :
    (retDist (paperCentres 12301)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12301))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12301} (t : ℝ)
    (hw : WINDOW (paperDesignP 12301) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12301 t c BstLean.Part259.agent12301.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12301

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12301
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12301) (a : Ix 12301) : Fin (Js 12301) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12301) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12301) : Measure (Fin (Js 12301)) :=
  (muI 12301).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12301) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12301) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12301) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12301)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12301) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12301)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12301)
    (M : Matrix (Fin (mA 12301)) (Fin (mA 12301)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12301) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12301) (mA 12301) (tA 12301) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12301) (mA 12301) (tA 12301)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12301) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12301

/-! A first-layer variance payment from dimension 12301. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12301
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12301} (hw : windowW wr)
    (θ : AHid 12301) {g : ℕ} (hg : g < Js 12301) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12301 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12301 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12301 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12301 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12301 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12301 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12301)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12301} (hw : windowW wr) :
    (gaussMat (mA 12301) 12301 (2 / (12301 : ℝ))).real {X | ∃ g < Js 12301,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12301 : ℝ)) ∨
      42 / (10 * (12301 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12301

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12302
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12302) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12302) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12302} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12302) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12302} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12302} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12302 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12302 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12302} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12302) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12302 - 1))).real
      {v | sgA (paperDesignP 12302) c a v < rowSigma} ∂BstLean.Part161.muI 12302 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12302 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12302 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12302 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12302

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12302
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12302) : Prop :=
  ∫ a, (stdGauss (Fin (12302 - 1))).real
    {v | sgA (paperDesignP 12302) c a v < rowSigma} ∂muI 12302 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12302) : SplitData 12302 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12302}
    (hw : WINDOW (paperDesignP 12302) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12302)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12302).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12302} (t : ℝ)
    (hw : WINDOW (paperDesignP 12302) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12302)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12302) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12302) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12302} (hw : WINDOW (paperDesignP 12302) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12302) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12302) c (hqSplit c) ⊆ bulkIx (paperDesignP 12302) c :=
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
noncomputable def hqRootInputs {c : Ret 12302} (t : ℝ)
    (hw : WINDOW (paperDesignP 12302) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12302))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12302 t c BstLean.Part259.agent12302.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12302] at h ⊢
    linarith

end BstLean.Part262.Row12302

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12302
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12302) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12302) c (rowSplit c wl ws),
    ((12302 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12302 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12302) c (rowSplit c wl ws),
    ((12302 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12302 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12302 - 1)))
    (rowSplit c wl ws).good a ∂muI 12302 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12302) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12302 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12302) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12302 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12302) c (rowSplit c wl ws),
    hellG2 12302 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12302 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12302}
    (hw : WINDOW (paperDesignP 12302) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12302}
    (hw : WINDOW (paperDesignP 12302) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12302 t c BstLean.Part259.agent12302.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12302

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12302
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12302) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12302)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12302)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12302)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12302)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12302)

theorem paidBaseCertificate (H : Set (Ret 12302)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12302

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12302
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12302) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12302)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12302)} (h : TablePayment H) :
    (retDist (paperCentres 12302)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12302))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12302} (t : ℝ)
    (hw : WINDOW (paperDesignP 12302) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12302 t c BstLean.Part259.agent12302.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12302

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12302
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12302) (a : Ix 12302) : Fin (Js 12302) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12302) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12302) : Measure (Fin (Js 12302)) :=
  (muI 12302).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12302) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12302) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12302) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12302)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12302) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12302)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12302)
    (M : Matrix (Fin (mA 12302)) (Fin (mA 12302)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12302) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12302) (mA 12302) (tA 12302) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12302) (mA 12302) (tA 12302)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12302) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12302

/-! A first-layer variance payment from dimension 12302. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12302
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12302} (hw : windowW wr)
    (θ : AHid 12302) {g : ℕ} (hg : g < Js 12302) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12302 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12302 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12302 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12302 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12302 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12302 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12302)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12302} (hw : windowW wr) :
    (gaussMat (mA 12302) 12302 (2 / (12302 : ℝ))).real {X | ∃ g < Js 12302,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12302 : ℝ)) ∨
      42 / (10 * (12302 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12302

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12303
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12303) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12303) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12303} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12303) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12303} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12303} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12303 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12303 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12303} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12303) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12303 - 1))).real
      {v | sgA (paperDesignP 12303) c a v < rowSigma} ∂BstLean.Part161.muI 12303 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12303 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12303 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12303 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12303

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12303
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12303) : Prop :=
  ∫ a, (stdGauss (Fin (12303 - 1))).real
    {v | sgA (paperDesignP 12303) c a v < rowSigma} ∂muI 12303 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12303) : SplitData 12303 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12303}
    (hw : WINDOW (paperDesignP 12303) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12303)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12303).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12303} (t : ℝ)
    (hw : WINDOW (paperDesignP 12303) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12303)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12303) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12303) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12303} (hw : WINDOW (paperDesignP 12303) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12303) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12303) c (hqSplit c) ⊆ bulkIx (paperDesignP 12303) c :=
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
noncomputable def hqRootInputs {c : Ret 12303} (t : ℝ)
    (hw : WINDOW (paperDesignP 12303) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12303))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12303 t c BstLean.Part259.agent12303.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12303] at h ⊢
    linarith

end BstLean.Part262.Row12303

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12303
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12303) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12303) c (rowSplit c wl ws),
    ((12303 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12303 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12303) c (rowSplit c wl ws),
    ((12303 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12303 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12303 - 1)))
    (rowSplit c wl ws).good a ∂muI 12303 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12303) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12303 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12303) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12303 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12303) c (rowSplit c wl ws),
    hellG2 12303 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12303 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12303}
    (hw : WINDOW (paperDesignP 12303) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12303}
    (hw : WINDOW (paperDesignP 12303) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12303 t c BstLean.Part259.agent12303.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12303

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12303
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12303) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12303)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12303)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12303)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12303)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12303)

theorem paidBaseCertificate (H : Set (Ret 12303)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12303

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12303
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12303) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12303)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12303)} (h : TablePayment H) :
    (retDist (paperCentres 12303)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12303))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12303} (t : ℝ)
    (hw : WINDOW (paperDesignP 12303) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12303 t c BstLean.Part259.agent12303.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12303

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12303
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12303) (a : Ix 12303) : Fin (Js 12303) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12303) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12303) : Measure (Fin (Js 12303)) :=
  (muI 12303).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12303) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12303) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12303) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12303)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12303) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12303)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12303)
    (M : Matrix (Fin (mA 12303)) (Fin (mA 12303)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12303) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12303) (mA 12303) (tA 12303) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12303) (mA 12303) (tA 12303)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12303) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12303

/-! A first-layer variance payment from dimension 12303. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12303
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12303} (hw : windowW wr)
    (θ : AHid 12303) {g : ℕ} (hg : g < Js 12303) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12303 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12303 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12303 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12303 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12303 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12303 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12303)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12303} (hw : windowW wr) :
    (gaussMat (mA 12303) 12303 (2 / (12303 : ℝ))).real {X | ∃ g < Js 12303,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12303 : ℝ)) ∨
      42 / (10 * (12303 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12303

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12304
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12304) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12304) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12304} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12304) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12304} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12304} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12304 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12304 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12304} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12304) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12304 - 1))).real
      {v | sgA (paperDesignP 12304) c a v < rowSigma} ∂BstLean.Part161.muI 12304 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12304 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12304 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12304 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12304

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12304
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12304) : Prop :=
  ∫ a, (stdGauss (Fin (12304 - 1))).real
    {v | sgA (paperDesignP 12304) c a v < rowSigma} ∂muI 12304 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12304) : SplitData 12304 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12304}
    (hw : WINDOW (paperDesignP 12304) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12304)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12304).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12304} (t : ℝ)
    (hw : WINDOW (paperDesignP 12304) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12304)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12304) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12304) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12304} (hw : WINDOW (paperDesignP 12304) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12304) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12304) c (hqSplit c) ⊆ bulkIx (paperDesignP 12304) c :=
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
noncomputable def hqRootInputs {c : Ret 12304} (t : ℝ)
    (hw : WINDOW (paperDesignP 12304) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12304))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12304 t c BstLean.Part259.agent12304.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12304] at h ⊢
    linarith

end BstLean.Part262.Row12304

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12304
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12304) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12304) c (rowSplit c wl ws),
    ((12304 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12304 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12304) c (rowSplit c wl ws),
    ((12304 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12304 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12304 - 1)))
    (rowSplit c wl ws).good a ∂muI 12304 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12304) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12304 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12304) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12304 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12304) c (rowSplit c wl ws),
    hellG2 12304 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12304 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12304}
    (hw : WINDOW (paperDesignP 12304) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12304}
    (hw : WINDOW (paperDesignP 12304) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12304 t c BstLean.Part259.agent12304.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12304

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12304
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12304) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12304)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12304)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12304)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12304)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12304)

theorem paidBaseCertificate (H : Set (Ret 12304)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12304

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12304
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12304) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12304)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12304)} (h : TablePayment H) :
    (retDist (paperCentres 12304)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12304))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12304} (t : ℝ)
    (hw : WINDOW (paperDesignP 12304) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12304 t c BstLean.Part259.agent12304.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12304

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12304
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12304) (a : Ix 12304) : Fin (Js 12304) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12304) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12304) : Measure (Fin (Js 12304)) :=
  (muI 12304).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12304) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12304) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12304) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12304)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12304) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12304)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12304)
    (M : Matrix (Fin (mA 12304)) (Fin (mA 12304)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12304) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12304) (mA 12304) (tA 12304) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12304) (mA 12304) (tA 12304)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12304) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12304

/-! A first-layer variance payment from dimension 12304. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12304
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12304} (hw : windowW wr)
    (θ : AHid 12304) {g : ℕ} (hg : g < Js 12304) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12304 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12304 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12304 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12304 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12304 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12304 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12304)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12304} (hw : windowW wr) :
    (gaussMat (mA 12304) 12304 (2 / (12304 : ℝ))).real {X | ∃ g < Js 12304,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12304 : ℝ)) ∨
      42 / (10 * (12304 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12304

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12305
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12305) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12305) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12305} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12305) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12305} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12305} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12305 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12305 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12305} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12305) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12305 - 1))).real
      {v | sgA (paperDesignP 12305) c a v < rowSigma} ∂BstLean.Part161.muI 12305 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12305 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12305 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12305 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12305

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12305
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12305) : Prop :=
  ∫ a, (stdGauss (Fin (12305 - 1))).real
    {v | sgA (paperDesignP 12305) c a v < rowSigma} ∂muI 12305 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12305) : SplitData 12305 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12305}
    (hw : WINDOW (paperDesignP 12305) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12305)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12305).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12305} (t : ℝ)
    (hw : WINDOW (paperDesignP 12305) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12305)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12305) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12305) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12305} (hw : WINDOW (paperDesignP 12305) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12305) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12305) c (hqSplit c) ⊆ bulkIx (paperDesignP 12305) c :=
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
noncomputable def hqRootInputs {c : Ret 12305} (t : ℝ)
    (hw : WINDOW (paperDesignP 12305) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12305))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12305 t c BstLean.Part259.agent12305.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12305] at h ⊢
    linarith

end BstLean.Part262.Row12305

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12305
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12305) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12305) c (rowSplit c wl ws),
    ((12305 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12305 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12305) c (rowSplit c wl ws),
    ((12305 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12305 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12305 - 1)))
    (rowSplit c wl ws).good a ∂muI 12305 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12305) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12305 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12305) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12305 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12305) c (rowSplit c wl ws),
    hellG2 12305 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12305 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12305}
    (hw : WINDOW (paperDesignP 12305) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12305}
    (hw : WINDOW (paperDesignP 12305) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12305 t c BstLean.Part259.agent12305.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12305

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12305
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12305) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12305)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12305)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12305)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12305)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12305)

theorem paidBaseCertificate (H : Set (Ret 12305)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12305

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12305
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12305) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12305)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12305)} (h : TablePayment H) :
    (retDist (paperCentres 12305)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12305))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12305} (t : ℝ)
    (hw : WINDOW (paperDesignP 12305) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12305 t c BstLean.Part259.agent12305.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12305

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12305
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12305) (a : Ix 12305) : Fin (Js 12305) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12305) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12305) : Measure (Fin (Js 12305)) :=
  (muI 12305).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12305) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12305) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12305) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12305)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12305) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12305)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12305)
    (M : Matrix (Fin (mA 12305)) (Fin (mA 12305)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12305) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12305) (mA 12305) (tA 12305) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12305) (mA 12305) (tA 12305)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12305) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12305

/-! A first-layer variance payment from dimension 12305. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12305
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12305} (hw : windowW wr)
    (θ : AHid 12305) {g : ℕ} (hg : g < Js 12305) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12305 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12305 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12305 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12305 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12305 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12305 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12305)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12305} (hw : windowW wr) :
    (gaussMat (mA 12305) 12305 (2 / (12305 : ℝ))).real {X | ∃ g < Js 12305,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12305 : ℝ)) ∨
      42 / (10 * (12305 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12305

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12306
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12306) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12306) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12306} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12306) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12306} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12306} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12306 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12306 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12306} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12306) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12306 - 1))).real
      {v | sgA (paperDesignP 12306) c a v < rowSigma} ∂BstLean.Part161.muI 12306 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12306 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12306 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12306 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12306

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12306
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12306) : Prop :=
  ∫ a, (stdGauss (Fin (12306 - 1))).real
    {v | sgA (paperDesignP 12306) c a v < rowSigma} ∂muI 12306 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12306) : SplitData 12306 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12306}
    (hw : WINDOW (paperDesignP 12306) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12306)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12306).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12306} (t : ℝ)
    (hw : WINDOW (paperDesignP 12306) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12306)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12306) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12306) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12306} (hw : WINDOW (paperDesignP 12306) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12306) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12306) c (hqSplit c) ⊆ bulkIx (paperDesignP 12306) c :=
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
noncomputable def hqRootInputs {c : Ret 12306} (t : ℝ)
    (hw : WINDOW (paperDesignP 12306) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12306))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12306 t c BstLean.Part259.agent12306.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12306] at h ⊢
    linarith

end BstLean.Part262.Row12306

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12306
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12306) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12306) c (rowSplit c wl ws),
    ((12306 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12306 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12306) c (rowSplit c wl ws),
    ((12306 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12306 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12306 - 1)))
    (rowSplit c wl ws).good a ∂muI 12306 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12306) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12306 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12306) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12306 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12306) c (rowSplit c wl ws),
    hellG2 12306 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12306 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12306}
    (hw : WINDOW (paperDesignP 12306) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12306}
    (hw : WINDOW (paperDesignP 12306) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12306 t c BstLean.Part259.agent12306.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12306

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12306
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12306) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12306)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12306)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12306)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12306)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12306)

theorem paidBaseCertificate (H : Set (Ret 12306)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12306

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12306
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12306) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12306)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12306)} (h : TablePayment H) :
    (retDist (paperCentres 12306)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12306))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12306} (t : ℝ)
    (hw : WINDOW (paperDesignP 12306) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12306 t c BstLean.Part259.agent12306.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12306

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12306
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12306) (a : Ix 12306) : Fin (Js 12306) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12306) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12306) : Measure (Fin (Js 12306)) :=
  (muI 12306).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12306) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12306) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12306) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12306)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12306) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12306)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12306)
    (M : Matrix (Fin (mA 12306)) (Fin (mA 12306)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12306) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12306) (mA 12306) (tA 12306) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12306) (mA 12306) (tA 12306)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12306) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12306

/-! A first-layer variance payment from dimension 12306. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12306
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12306} (hw : windowW wr)
    (θ : AHid 12306) {g : ℕ} (hg : g < Js 12306) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12306 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12306 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12306 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12306 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12306 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12306 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12306)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12306} (hw : windowW wr) :
    (gaussMat (mA 12306) 12306 (2 / (12306 : ℝ))).real {X | ∃ g < Js 12306,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12306 : ℝ)) ∨
      42 / (10 * (12306 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12306

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12307
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12307) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12307) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12307} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12307) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12307} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12307} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12307 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12307 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12307} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12307) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12307 - 1))).real
      {v | sgA (paperDesignP 12307) c a v < rowSigma} ∂BstLean.Part161.muI 12307 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12307 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12307 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12307 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12307

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12307
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12307) : Prop :=
  ∫ a, (stdGauss (Fin (12307 - 1))).real
    {v | sgA (paperDesignP 12307) c a v < rowSigma} ∂muI 12307 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12307) : SplitData 12307 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12307}
    (hw : WINDOW (paperDesignP 12307) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12307)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12307).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12307} (t : ℝ)
    (hw : WINDOW (paperDesignP 12307) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12307)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12307) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12307) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12307} (hw : WINDOW (paperDesignP 12307) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12307) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12307) c (hqSplit c) ⊆ bulkIx (paperDesignP 12307) c :=
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
noncomputable def hqRootInputs {c : Ret 12307} (t : ℝ)
    (hw : WINDOW (paperDesignP 12307) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12307))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12307 t c BstLean.Part259.agent12307.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12307] at h ⊢
    linarith

end BstLean.Part262.Row12307

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12307
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12307) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12307) c (rowSplit c wl ws),
    ((12307 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12307 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12307) c (rowSplit c wl ws),
    ((12307 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12307 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12307 - 1)))
    (rowSplit c wl ws).good a ∂muI 12307 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12307) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12307 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12307) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12307 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12307) c (rowSplit c wl ws),
    hellG2 12307 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12307 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12307}
    (hw : WINDOW (paperDesignP 12307) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12307}
    (hw : WINDOW (paperDesignP 12307) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12307 t c BstLean.Part259.agent12307.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12307

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12307
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12307) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12307)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12307)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12307)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12307)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12307)

theorem paidBaseCertificate (H : Set (Ret 12307)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12307

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12307
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12307) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12307)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12307)} (h : TablePayment H) :
    (retDist (paperCentres 12307)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12307))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12307} (t : ℝ)
    (hw : WINDOW (paperDesignP 12307) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12307 t c BstLean.Part259.agent12307.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12307

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12307
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12307) (a : Ix 12307) : Fin (Js 12307) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12307) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12307) : Measure (Fin (Js 12307)) :=
  (muI 12307).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12307) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12307) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12307) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12307)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12307) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12307)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12307)
    (M : Matrix (Fin (mA 12307)) (Fin (mA 12307)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12307) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12307) (mA 12307) (tA 12307) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12307) (mA 12307) (tA 12307)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12307) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12307

/-! A first-layer variance payment from dimension 12307. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12307
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12307} (hw : windowW wr)
    (θ : AHid 12307) {g : ℕ} (hg : g < Js 12307) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12307 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12307 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12307 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12307 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12307 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12307 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12307)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12307} (hw : windowW wr) :
    (gaussMat (mA 12307) 12307 (2 / (12307 : ℝ))).real {X | ∃ g < Js 12307,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12307 : ℝ)) ∨
      42 / (10 * (12307 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12307

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12308
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12308) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12308) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12308} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12308) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12308} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12308} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12308 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12308 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12308} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12308) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12308 - 1))).real
      {v | sgA (paperDesignP 12308) c a v < rowSigma} ∂BstLean.Part161.muI 12308 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12308 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12308 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12308 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12308

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12308
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12308) : Prop :=
  ∫ a, (stdGauss (Fin (12308 - 1))).real
    {v | sgA (paperDesignP 12308) c a v < rowSigma} ∂muI 12308 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12308) : SplitData 12308 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12308}
    (hw : WINDOW (paperDesignP 12308) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12308)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12308).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12308} (t : ℝ)
    (hw : WINDOW (paperDesignP 12308) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12308)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12308) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12308) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12308} (hw : WINDOW (paperDesignP 12308) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12308) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12308) c (hqSplit c) ⊆ bulkIx (paperDesignP 12308) c :=
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
noncomputable def hqRootInputs {c : Ret 12308} (t : ℝ)
    (hw : WINDOW (paperDesignP 12308) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12308))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12308 t c BstLean.Part259.agent12308.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12308] at h ⊢
    linarith

end BstLean.Part262.Row12308

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12308
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12308) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12308) c (rowSplit c wl ws),
    ((12308 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12308 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12308) c (rowSplit c wl ws),
    ((12308 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12308 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12308 - 1)))
    (rowSplit c wl ws).good a ∂muI 12308 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12308) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12308 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12308) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12308 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12308) c (rowSplit c wl ws),
    hellG2 12308 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12308 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12308}
    (hw : WINDOW (paperDesignP 12308) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12308}
    (hw : WINDOW (paperDesignP 12308) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12308 t c BstLean.Part259.agent12308.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12308

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12308
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12308) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12308)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12308)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12308)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12308)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12308)

theorem paidBaseCertificate (H : Set (Ret 12308)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12308

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12308
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12308) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12308)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12308)} (h : TablePayment H) :
    (retDist (paperCentres 12308)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12308))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12308} (t : ℝ)
    (hw : WINDOW (paperDesignP 12308) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12308 t c BstLean.Part259.agent12308.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12308

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12308
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12308) (a : Ix 12308) : Fin (Js 12308) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12308) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12308) : Measure (Fin (Js 12308)) :=
  (muI 12308).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12308) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12308) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12308) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12308)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12308) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12308)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12308)
    (M : Matrix (Fin (mA 12308)) (Fin (mA 12308)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12308) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12308) (mA 12308) (tA 12308) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12308) (mA 12308) (tA 12308)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12308) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12308

/-! A first-layer variance payment from dimension 12308. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12308
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12308} (hw : windowW wr)
    (θ : AHid 12308) {g : ℕ} (hg : g < Js 12308) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12308 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12308 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12308 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12308 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12308 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12308 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12308)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12308} (hw : windowW wr) :
    (gaussMat (mA 12308) 12308 (2 / (12308 : ℝ))).real {X | ∃ g < Js 12308,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12308 : ℝ)) ∨
      42 / (10 * (12308 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12308

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12309
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12309) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12309) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12309} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12309) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12309} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12309} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12309 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12309 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12309} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12309) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12309 - 1))).real
      {v | sgA (paperDesignP 12309) c a v < rowSigma} ∂BstLean.Part161.muI 12309 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12309 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12309 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12309 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12309

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12309
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12309) : Prop :=
  ∫ a, (stdGauss (Fin (12309 - 1))).real
    {v | sgA (paperDesignP 12309) c a v < rowSigma} ∂muI 12309 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12309) : SplitData 12309 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12309}
    (hw : WINDOW (paperDesignP 12309) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12309)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12309).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12309} (t : ℝ)
    (hw : WINDOW (paperDesignP 12309) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12309)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12309) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12309) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12309} (hw : WINDOW (paperDesignP 12309) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12309) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12309) c (hqSplit c) ⊆ bulkIx (paperDesignP 12309) c :=
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
noncomputable def hqRootInputs {c : Ret 12309} (t : ℝ)
    (hw : WINDOW (paperDesignP 12309) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12309))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12309 t c BstLean.Part259.agent12309.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12309] at h ⊢
    linarith

end BstLean.Part262.Row12309

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12309
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12309) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12309) c (rowSplit c wl ws),
    ((12309 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12309 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12309) c (rowSplit c wl ws),
    ((12309 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12309 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12309 - 1)))
    (rowSplit c wl ws).good a ∂muI 12309 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12309) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12309 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12309) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12309 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12309) c (rowSplit c wl ws),
    hellG2 12309 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12309 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12309}
    (hw : WINDOW (paperDesignP 12309) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12309}
    (hw : WINDOW (paperDesignP 12309) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12309 t c BstLean.Part259.agent12309.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12309

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12309
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12309) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12309)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12309)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12309)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12309)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12309)

theorem paidBaseCertificate (H : Set (Ret 12309)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12309

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12309
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12309) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12309)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12309)} (h : TablePayment H) :
    (retDist (paperCentres 12309)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12309))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12309} (t : ℝ)
    (hw : WINDOW (paperDesignP 12309) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12309 t c BstLean.Part259.agent12309.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12309

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12309
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12309) (a : Ix 12309) : Fin (Js 12309) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12309) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12309) : Measure (Fin (Js 12309)) :=
  (muI 12309).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12309) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12309) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12309) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12309)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12309) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12309)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12309)
    (M : Matrix (Fin (mA 12309)) (Fin (mA 12309)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12309) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12309) (mA 12309) (tA 12309) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12309) (mA 12309) (tA 12309)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12309) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12309

/-! A first-layer variance payment from dimension 12309. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12309
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12309} (hw : windowW wr)
    (θ : AHid 12309) {g : ℕ} (hg : g < Js 12309) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12309 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12309 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12309 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12309 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12309 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12309 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12309)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12309} (hw : windowW wr) :
    (gaussMat (mA 12309) 12309 (2 / (12309 : ℝ))).real {X | ∃ g < Js 12309,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12309 : ℝ)) ∨
      42 / (10 * (12309 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12309

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12310
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12310) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12310) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12310} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12310) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12310} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12310} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12310 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12310 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12310} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12310) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12310 - 1))).real
      {v | sgA (paperDesignP 12310) c a v < rowSigma} ∂BstLean.Part161.muI 12310 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12310 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12310 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12310 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12310

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12310
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12310) : Prop :=
  ∫ a, (stdGauss (Fin (12310 - 1))).real
    {v | sgA (paperDesignP 12310) c a v < rowSigma} ∂muI 12310 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12310) : SplitData 12310 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12310}
    (hw : WINDOW (paperDesignP 12310) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12310)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12310).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12310} (t : ℝ)
    (hw : WINDOW (paperDesignP 12310) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12310)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12310) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12310) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12310} (hw : WINDOW (paperDesignP 12310) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12310) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12310) c (hqSplit c) ⊆ bulkIx (paperDesignP 12310) c :=
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
noncomputable def hqRootInputs {c : Ret 12310} (t : ℝ)
    (hw : WINDOW (paperDesignP 12310) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12310))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12310 t c BstLean.Part259.agent12310.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12310] at h ⊢
    linarith

end BstLean.Part262.Row12310

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12310
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12310) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12310) c (rowSplit c wl ws),
    ((12310 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12310 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12310) c (rowSplit c wl ws),
    ((12310 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12310 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12310 - 1)))
    (rowSplit c wl ws).good a ∂muI 12310 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12310) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12310 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12310) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12310 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12310) c (rowSplit c wl ws),
    hellG2 12310 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12310 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12310}
    (hw : WINDOW (paperDesignP 12310) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12310}
    (hw : WINDOW (paperDesignP 12310) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12310 t c BstLean.Part259.agent12310.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12310

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12310
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12310) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12310)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12310)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12310)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12310)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12310)

theorem paidBaseCertificate (H : Set (Ret 12310)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12310

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12310
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12310) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12310)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12310)} (h : TablePayment H) :
    (retDist (paperCentres 12310)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12310))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12310} (t : ℝ)
    (hw : WINDOW (paperDesignP 12310) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12310 t c BstLean.Part259.agent12310.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12310

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12310
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12310) (a : Ix 12310) : Fin (Js 12310) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12310) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12310) : Measure (Fin (Js 12310)) :=
  (muI 12310).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12310) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12310) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12310) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12310)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12310) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12310)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12310)
    (M : Matrix (Fin (mA 12310)) (Fin (mA 12310)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12310) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12310) (mA 12310) (tA 12310) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12310) (mA 12310) (tA 12310)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12310) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12310

/-! A first-layer variance payment from dimension 12310. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12310
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12310} (hw : windowW wr)
    (θ : AHid 12310) {g : ℕ} (hg : g < Js 12310) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12310 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12310 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12310 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12310 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12310 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12310 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12310)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12310} (hw : windowW wr) :
    (gaussMat (mA 12310) 12310 (2 / (12310 : ℝ))).real {X | ∃ g < Js 12310,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12310 : ℝ)) ∨
      42 / (10 * (12310 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12310

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12311
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12311) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12311) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12311} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12311) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12311} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12311} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12311 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12311 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12311} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12311) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12311 - 1))).real
      {v | sgA (paperDesignP 12311) c a v < rowSigma} ∂BstLean.Part161.muI 12311 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12311 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12311 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12311 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12311

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12311
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12311) : Prop :=
  ∫ a, (stdGauss (Fin (12311 - 1))).real
    {v | sgA (paperDesignP 12311) c a v < rowSigma} ∂muI 12311 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12311) : SplitData 12311 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12311}
    (hw : WINDOW (paperDesignP 12311) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12311)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12311).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12311} (t : ℝ)
    (hw : WINDOW (paperDesignP 12311) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12311)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12311) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12311) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12311} (hw : WINDOW (paperDesignP 12311) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12311) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12311) c (hqSplit c) ⊆ bulkIx (paperDesignP 12311) c :=
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
noncomputable def hqRootInputs {c : Ret 12311} (t : ℝ)
    (hw : WINDOW (paperDesignP 12311) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12311))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12311 t c BstLean.Part259.agent12311.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12311] at h ⊢
    linarith

end BstLean.Part262.Row12311

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12311
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12311) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12311) c (rowSplit c wl ws),
    ((12311 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12311 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12311) c (rowSplit c wl ws),
    ((12311 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12311 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12311 - 1)))
    (rowSplit c wl ws).good a ∂muI 12311 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12311) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12311 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12311) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12311 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12311) c (rowSplit c wl ws),
    hellG2 12311 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12311 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12311}
    (hw : WINDOW (paperDesignP 12311) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12311}
    (hw : WINDOW (paperDesignP 12311) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12311 t c BstLean.Part259.agent12311.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12311

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12311
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12311) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12311)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12311)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12311)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12311)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12311)

theorem paidBaseCertificate (H : Set (Ret 12311)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12311

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12311
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12311) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12311)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12311)} (h : TablePayment H) :
    (retDist (paperCentres 12311)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12311))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12311} (t : ℝ)
    (hw : WINDOW (paperDesignP 12311) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12311 t c BstLean.Part259.agent12311.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12311

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12311
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12311) (a : Ix 12311) : Fin (Js 12311) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12311) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12311) : Measure (Fin (Js 12311)) :=
  (muI 12311).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12311) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12311) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12311) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12311)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12311) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12311)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12311)
    (M : Matrix (Fin (mA 12311)) (Fin (mA 12311)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12311) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12311) (mA 12311) (tA 12311) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12311) (mA 12311) (tA 12311)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12311) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12311

/-! A first-layer variance payment from dimension 12311. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12311
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12311} (hw : windowW wr)
    (θ : AHid 12311) {g : ℕ} (hg : g < Js 12311) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12311 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12311 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12311 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12311 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12311 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12311 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12311)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12311} (hw : windowW wr) :
    (gaussMat (mA 12311) 12311 (2 / (12311 : ℝ))).real {X | ∃ g < Js 12311,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12311 : ℝ)) ∨
      42 / (10 * (12311 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12311

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12312
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12312) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12312) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12312} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12312) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12312} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12312} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12312 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12312 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12312} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12312) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12312 - 1))).real
      {v | sgA (paperDesignP 12312) c a v < rowSigma} ∂BstLean.Part161.muI 12312 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12312 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12312 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12312 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12312

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12312
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12312) : Prop :=
  ∫ a, (stdGauss (Fin (12312 - 1))).real
    {v | sgA (paperDesignP 12312) c a v < rowSigma} ∂muI 12312 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12312) : SplitData 12312 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12312}
    (hw : WINDOW (paperDesignP 12312) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12312)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12312).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12312} (t : ℝ)
    (hw : WINDOW (paperDesignP 12312) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12312)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12312) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12312) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12312} (hw : WINDOW (paperDesignP 12312) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12312) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12312) c (hqSplit c) ⊆ bulkIx (paperDesignP 12312) c :=
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
noncomputable def hqRootInputs {c : Ret 12312} (t : ℝ)
    (hw : WINDOW (paperDesignP 12312) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12312))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12312 t c BstLean.Part259.agent12312.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12312] at h ⊢
    linarith

end BstLean.Part262.Row12312

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12312
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12312) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12312) c (rowSplit c wl ws),
    ((12312 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12312 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12312) c (rowSplit c wl ws),
    ((12312 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12312 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12312 - 1)))
    (rowSplit c wl ws).good a ∂muI 12312 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12312) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12312 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12312) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12312 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12312) c (rowSplit c wl ws),
    hellG2 12312 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12312 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12312}
    (hw : WINDOW (paperDesignP 12312) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12312}
    (hw : WINDOW (paperDesignP 12312) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12312 t c BstLean.Part259.agent12312.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12312

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12312
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12312) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12312)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12312)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12312)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12312)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12312)

theorem paidBaseCertificate (H : Set (Ret 12312)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12312

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12312
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12312) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12312)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12312)} (h : TablePayment H) :
    (retDist (paperCentres 12312)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12312))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12312} (t : ℝ)
    (hw : WINDOW (paperDesignP 12312) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12312 t c BstLean.Part259.agent12312.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12312

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12312
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12312) (a : Ix 12312) : Fin (Js 12312) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12312) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12312) : Measure (Fin (Js 12312)) :=
  (muI 12312).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12312) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12312) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12312) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12312)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12312) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12312)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12312)
    (M : Matrix (Fin (mA 12312)) (Fin (mA 12312)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12312) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12312) (mA 12312) (tA 12312) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12312) (mA 12312) (tA 12312)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12312) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12312

/-! A first-layer variance payment from dimension 12312. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12312
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12312} (hw : windowW wr)
    (θ : AHid 12312) {g : ℕ} (hg : g < Js 12312) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12312 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12312 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12312 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12312 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12312 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12312 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12312)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12312} (hw : windowW wr) :
    (gaussMat (mA 12312) 12312 (2 / (12312 : ℝ))).real {X | ∃ g < Js 12312,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12312 : ℝ)) ∨
      42 / (10 * (12312 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12312

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12313
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12313) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12313) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12313} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12313) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12313} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12313} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12313 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12313 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12313} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12313) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12313 - 1))).real
      {v | sgA (paperDesignP 12313) c a v < rowSigma} ∂BstLean.Part161.muI 12313 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12313 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12313 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12313 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12313

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12313
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12313) : Prop :=
  ∫ a, (stdGauss (Fin (12313 - 1))).real
    {v | sgA (paperDesignP 12313) c a v < rowSigma} ∂muI 12313 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12313) : SplitData 12313 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12313}
    (hw : WINDOW (paperDesignP 12313) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12313)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12313).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12313} (t : ℝ)
    (hw : WINDOW (paperDesignP 12313) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12313)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12313) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12313) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12313} (hw : WINDOW (paperDesignP 12313) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12313) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12313) c (hqSplit c) ⊆ bulkIx (paperDesignP 12313) c :=
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
noncomputable def hqRootInputs {c : Ret 12313} (t : ℝ)
    (hw : WINDOW (paperDesignP 12313) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12313))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12313 t c BstLean.Part259.agent12313.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12313] at h ⊢
    linarith

end BstLean.Part262.Row12313

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12313
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12313) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12313) c (rowSplit c wl ws),
    ((12313 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12313 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12313) c (rowSplit c wl ws),
    ((12313 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12313 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12313 - 1)))
    (rowSplit c wl ws).good a ∂muI 12313 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12313) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12313 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12313) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12313 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12313) c (rowSplit c wl ws),
    hellG2 12313 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12313 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12313}
    (hw : WINDOW (paperDesignP 12313) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12313}
    (hw : WINDOW (paperDesignP 12313) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12313 t c BstLean.Part259.agent12313.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12313

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12313
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12313) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12313)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12313)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12313)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12313)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12313)

theorem paidBaseCertificate (H : Set (Ret 12313)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12313

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12313
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12313) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12313)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12313)} (h : TablePayment H) :
    (retDist (paperCentres 12313)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12313))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12313} (t : ℝ)
    (hw : WINDOW (paperDesignP 12313) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12313 t c BstLean.Part259.agent12313.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12313

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12313
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12313) (a : Ix 12313) : Fin (Js 12313) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12313) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12313) : Measure (Fin (Js 12313)) :=
  (muI 12313).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12313) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12313) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12313) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12313)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12313) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12313)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12313)
    (M : Matrix (Fin (mA 12313)) (Fin (mA 12313)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12313) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12313) (mA 12313) (tA 12313) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12313) (mA 12313) (tA 12313)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12313) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12313

/-! A first-layer variance payment from dimension 12313. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12313
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12313} (hw : windowW wr)
    (θ : AHid 12313) {g : ℕ} (hg : g < Js 12313) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12313 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12313 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12313 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12313 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12313 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12313 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12313)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12313} (hw : windowW wr) :
    (gaussMat (mA 12313) 12313 (2 / (12313 : ℝ))).real {X | ∃ g < Js 12313,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12313 : ℝ)) ∨
      42 / (10 * (12313 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12313

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12314
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12314) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12314) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12314} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12314) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12314} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12314} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12314 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12314 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12314} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12314) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12314 - 1))).real
      {v | sgA (paperDesignP 12314) c a v < rowSigma} ∂BstLean.Part161.muI 12314 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12314 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12314 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12314 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12314

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12314
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12314) : Prop :=
  ∫ a, (stdGauss (Fin (12314 - 1))).real
    {v | sgA (paperDesignP 12314) c a v < rowSigma} ∂muI 12314 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12314) : SplitData 12314 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12314}
    (hw : WINDOW (paperDesignP 12314) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12314)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12314).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12314} (t : ℝ)
    (hw : WINDOW (paperDesignP 12314) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12314)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12314) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12314) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12314} (hw : WINDOW (paperDesignP 12314) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12314) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12314) c (hqSplit c) ⊆ bulkIx (paperDesignP 12314) c :=
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
noncomputable def hqRootInputs {c : Ret 12314} (t : ℝ)
    (hw : WINDOW (paperDesignP 12314) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12314))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12314 t c BstLean.Part259.agent12314.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12314] at h ⊢
    linarith

end BstLean.Part262.Row12314

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12314
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12314) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12314) c (rowSplit c wl ws),
    ((12314 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12314 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12314) c (rowSplit c wl ws),
    ((12314 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12314 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12314 - 1)))
    (rowSplit c wl ws).good a ∂muI 12314 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12314) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12314 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12314) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12314 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12314) c (rowSplit c wl ws),
    hellG2 12314 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12314 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12314}
    (hw : WINDOW (paperDesignP 12314) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12314}
    (hw : WINDOW (paperDesignP 12314) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12314 t c BstLean.Part259.agent12314.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12314

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12314
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12314) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12314)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12314)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12314)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12314)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12314)

theorem paidBaseCertificate (H : Set (Ret 12314)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12314

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12314
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12314) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12314)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12314)} (h : TablePayment H) :
    (retDist (paperCentres 12314)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12314))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12314} (t : ℝ)
    (hw : WINDOW (paperDesignP 12314) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12314 t c BstLean.Part259.agent12314.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12314

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12314
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12314) (a : Ix 12314) : Fin (Js 12314) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12314) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12314) : Measure (Fin (Js 12314)) :=
  (muI 12314).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12314) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12314) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12314) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12314)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12314) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12314)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12314)
    (M : Matrix (Fin (mA 12314)) (Fin (mA 12314)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12314) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12314) (mA 12314) (tA 12314) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12314) (mA 12314) (tA 12314)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12314) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12314

/-! A first-layer variance payment from dimension 12314. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12314
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12314} (hw : windowW wr)
    (θ : AHid 12314) {g : ℕ} (hg : g < Js 12314) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12314 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12314 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12314 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12314 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12314 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12314 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12314)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12314} (hw : windowW wr) :
    (gaussMat (mA 12314) 12314 (2 / (12314 : ℝ))).real {X | ∃ g < Js 12314,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12314 : ℝ)) ∨
      42 / (10 * (12314 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12314

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12315
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12315) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12315) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12315} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12315) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12315} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12315} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12315 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12315 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12315} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12315) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12315 - 1))).real
      {v | sgA (paperDesignP 12315) c a v < rowSigma} ∂BstLean.Part161.muI 12315 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12315 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12315 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12315 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12315

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12315
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12315) : Prop :=
  ∫ a, (stdGauss (Fin (12315 - 1))).real
    {v | sgA (paperDesignP 12315) c a v < rowSigma} ∂muI 12315 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12315) : SplitData 12315 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12315}
    (hw : WINDOW (paperDesignP 12315) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12315)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12315).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12315} (t : ℝ)
    (hw : WINDOW (paperDesignP 12315) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12315)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12315) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12315) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12315} (hw : WINDOW (paperDesignP 12315) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12315) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12315) c (hqSplit c) ⊆ bulkIx (paperDesignP 12315) c :=
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
noncomputable def hqRootInputs {c : Ret 12315} (t : ℝ)
    (hw : WINDOW (paperDesignP 12315) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12315))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12315 t c BstLean.Part259.agent12315.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12315] at h ⊢
    linarith

end BstLean.Part262.Row12315

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12315
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12315) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12315) c (rowSplit c wl ws),
    ((12315 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12315 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12315) c (rowSplit c wl ws),
    ((12315 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12315 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12315 - 1)))
    (rowSplit c wl ws).good a ∂muI 12315 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12315) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12315 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12315) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12315 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12315) c (rowSplit c wl ws),
    hellG2 12315 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12315 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12315}
    (hw : WINDOW (paperDesignP 12315) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12315}
    (hw : WINDOW (paperDesignP 12315) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12315 t c BstLean.Part259.agent12315.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12315

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12315
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12315) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12315)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12315)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12315)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12315)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12315)

theorem paidBaseCertificate (H : Set (Ret 12315)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12315

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12315
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12315) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12315)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12315)} (h : TablePayment H) :
    (retDist (paperCentres 12315)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12315))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12315} (t : ℝ)
    (hw : WINDOW (paperDesignP 12315) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12315 t c BstLean.Part259.agent12315.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12315

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12315
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12315) (a : Ix 12315) : Fin (Js 12315) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12315) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12315) : Measure (Fin (Js 12315)) :=
  (muI 12315).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12315) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12315) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12315) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12315)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12315) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12315)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12315)
    (M : Matrix (Fin (mA 12315)) (Fin (mA 12315)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12315) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12315) (mA 12315) (tA 12315) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12315) (mA 12315) (tA 12315)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12315) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12315

/-! A first-layer variance payment from dimension 12315. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12315
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12315} (hw : windowW wr)
    (θ : AHid 12315) {g : ℕ} (hg : g < Js 12315) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12315 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12315 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12315 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12315 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12315 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12315 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12315)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12315} (hw : windowW wr) :
    (gaussMat (mA 12315) 12315 (2 / (12315 : ℝ))).real {X | ∃ g < Js 12315,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12315 : ℝ)) ∨
      42 / (10 * (12315 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12315

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12316
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12316) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12316) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12316} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12316) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12316} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12316} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12316 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12316 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12316} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12316) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12316 - 1))).real
      {v | sgA (paperDesignP 12316) c a v < rowSigma} ∂BstLean.Part161.muI 12316 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12316 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12316 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12316 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12316

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12316
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12316) : Prop :=
  ∫ a, (stdGauss (Fin (12316 - 1))).real
    {v | sgA (paperDesignP 12316) c a v < rowSigma} ∂muI 12316 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12316) : SplitData 12316 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12316}
    (hw : WINDOW (paperDesignP 12316) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12316)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12316).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12316} (t : ℝ)
    (hw : WINDOW (paperDesignP 12316) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12316)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12316) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12316) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12316} (hw : WINDOW (paperDesignP 12316) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12316) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12316) c (hqSplit c) ⊆ bulkIx (paperDesignP 12316) c :=
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
noncomputable def hqRootInputs {c : Ret 12316} (t : ℝ)
    (hw : WINDOW (paperDesignP 12316) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12316))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12316 t c BstLean.Part259.agent12316.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12316] at h ⊢
    linarith

end BstLean.Part262.Row12316

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12316
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12316) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12316) c (rowSplit c wl ws),
    ((12316 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12316 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12316) c (rowSplit c wl ws),
    ((12316 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12316 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12316 - 1)))
    (rowSplit c wl ws).good a ∂muI 12316 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12316) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12316 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12316) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12316 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12316) c (rowSplit c wl ws),
    hellG2 12316 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12316 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12316}
    (hw : WINDOW (paperDesignP 12316) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12316}
    (hw : WINDOW (paperDesignP 12316) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12316 t c BstLean.Part259.agent12316.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12316

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12316
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12316) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12316)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12316)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12316)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12316)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12316)

theorem paidBaseCertificate (H : Set (Ret 12316)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12316

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12316
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12316) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12316)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12316)} (h : TablePayment H) :
    (retDist (paperCentres 12316)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12316))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12316} (t : ℝ)
    (hw : WINDOW (paperDesignP 12316) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12316 t c BstLean.Part259.agent12316.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12316

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12316
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12316) (a : Ix 12316) : Fin (Js 12316) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12316) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12316) : Measure (Fin (Js 12316)) :=
  (muI 12316).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12316) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12316) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12316) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12316)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12316) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12316)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12316)
    (M : Matrix (Fin (mA 12316)) (Fin (mA 12316)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12316) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12316) (mA 12316) (tA 12316) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12316) (mA 12316) (tA 12316)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12316) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12316

/-! A first-layer variance payment from dimension 12316. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12316
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12316} (hw : windowW wr)
    (θ : AHid 12316) {g : ℕ} (hg : g < Js 12316) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12316 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12316 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12316 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12316 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12316 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12316 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12316)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12316} (hw : windowW wr) :
    (gaussMat (mA 12316) 12316 (2 / (12316 : ℝ))).real {X | ∃ g < Js 12316,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12316 : ℝ)) ∨
      42 / (10 * (12316 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12316

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12317
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12317) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12317) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12317} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12317) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12317} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12317} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12317 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12317 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12317} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12317) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12317 - 1))).real
      {v | sgA (paperDesignP 12317) c a v < rowSigma} ∂BstLean.Part161.muI 12317 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12317 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12317 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12317 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12317

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12317
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12317) : Prop :=
  ∫ a, (stdGauss (Fin (12317 - 1))).real
    {v | sgA (paperDesignP 12317) c a v < rowSigma} ∂muI 12317 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12317) : SplitData 12317 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12317}
    (hw : WINDOW (paperDesignP 12317) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12317)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12317).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12317} (t : ℝ)
    (hw : WINDOW (paperDesignP 12317) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12317)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12317) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12317) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12317} (hw : WINDOW (paperDesignP 12317) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12317) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12317) c (hqSplit c) ⊆ bulkIx (paperDesignP 12317) c :=
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
noncomputable def hqRootInputs {c : Ret 12317} (t : ℝ)
    (hw : WINDOW (paperDesignP 12317) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12317))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12317 t c BstLean.Part259.agent12317.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12317] at h ⊢
    linarith

end BstLean.Part262.Row12317

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12317
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12317) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12317) c (rowSplit c wl ws),
    ((12317 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12317 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12317) c (rowSplit c wl ws),
    ((12317 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12317 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12317 - 1)))
    (rowSplit c wl ws).good a ∂muI 12317 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12317) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12317 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12317) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12317 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12317) c (rowSplit c wl ws),
    hellG2 12317 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12317 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12317}
    (hw : WINDOW (paperDesignP 12317) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12317}
    (hw : WINDOW (paperDesignP 12317) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12317 t c BstLean.Part259.agent12317.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12317

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12317
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12317) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12317)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12317)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12317)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12317)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12317)

theorem paidBaseCertificate (H : Set (Ret 12317)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12317

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12317
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12317) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12317)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12317)} (h : TablePayment H) :
    (retDist (paperCentres 12317)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12317))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12317} (t : ℝ)
    (hw : WINDOW (paperDesignP 12317) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12317 t c BstLean.Part259.agent12317.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12317

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12317
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12317) (a : Ix 12317) : Fin (Js 12317) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12317) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12317) : Measure (Fin (Js 12317)) :=
  (muI 12317).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12317) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12317) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12317) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12317)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12317) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12317)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12317)
    (M : Matrix (Fin (mA 12317)) (Fin (mA 12317)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12317) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12317) (mA 12317) (tA 12317) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12317) (mA 12317) (tA 12317)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12317) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12317

/-! A first-layer variance payment from dimension 12317. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12317
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12317} (hw : windowW wr)
    (θ : AHid 12317) {g : ℕ} (hg : g < Js 12317) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12317 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12317 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12317 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12317 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12317 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12317 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12317)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12317} (hw : windowW wr) :
    (gaussMat (mA 12317) 12317 (2 / (12317 : ℝ))).real {X | ∃ g < Js 12317,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12317 : ℝ)) ∨
      42 / (10 * (12317 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12317

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12318
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12318) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12318) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12318} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12318) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12318} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12318} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12318 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12318 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12318} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12318) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12318 - 1))).real
      {v | sgA (paperDesignP 12318) c a v < rowSigma} ∂BstLean.Part161.muI 12318 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12318 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12318 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12318 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12318

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12318
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12318) : Prop :=
  ∫ a, (stdGauss (Fin (12318 - 1))).real
    {v | sgA (paperDesignP 12318) c a v < rowSigma} ∂muI 12318 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12318) : SplitData 12318 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12318}
    (hw : WINDOW (paperDesignP 12318) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12318)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12318).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12318} (t : ℝ)
    (hw : WINDOW (paperDesignP 12318) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12318)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12318) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12318) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12318} (hw : WINDOW (paperDesignP 12318) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12318) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12318) c (hqSplit c) ⊆ bulkIx (paperDesignP 12318) c :=
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
noncomputable def hqRootInputs {c : Ret 12318} (t : ℝ)
    (hw : WINDOW (paperDesignP 12318) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12318))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12318 t c BstLean.Part259.agent12318.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12318] at h ⊢
    linarith

end BstLean.Part262.Row12318

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12318
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12318) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12318) c (rowSplit c wl ws),
    ((12318 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12318 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12318) c (rowSplit c wl ws),
    ((12318 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12318 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12318 - 1)))
    (rowSplit c wl ws).good a ∂muI 12318 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12318) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12318 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12318) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12318 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12318) c (rowSplit c wl ws),
    hellG2 12318 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12318 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12318}
    (hw : WINDOW (paperDesignP 12318) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12318}
    (hw : WINDOW (paperDesignP 12318) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12318 t c BstLean.Part259.agent12318.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12318

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12318
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12318) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12318)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12318)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12318)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12318)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12318)

theorem paidBaseCertificate (H : Set (Ret 12318)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12318

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12318
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12318) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12318)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12318)} (h : TablePayment H) :
    (retDist (paperCentres 12318)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12318))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12318} (t : ℝ)
    (hw : WINDOW (paperDesignP 12318) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12318 t c BstLean.Part259.agent12318.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12318

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12318
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12318) (a : Ix 12318) : Fin (Js 12318) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12318) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12318) : Measure (Fin (Js 12318)) :=
  (muI 12318).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12318) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12318) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12318) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12318)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12318) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12318)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12318)
    (M : Matrix (Fin (mA 12318)) (Fin (mA 12318)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12318) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12318) (mA 12318) (tA 12318) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12318) (mA 12318) (tA 12318)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12318) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12318

/-! A first-layer variance payment from dimension 12318. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12318
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12318} (hw : windowW wr)
    (θ : AHid 12318) {g : ℕ} (hg : g < Js 12318) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12318 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12318 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12318 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12318 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12318 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12318 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12318)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12318} (hw : windowW wr) :
    (gaussMat (mA 12318) 12318 (2 / (12318 : ℝ))).real {X | ∃ g < Js 12318,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12318 : ℝ)) ∨
      42 / (10 * (12318 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12318

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12319
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12319) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12319) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12319} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12319) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12319} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12319} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12319 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12319 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12319} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12319) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12319 - 1))).real
      {v | sgA (paperDesignP 12319) c a v < rowSigma} ∂BstLean.Part161.muI 12319 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12319 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12319 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12319 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12319

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12319
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12319) : Prop :=
  ∫ a, (stdGauss (Fin (12319 - 1))).real
    {v | sgA (paperDesignP 12319) c a v < rowSigma} ∂muI 12319 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12319) : SplitData 12319 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12319}
    (hw : WINDOW (paperDesignP 12319) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12319)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12319).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12319} (t : ℝ)
    (hw : WINDOW (paperDesignP 12319) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12319)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12319) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12319) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12319} (hw : WINDOW (paperDesignP 12319) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12319) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12319) c (hqSplit c) ⊆ bulkIx (paperDesignP 12319) c :=
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
noncomputable def hqRootInputs {c : Ret 12319} (t : ℝ)
    (hw : WINDOW (paperDesignP 12319) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12319))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12319 t c BstLean.Part259.agent12319.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12319] at h ⊢
    linarith

end BstLean.Part262.Row12319

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12319
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12319) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12319) c (rowSplit c wl ws),
    ((12319 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12319 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12319) c (rowSplit c wl ws),
    ((12319 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12319 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12319 - 1)))
    (rowSplit c wl ws).good a ∂muI 12319 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12319) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12319 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12319) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12319 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12319) c (rowSplit c wl ws),
    hellG2 12319 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12319 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12319}
    (hw : WINDOW (paperDesignP 12319) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12319}
    (hw : WINDOW (paperDesignP 12319) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12319 t c BstLean.Part259.agent12319.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12319

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12319
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12319) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12319)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12319)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12319)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12319)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12319)

theorem paidBaseCertificate (H : Set (Ret 12319)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12319

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12319
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12319) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12319)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12319)} (h : TablePayment H) :
    (retDist (paperCentres 12319)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12319))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12319} (t : ℝ)
    (hw : WINDOW (paperDesignP 12319) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12319 t c BstLean.Part259.agent12319.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12319

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12319
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12319) (a : Ix 12319) : Fin (Js 12319) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12319) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12319) : Measure (Fin (Js 12319)) :=
  (muI 12319).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12319) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12319) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12319) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12319)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12319) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12319)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12319)
    (M : Matrix (Fin (mA 12319)) (Fin (mA 12319)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12319) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12319) (mA 12319) (tA 12319) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12319) (mA 12319) (tA 12319)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12319) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12319

/-! A first-layer variance payment from dimension 12319. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12319
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12319} (hw : windowW wr)
    (θ : AHid 12319) {g : ℕ} (hg : g < Js 12319) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12319 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12319 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12319 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12319 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12319 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12319 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12319)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12319} (hw : windowW wr) :
    (gaussMat (mA 12319) 12319 (2 / (12319 : ℝ))).real {X | ∃ g < Js 12319,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12319 : ℝ)) ∨
      42 / (10 * (12319 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12319

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12320
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12320) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12320) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12320} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12320) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12320} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12320} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12320 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12320 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12320} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12320) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12320 - 1))).real
      {v | sgA (paperDesignP 12320) c a v < rowSigma} ∂BstLean.Part161.muI 12320 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12320 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12320 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12320 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12320

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12320
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12320) : Prop :=
  ∫ a, (stdGauss (Fin (12320 - 1))).real
    {v | sgA (paperDesignP 12320) c a v < rowSigma} ∂muI 12320 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12320) : SplitData 12320 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12320}
    (hw : WINDOW (paperDesignP 12320) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12320)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12320).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12320} (t : ℝ)
    (hw : WINDOW (paperDesignP 12320) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12320)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12320) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12320) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12320} (hw : WINDOW (paperDesignP 12320) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12320) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12320) c (hqSplit c) ⊆ bulkIx (paperDesignP 12320) c :=
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
noncomputable def hqRootInputs {c : Ret 12320} (t : ℝ)
    (hw : WINDOW (paperDesignP 12320) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12320))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12320 t c BstLean.Part259.agent12320.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12320] at h ⊢
    linarith

end BstLean.Part262.Row12320

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12320
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12320) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12320) c (rowSplit c wl ws),
    ((12320 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12320 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12320) c (rowSplit c wl ws),
    ((12320 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12320 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12320 - 1)))
    (rowSplit c wl ws).good a ∂muI 12320 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12320) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12320 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12320) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12320 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12320) c (rowSplit c wl ws),
    hellG2 12320 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12320 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12320}
    (hw : WINDOW (paperDesignP 12320) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12320}
    (hw : WINDOW (paperDesignP 12320) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12320 t c BstLean.Part259.agent12320.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12320

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12320
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12320) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12320)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12320)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12320)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12320)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12320)

theorem paidBaseCertificate (H : Set (Ret 12320)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12320

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12320
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12320) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12320)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12320)} (h : TablePayment H) :
    (retDist (paperCentres 12320)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12320))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12320} (t : ℝ)
    (hw : WINDOW (paperDesignP 12320) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12320 t c BstLean.Part259.agent12320.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12320

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12320
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12320) (a : Ix 12320) : Fin (Js 12320) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12320) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12320) : Measure (Fin (Js 12320)) :=
  (muI 12320).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12320) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12320) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12320) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12320)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12320) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12320)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12320)
    (M : Matrix (Fin (mA 12320)) (Fin (mA 12320)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12320) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12320) (mA 12320) (tA 12320) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12320) (mA 12320) (tA 12320)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12320) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12320

/-! A first-layer variance payment from dimension 12320. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12320
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12320} (hw : windowW wr)
    (θ : AHid 12320) {g : ℕ} (hg : g < Js 12320) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12320 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12320 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12320 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12320 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12320 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12320 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12320)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12320} (hw : windowW wr) :
    (gaussMat (mA 12320) 12320 (2 / (12320 : ℝ))).real {X | ∃ g < Js 12320,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12320 : ℝ)) ∨
      42 / (10 * (12320 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12320

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12321
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12321) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12321) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12321} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12321) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12321} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12321} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12321 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12321 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12321} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12321) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12321 - 1))).real
      {v | sgA (paperDesignP 12321) c a v < rowSigma} ∂BstLean.Part161.muI 12321 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12321 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12321 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12321 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12321

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12321
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12321) : Prop :=
  ∫ a, (stdGauss (Fin (12321 - 1))).real
    {v | sgA (paperDesignP 12321) c a v < rowSigma} ∂muI 12321 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12321) : SplitData 12321 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12321}
    (hw : WINDOW (paperDesignP 12321) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12321)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12321).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12321} (t : ℝ)
    (hw : WINDOW (paperDesignP 12321) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12321)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12321) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12321) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12321} (hw : WINDOW (paperDesignP 12321) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12321) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12321) c (hqSplit c) ⊆ bulkIx (paperDesignP 12321) c :=
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
noncomputable def hqRootInputs {c : Ret 12321} (t : ℝ)
    (hw : WINDOW (paperDesignP 12321) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12321))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12321 t c BstLean.Part259.agent12321.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12321] at h ⊢
    linarith

end BstLean.Part262.Row12321

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12321
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12321) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12321) c (rowSplit c wl ws),
    ((12321 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12321 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12321) c (rowSplit c wl ws),
    ((12321 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12321 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12321 - 1)))
    (rowSplit c wl ws).good a ∂muI 12321 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12321) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12321 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12321) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12321 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12321) c (rowSplit c wl ws),
    hellG2 12321 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12321 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12321}
    (hw : WINDOW (paperDesignP 12321) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12321}
    (hw : WINDOW (paperDesignP 12321) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12321 t c BstLean.Part259.agent12321.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12321

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12321
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12321) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12321)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12321)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12321)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12321)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12321)

theorem paidBaseCertificate (H : Set (Ret 12321)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12321

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12321
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12321) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12321)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12321)} (h : TablePayment H) :
    (retDist (paperCentres 12321)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12321))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12321} (t : ℝ)
    (hw : WINDOW (paperDesignP 12321) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12321 t c BstLean.Part259.agent12321.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12321

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12321
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12321) (a : Ix 12321) : Fin (Js 12321) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12321) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12321) : Measure (Fin (Js 12321)) :=
  (muI 12321).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12321) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12321) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12321) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12321)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12321) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12321)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12321)
    (M : Matrix (Fin (mA 12321)) (Fin (mA 12321)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12321) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12321) (mA 12321) (tA 12321) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12321) (mA 12321) (tA 12321)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12321) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12321

/-! A first-layer variance payment from dimension 12321. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12321
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12321} (hw : windowW wr)
    (θ : AHid 12321) {g : ℕ} (hg : g < Js 12321) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12321 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12321 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12321 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12321 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12321 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12321 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12321)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12321} (hw : windowW wr) :
    (gaussMat (mA 12321) 12321 (2 / (12321 : ℝ))).real {X | ∃ g < Js 12321,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12321 : ℝ)) ∨
      42 / (10 * (12321 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12321

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12322
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12322) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12322) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12322} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12322) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12322} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12322} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12322 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12322 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12322} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12322) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12322 - 1))).real
      {v | sgA (paperDesignP 12322) c a v < rowSigma} ∂BstLean.Part161.muI 12322 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12322 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12322 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12322 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12322

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12322
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12322) : Prop :=
  ∫ a, (stdGauss (Fin (12322 - 1))).real
    {v | sgA (paperDesignP 12322) c a v < rowSigma} ∂muI 12322 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12322) : SplitData 12322 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12322}
    (hw : WINDOW (paperDesignP 12322) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12322)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12322).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12322} (t : ℝ)
    (hw : WINDOW (paperDesignP 12322) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12322)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12322) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12322) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12322} (hw : WINDOW (paperDesignP 12322) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12322) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12322) c (hqSplit c) ⊆ bulkIx (paperDesignP 12322) c :=
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
noncomputable def hqRootInputs {c : Ret 12322} (t : ℝ)
    (hw : WINDOW (paperDesignP 12322) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12322))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12322 t c BstLean.Part259.agent12322.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12322] at h ⊢
    linarith

end BstLean.Part262.Row12322

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12322
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12322) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12322) c (rowSplit c wl ws),
    ((12322 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12322 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12322) c (rowSplit c wl ws),
    ((12322 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12322 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12322 - 1)))
    (rowSplit c wl ws).good a ∂muI 12322 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12322) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12322 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12322) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12322 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12322) c (rowSplit c wl ws),
    hellG2 12322 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12322 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12322}
    (hw : WINDOW (paperDesignP 12322) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12322}
    (hw : WINDOW (paperDesignP 12322) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12322 t c BstLean.Part259.agent12322.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12322

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12322
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12322) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12322)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12322)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12322)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12322)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12322)

theorem paidBaseCertificate (H : Set (Ret 12322)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12322

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12322
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12322) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12322)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12322)} (h : TablePayment H) :
    (retDist (paperCentres 12322)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12322))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12322} (t : ℝ)
    (hw : WINDOW (paperDesignP 12322) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12322 t c BstLean.Part259.agent12322.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12322

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12322
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12322) (a : Ix 12322) : Fin (Js 12322) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12322) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12322) : Measure (Fin (Js 12322)) :=
  (muI 12322).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12322) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12322) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12322) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12322)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12322) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12322)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12322)
    (M : Matrix (Fin (mA 12322)) (Fin (mA 12322)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12322) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12322) (mA 12322) (tA 12322) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12322) (mA 12322) (tA 12322)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12322) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12322

/-! A first-layer variance payment from dimension 12322. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12322
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12322} (hw : windowW wr)
    (θ : AHid 12322) {g : ℕ} (hg : g < Js 12322) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12322 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12322 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12322 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12322 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12322 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12322 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12322)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12322} (hw : windowW wr) :
    (gaussMat (mA 12322) 12322 (2 / (12322 : ℝ))).real {X | ∃ g < Js 12322,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12322 : ℝ)) ∨
      42 / (10 * (12322 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12322

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12323
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12323) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12323) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12323} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12323) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12323} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12323} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12323 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12323 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12323} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12323) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12323 - 1))).real
      {v | sgA (paperDesignP 12323) c a v < rowSigma} ∂BstLean.Part161.muI 12323 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12323 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12323 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12323 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12323

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12323
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12323) : Prop :=
  ∫ a, (stdGauss (Fin (12323 - 1))).real
    {v | sgA (paperDesignP 12323) c a v < rowSigma} ∂muI 12323 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12323) : SplitData 12323 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12323}
    (hw : WINDOW (paperDesignP 12323) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12323)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12323).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12323} (t : ℝ)
    (hw : WINDOW (paperDesignP 12323) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12323)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12323) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12323) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12323} (hw : WINDOW (paperDesignP 12323) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12323) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12323) c (hqSplit c) ⊆ bulkIx (paperDesignP 12323) c :=
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
noncomputable def hqRootInputs {c : Ret 12323} (t : ℝ)
    (hw : WINDOW (paperDesignP 12323) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12323))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12323 t c BstLean.Part259.agent12323.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12323] at h ⊢
    linarith

end BstLean.Part262.Row12323

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12323
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12323) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12323) c (rowSplit c wl ws),
    ((12323 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12323 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12323) c (rowSplit c wl ws),
    ((12323 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12323 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12323 - 1)))
    (rowSplit c wl ws).good a ∂muI 12323 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12323) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12323 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12323) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12323 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12323) c (rowSplit c wl ws),
    hellG2 12323 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12323 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12323}
    (hw : WINDOW (paperDesignP 12323) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12323}
    (hw : WINDOW (paperDesignP 12323) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12323 t c BstLean.Part259.agent12323.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12323

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12323
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12323) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12323)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12323)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12323)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12323)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12323)

theorem paidBaseCertificate (H : Set (Ret 12323)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12323

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12323
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12323) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12323)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12323)} (h : TablePayment H) :
    (retDist (paperCentres 12323)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12323))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12323} (t : ℝ)
    (hw : WINDOW (paperDesignP 12323) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12323 t c BstLean.Part259.agent12323.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12323

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12323
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12323) (a : Ix 12323) : Fin (Js 12323) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12323) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12323) : Measure (Fin (Js 12323)) :=
  (muI 12323).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12323) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12323) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12323) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12323)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12323) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12323)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12323)
    (M : Matrix (Fin (mA 12323)) (Fin (mA 12323)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12323) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12323) (mA 12323) (tA 12323) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12323) (mA 12323) (tA 12323)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12323) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12323

/-! A first-layer variance payment from dimension 12323. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12323
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12323} (hw : windowW wr)
    (θ : AHid 12323) {g : ℕ} (hg : g < Js 12323) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12323 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12323 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12323 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12323 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12323 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12323 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12323)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12323} (hw : windowW wr) :
    (gaussMat (mA 12323) 12323 (2 / (12323 : ℝ))).real {X | ∃ g < Js 12323,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12323 : ℝ)) ∨
      42 / (10 * (12323 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12323

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part262.Row12324
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12324) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12324) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12324} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (115400 : ℝ) * ((1003 / 1000) * (3505 / 10 ^ 15)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / (593 / 10 ^ 5) ^ 2 * ((1003 / 1000) * (357 / 10 ^ 10)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (534 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (54 / 10 ^ 5)) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (340 : ℝ) * ((1001 / 1000 + 48 / 1000 + 31 / 10000) * (656 / 10 ^ 8)) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (593 / 10 ^ 5) * ((1001 / 1000 + 48 / 1000) * (665 / 10 ^ 6)) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12324) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12324} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 12324} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12324 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      260 / 10 ^ 6 := by
  have hroot : √B ≤ 227 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (227 / 10 ^ 8 : ℝ) * ((1918 / 1000) * (357 / 10 ^ 10) /
        (2 * (1 - eta) * (593 / 10 ^ 5) ^ 2) +
        12324 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * (593 / 10 ^ 5) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12324} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12324) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12324 - 1))).real
      {v | sgA (paperDesignP 12324) c a v < rowSigma} ∂BstLean.Part161.muI 12324 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 12324 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12324 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12324 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part262.Row12324

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part262.Row12324
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12324) : Prop :=
  ∫ a, (stdGauss (Fin (12324 - 1))).real
    {v | sgA (paperDesignP 12324) c a v < rowSigma} ∂muI 12324 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12324) : SplitData 12324 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12324}
    (hw : WINDOW (paperDesignP 12324) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12324)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12324).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12324} (t : ℝ)
    (hw : WINDOW (paperDesignP 12324) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12324)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12324) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12324) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12324} (hw : WINDOW (paperDesignP 12324) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12324) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12324) c (hqSplit c) ⊆ bulkIx (paperDesignP 12324) c :=
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
noncomputable def hqRootInputs {c : Ret 12324} (t : ℝ)
    (hw : WINDOW (paperDesignP 12324) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12324))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12324 t c BstLean.Part259.agent12324.root where
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
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part259.agent12324] at h ⊢
    linarith

end BstLean.Part262.Row12324

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part262.Row12324
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12324) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12324) c (rowSplit c wl ws),
    ((12324 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12324 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12324) c (rowSplit c wl ws),
    ((12324 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12324 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12324 - 1)))
    (rowSplit c wl ws).good a ∂muI 12324 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12324) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12324 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12324) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12324 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12324) c (rowSplit c wl ws),
    hellG2 12324 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12324 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12324}
    (hw : WINDOW (paperDesignP 12324) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12324}
    (hw : WINDOW (paperDesignP 12324) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12324 t c BstLean.Part259.agent12324.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part262.Row12324

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part262.Row12324
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12324) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12324)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12324)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12324)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12324)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12324)

theorem paidBaseCertificate (H : Set (Ret 12324)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part262.Row12324

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part262.Row12324
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12324) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12324)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12324)} (h : TablePayment H) :
    (retDist (paperCentres 12324)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12324))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 12324} (t : ℝ)
    (hw : WINDOW (paperDesignP 12324) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12324 t c BstLean.Part259.agent12324.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part262.Row12324

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part262.Row12324
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12324) (a : Ix 12324) : Fin (Js 12324) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12324) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12324) : Measure (Fin (Js 12324)) :=
  (muI 12324).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12324) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12324) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12324) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12324)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12324) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12324)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12324)
    (M : Matrix (Fin (mA 12324)) (Fin (mA 12324)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12324) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12324) (mA 12324) (tA 12324) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12324) (mA 12324) (tA 12324)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12324) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part262.Row12324

/-! A first-layer variance payment from dimension 12324. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part262.Row12324
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

theorem row_node_geometry {wr : WRet 12324} (hw : windowW wr)
    (θ : AHid 12324) {g : ℕ} (hg : g < Js 12324) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12324 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12324 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12324 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12324 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12324 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12324 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12324)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12324} (hw : windowW wr) :
    (gaussMat (mA 12324) 12324 (2 / (12324 : ℝ))).real {X | ∃ g < Js 12324,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12324 : ℝ)) ∨
      42 / (10 * (12324 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part262.Row12324
