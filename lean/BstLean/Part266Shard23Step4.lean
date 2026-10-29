import BstLean.Part266Shard23Step3


/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12925) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12925) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12925} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((1489841699 / 12500) : ℝ) * ((1003 / 1000) * ((1482379 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5826053 / 1000000000)) ^ 2 * ((1003 / 1000) * ((15966453 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345235249 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2454201863 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5826053 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((254703513 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345235249 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1507199459 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5826053 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((156421117 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12925) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12925} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12925} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12925 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((15966453 / 500000000000000)) /
        (2 * (1 - eta) * ((5826053 / 1000000000)) ^ 2) +
        12925 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5826053 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12925} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12925) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12925 - 1))).real
      {v | sgA (paperDesignP 12925) c a v < rowSigma} ∂BstLean.Part161.muI 12925 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12925 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12925 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12925 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12925

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12925) : Prop :=
  ∫ a, (stdGauss (Fin (12925 - 1))).real
    {v | sgA (paperDesignP 12925) c a v < rowSigma} ∂muI 12925 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12925) : SplitData 12925 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12925}
    (hw : WINDOW (paperDesignP 12925) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12925)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12925).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12925} (t : ℝ)
    (hw : WINDOW (paperDesignP 12925) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12925)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12925) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12925) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12925} (hw : WINDOW (paperDesignP 12925) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12925) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12925) c (hqSplit c) ⊆ bulkIx (paperDesignP 12925) c :=
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
noncomputable def hqRootInputs {c : Ret 12925} (t : ℝ)
    (hw : WINDOW (paperDesignP 12925) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12925))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12925 t c BstLean.Part266.agent12925.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12925] at h ⊢
    linarith

end BstLean.Part266.Row12925

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12925) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12925) c (rowSplit c wl ws),
    ((12925 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12925 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12925) c (rowSplit c wl ws),
    ((12925 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12925 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12925 - 1)))
    (rowSplit c wl ws).good a ∂muI 12925 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12925) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12925 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12925) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12925 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12925) c (rowSplit c wl ws),
    hellG2 12925 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12925 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12925}
    (hw : WINDOW (paperDesignP 12925) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12925}
    (hw : WINDOW (paperDesignP 12925) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12925 t c BstLean.Part266.agent12925.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12925

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12925) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12925)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12925)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12925)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12925)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12925)

theorem paidBaseCertificate (H : Set (Ret 12925)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12925

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12925) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12925)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12925)} (h : TablePayment H) :
    (retDist (paperCentres 12925)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12925))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12925} (t : ℝ)
    (hw : WINDOW (paperDesignP 12925) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12925 t c BstLean.Part266.agent12925.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12925

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12925) (a : Ix 12925) : Fin (Js 12925) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12925) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12925) : Measure (Fin (Js 12925)) :=
  (muI 12925).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12925) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12925) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12925) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12925)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12925) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12925)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12925)
    (M : Matrix (Fin (mA 12925)) (Fin (mA 12925)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12925) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12925) (mA 12925) (tA 12925) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12925) (mA 12925) (tA 12925)).real
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

theorem table_second_layer_bad_subset (c : Ret 12925) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12925

/-! A first-layer variance payment from dimension 12925. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12925
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

theorem row_node_geometry {wr : WRet 12925} (hw : windowW wr)
    (θ : AHid 12925) {g : ℕ} (hg : g < Js 12925) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12925 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12925 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12925 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12925 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12925 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12925 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12925)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12925} (hw : windowW wr) :
    (gaussMat (mA 12925) 12925 (2 / (12925 : ℝ))).real {X | ∃ g < Js 12925,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12925 : ℝ)) ∨
      42 / (10 * (12925 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12925

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12926) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12926) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12926} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59598219029 / 500000) : ℝ) * ((1003 / 1000) * ((296407 / 100000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1456457 / 250000000)) ^ 2 * ((1003 / 1000) * ((6385593 / 200000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345248431 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((613479251 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1456457 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((254683801 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345248431 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3014049001 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1456457 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((312818019 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12926) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12926} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12926} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12926 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((6385593 / 200000000000000)) /
        (2 * (1 - eta) * ((1456457 / 250000000)) ^ 2) +
        12926 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1456457 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12926} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12926) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12926 - 1))).real
      {v | sgA (paperDesignP 12926) c a v < rowSigma} ∂BstLean.Part161.muI 12926 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12926 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12926 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12926 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12926

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12926) : Prop :=
  ∫ a, (stdGauss (Fin (12926 - 1))).real
    {v | sgA (paperDesignP 12926) c a v < rowSigma} ∂muI 12926 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12926) : SplitData 12926 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12926}
    (hw : WINDOW (paperDesignP 12926) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12926)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12926).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12926} (t : ℝ)
    (hw : WINDOW (paperDesignP 12926) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12926)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12926) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12926) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12926} (hw : WINDOW (paperDesignP 12926) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12926) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12926) c (hqSplit c) ⊆ bulkIx (paperDesignP 12926) c :=
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
noncomputable def hqRootInputs {c : Ret 12926} (t : ℝ)
    (hw : WINDOW (paperDesignP 12926) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12926))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12926 t c BstLean.Part266.agent12926.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12926] at h ⊢
    linarith

end BstLean.Part266.Row12926

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12926) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12926) c (rowSplit c wl ws),
    ((12926 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12926 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12926) c (rowSplit c wl ws),
    ((12926 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12926 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12926 - 1)))
    (rowSplit c wl ws).good a ∂muI 12926 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12926) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12926 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12926) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12926 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12926) c (rowSplit c wl ws),
    hellG2 12926 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12926 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12926}
    (hw : WINDOW (paperDesignP 12926) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12926}
    (hw : WINDOW (paperDesignP 12926) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12926 t c BstLean.Part266.agent12926.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12926

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12926) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12926)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12926)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12926)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12926)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12926)

theorem paidBaseCertificate (H : Set (Ret 12926)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12926

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12926) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12926)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12926)} (h : TablePayment H) :
    (retDist (paperCentres 12926)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12926))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12926} (t : ℝ)
    (hw : WINDOW (paperDesignP 12926) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12926 t c BstLean.Part266.agent12926.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12926

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12926) (a : Ix 12926) : Fin (Js 12926) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12926) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12926) : Measure (Fin (Js 12926)) :=
  (muI 12926).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12926) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12926) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12926) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12926)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12926) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12926)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12926)
    (M : Matrix (Fin (mA 12926)) (Fin (mA 12926)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12926) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12926) (mA 12926) (tA 12926) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12926) (mA 12926) (tA 12926)).real
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

theorem table_second_layer_bad_subset (c : Ret 12926) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12926

/-! A first-layer variance payment from dimension 12926. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12926
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

theorem row_node_geometry {wr : WRet 12926} (hw : windowW wr)
    (θ : AHid 12926) {g : ℕ} (hg : g < Js 12926) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12926 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12926 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12926 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12926 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12926 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12926 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12926)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12926} (hw : windowW wr) :
    (gaussMat (mA 12926) 12926 (2 / (12926 : ℝ))).real {X | ∃ g < Js 12926,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12926 : ℝ)) ∨
      42 / (10 * (12926 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12926

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12927) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12927) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12927} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((4768223297 / 40000) : ℝ) * ((1003 / 1000) * ((1481691 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2912801 / 500000000)) ^ 2 * ((1003 / 1000) * ((1276921 / 40000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172630837 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((12268161 / 2500000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2912801 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((101865637 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172630837 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((188356197 / 31250000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2912801 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((19549613 / 31250000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12927) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12927} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12927} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12927 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((1276921 / 40000000000000)) /
        (2 * (1 - eta) * ((2912801 / 500000000)) ^ 2) +
        12927 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2912801 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12927} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12927) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12927 - 1))).real
      {v | sgA (paperDesignP 12927) c a v < rowSigma} ∂BstLean.Part161.muI 12927 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12927 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12927 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12927 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12927

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12927) : Prop :=
  ∫ a, (stdGauss (Fin (12927 - 1))).real
    {v | sgA (paperDesignP 12927) c a v < rowSigma} ∂muI 12927 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12927) : SplitData 12927 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12927}
    (hw : WINDOW (paperDesignP 12927) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12927)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12927).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12927} (t : ℝ)
    (hw : WINDOW (paperDesignP 12927) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12927)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12927) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12927) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12927} (hw : WINDOW (paperDesignP 12927) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12927) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12927) c (hqSplit c) ⊆ bulkIx (paperDesignP 12927) c :=
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
noncomputable def hqRootInputs {c : Ret 12927} (t : ℝ)
    (hw : WINDOW (paperDesignP 12927) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12927))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12927 t c BstLean.Part266.agent12927.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12927] at h ⊢
    linarith

end BstLean.Part266.Row12927

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12927) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12927) c (rowSplit c wl ws),
    ((12927 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12927 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12927) c (rowSplit c wl ws),
    ((12927 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12927 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12927 - 1)))
    (rowSplit c wl ws).good a ∂muI 12927 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12927) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12927 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12927) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12927 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12927) c (rowSplit c wl ws),
    hellG2 12927 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12927 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12927}
    (hw : WINDOW (paperDesignP 12927) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12927}
    (hw : WINDOW (paperDesignP 12927) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12927 t c BstLean.Part266.agent12927.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12927

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12927) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12927)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12927)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12927)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12927)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12927)

theorem paidBaseCertificate (H : Set (Ret 12927)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12927

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12927) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12927)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12927)} (h : TablePayment H) :
    (retDist (paperCentres 12927)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12927))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12927} (t : ℝ)
    (hw : WINDOW (paperDesignP 12927) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12927 t c BstLean.Part266.agent12927.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12927

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12927) (a : Ix 12927) : Fin (Js 12927) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12927) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12927) : Measure (Fin (Js 12927)) :=
  (muI 12927).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12927) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12927) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12927) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12927)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12927) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12927)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12927)
    (M : Matrix (Fin (mA 12927)) (Fin (mA 12927)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12927) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12927) (mA 12927) (tA 12927) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12927) (mA 12927) (tA 12927)).real
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

theorem table_second_layer_bad_subset (c : Ret 12927) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12927

/-! A first-layer variance payment from dimension 12927. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12927
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

theorem row_node_geometry {wr : WRet 12927} (hw : windowW wr)
    (θ : AHid 12927) {g : ℕ} (hg : g < Js 12927) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12927 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12927 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12927 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12927 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12927 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12927 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12927)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12927} (hw : windowW wr) :
    (gaussMat (mA 12927) 12927 (2 / (12927 : ℝ))).real {X | ∃ g < Js 12927,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12927 : ℝ)) ∨
      42 / (10 * (12927 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12927

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12928) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12928) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12928} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59607343357 / 500000) : ℝ) * ((1003 / 1000) * ((1481347 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5825377 / 1000000000)) ^ 2 * ((1003 / 1000) * ((15959043 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172637429 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4906694903 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5825377 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((254644387 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172637429 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((301334937 / 50000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5825377 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((312769601 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12928) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12928} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12928} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12928 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((15959043 / 500000000000000)) /
        (2 * (1 - eta) * ((5825377 / 1000000000)) ^ 2) +
        12928 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5825377 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12928} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12928) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12928 - 1))).real
      {v | sgA (paperDesignP 12928) c a v < rowSigma} ∂BstLean.Part161.muI 12928 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12928 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12928 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12928 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12928

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12928) : Prop :=
  ∫ a, (stdGauss (Fin (12928 - 1))).real
    {v | sgA (paperDesignP 12928) c a v < rowSigma} ∂muI 12928 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12928) : SplitData 12928 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12928}
    (hw : WINDOW (paperDesignP 12928) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12928)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12928).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12928} (t : ℝ)
    (hw : WINDOW (paperDesignP 12928) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12928)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12928) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12928) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12928} (hw : WINDOW (paperDesignP 12928) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12928) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12928) c (hqSplit c) ⊆ bulkIx (paperDesignP 12928) c :=
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
noncomputable def hqRootInputs {c : Ret 12928} (t : ℝ)
    (hw : WINDOW (paperDesignP 12928) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12928))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12928 t c BstLean.Part266.agent12928.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12928] at h ⊢
    linarith

end BstLean.Part266.Row12928

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12928) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12928) c (rowSplit c wl ws),
    ((12928 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12928 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12928) c (rowSplit c wl ws),
    ((12928 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12928 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12928 - 1)))
    (rowSplit c wl ws).good a ∂muI 12928 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12928) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12928 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12928) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12928 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12928) c (rowSplit c wl ws),
    hellG2 12928 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12928 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12928}
    (hw : WINDOW (paperDesignP 12928) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12928}
    (hw : WINDOW (paperDesignP 12928) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12928 t c BstLean.Part266.agent12928.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12928

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12928) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12928)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12928)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12928)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12928)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12928)

theorem paidBaseCertificate (H : Set (Ret 12928)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12928

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12928) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12928)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12928)} (h : TablePayment H) :
    (retDist (paperCentres 12928)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12928))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12928} (t : ℝ)
    (hw : WINDOW (paperDesignP 12928) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12928 t c BstLean.Part266.agent12928.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12928

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12928) (a : Ix 12928) : Fin (Js 12928) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12928) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12928) : Measure (Fin (Js 12928)) :=
  (muI 12928).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12928) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12928) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12928) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12928)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12928) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12928)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12928)
    (M : Matrix (Fin (mA 12928)) (Fin (mA 12928)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12928) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12928) (mA 12928) (tA 12928) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12928) (mA 12928) (tA 12928)).real
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

theorem table_second_layer_bad_subset (c : Ret 12928) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12928

/-! A first-layer variance payment from dimension 12928. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12928
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

theorem row_node_geometry {wr : WRet 12928} (hw : windowW wr)
    (θ : AHid 12928) {g : ℕ} (hg : g < Js 12928) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12928 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12928 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12928 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12928 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12928 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12928 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12928)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12928} (hw : windowW wr) :
    (gaussMat (mA 12928) 12928 (2 / (12928 : ℝ))).real {X | ∃ g < Js 12928,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12928 : ℝ)) ∨
      42 / (10 * (12928 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12928

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12929) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12929) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12929} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((119223792077 / 1000000) : ℝ) * ((1003 / 1000) * ((2962007 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((45509 / 7812500)) ^ 2 * ((1003 / 1000) * ((7978287 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((86322011 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1226531379 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((45509 / 7812500)) * ((1001 / 1000 + 52 / 1000) * ((509249369 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((86322011 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((376624957 / 62500000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((45509 / 7812500)) * ((1001 / 1000 + 52 / 1000) * ((125098159 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12929) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12929} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12929} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12929 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((7978287 / 250000000000000)) /
        (2 * (1 - eta) * ((45509 / 7812500)) ^ 2) +
        12929 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((45509 / 7812500)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12929} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12929) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12929 - 1))).real
      {v | sgA (paperDesignP 12929) c a v < rowSigma} ∂BstLean.Part161.muI 12929 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12929 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12929 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12929 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12929

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12929) : Prop :=
  ∫ a, (stdGauss (Fin (12929 - 1))).real
    {v | sgA (paperDesignP 12929) c a v < rowSigma} ∂muI 12929 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12929) : SplitData 12929 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12929}
    (hw : WINDOW (paperDesignP 12929) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12929)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12929).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12929} (t : ℝ)
    (hw : WINDOW (paperDesignP 12929) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12929)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12929) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12929) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12929} (hw : WINDOW (paperDesignP 12929) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12929) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12929) c (hqSplit c) ⊆ bulkIx (paperDesignP 12929) c :=
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
noncomputable def hqRootInputs {c : Ret 12929} (t : ℝ)
    (hw : WINDOW (paperDesignP 12929) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12929))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12929 t c BstLean.Part266.agent12929.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12929] at h ⊢
    linarith

end BstLean.Part266.Row12929

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12929) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12929) c (rowSplit c wl ws),
    ((12929 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12929 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12929) c (rowSplit c wl ws),
    ((12929 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12929 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12929 - 1)))
    (rowSplit c wl ws).good a ∂muI 12929 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12929) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12929 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12929) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12929 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12929) c (rowSplit c wl ws),
    hellG2 12929 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12929 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12929}
    (hw : WINDOW (paperDesignP 12929) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12929}
    (hw : WINDOW (paperDesignP 12929) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12929 t c BstLean.Part266.agent12929.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12929

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12929) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12929)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12929)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12929)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12929)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12929)

theorem paidBaseCertificate (H : Set (Ret 12929)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12929

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12929) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12929)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12929)} (h : TablePayment H) :
    (retDist (paperCentres 12929)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12929))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12929} (t : ℝ)
    (hw : WINDOW (paperDesignP 12929) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12929 t c BstLean.Part266.agent12929.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12929

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12929) (a : Ix 12929) : Fin (Js 12929) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12929) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12929) : Measure (Fin (Js 12929)) :=
  (muI 12929).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12929) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12929) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12929) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12929)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12929) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12929)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12929)
    (M : Matrix (Fin (mA 12929)) (Fin (mA 12929)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12929) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12929) (mA 12929) (tA 12929) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12929) (mA 12929) (tA 12929)).real
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

theorem table_second_layer_bad_subset (c : Ret 12929) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12929

/-! A first-layer variance payment from dimension 12929. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12929
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

theorem row_node_geometry {wr : WRet 12929} (hw : windowW wr)
    (θ : AHid 12929) {g : ℕ} (hg : g < Js 12929) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12929 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12929 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12929 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12929 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12929 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12929 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12929)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12929} (hw : windowW wr) :
    (gaussMat (mA 12929) 12929 (2 / (12929 : ℝ))).real {X | ∃ g < Js 12929,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12929 : ℝ)) ∨
      42 / (10 * (12929 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12929

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12930) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12930) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12930} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((7452056157 / 62500) : ℝ) * ((1003 / 1000) * ((2961319 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5824927 / 1000000000)) ^ 2 * ((1003 / 1000) * ((31908211 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34530123 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2452778119 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5824927 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((509209971 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34530123 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6025300019 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5824927 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((125088479 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12930) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12930} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12930} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12930 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31908211 / 1000000000000000)) /
        (2 * (1 - eta) * ((5824927 / 1000000000)) ^ 2) +
        12930 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5824927 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12930} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12930) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12930 - 1))).real
      {v | sgA (paperDesignP 12930) c a v < rowSigma} ∂BstLean.Part161.muI 12930 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12930 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12930 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12930 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12930

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12930) : Prop :=
  ∫ a, (stdGauss (Fin (12930 - 1))).real
    {v | sgA (paperDesignP 12930) c a v < rowSigma} ∂muI 12930 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12930) : SplitData 12930 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12930}
    (hw : WINDOW (paperDesignP 12930) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12930)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12930).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12930} (t : ℝ)
    (hw : WINDOW (paperDesignP 12930) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12930)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12930) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12930) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12930} (hw : WINDOW (paperDesignP 12930) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12930) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12930) c (hqSplit c) ⊆ bulkIx (paperDesignP 12930) c :=
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
noncomputable def hqRootInputs {c : Ret 12930} (t : ℝ)
    (hw : WINDOW (paperDesignP 12930) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12930))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12930 t c BstLean.Part266.agent12930.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12930] at h ⊢
    linarith

end BstLean.Part266.Row12930

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12930) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12930) c (rowSplit c wl ws),
    ((12930 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12930 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12930) c (rowSplit c wl ws),
    ((12930 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12930 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12930 - 1)))
    (rowSplit c wl ws).good a ∂muI 12930 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12930) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12930 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12930) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12930 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12930) c (rowSplit c wl ws),
    hellG2 12930 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12930 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12930}
    (hw : WINDOW (paperDesignP 12930) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12930}
    (hw : WINDOW (paperDesignP 12930) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12930 t c BstLean.Part266.agent12930.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12930

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12930) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12930)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12930)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12930)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12930)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12930)

theorem paidBaseCertificate (H : Set (Ret 12930)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12930

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12930) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12930)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12930)} (h : TablePayment H) :
    (retDist (paperCentres 12930)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12930))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12930} (t : ℝ)
    (hw : WINDOW (paperDesignP 12930) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12930 t c BstLean.Part266.agent12930.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12930

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12930) (a : Ix 12930) : Fin (Js 12930) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12930) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12930) : Measure (Fin (Js 12930)) :=
  (muI 12930).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12930) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12930) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12930) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12930)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12930) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12930)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12930)
    (M : Matrix (Fin (mA 12930)) (Fin (mA 12930)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12930) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12930) (mA 12930) (tA 12930) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12930) (mA 12930) (tA 12930)).real
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

theorem table_second_layer_bad_subset (c : Ret 12930) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12930

/-! A first-layer variance payment from dimension 12930. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12930
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

theorem row_node_geometry {wr : WRet 12930} (hw : windowW wr)
    (θ : AHid 12930) {g : ℕ} (hg : g < Js 12930) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12930 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12930 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12930 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12930 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12930 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12930 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12930)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12930} (hw : windowW wr) :
    (gaussMat (mA 12930) 12930 (2 / (12930 : ℝ))).real {X | ∃ g < Js 12930,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12930 : ℝ)) ∨
      42 / (10 * (12930 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12930

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12931) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12931) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12931} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((29810511799 / 250000) : ℝ) * ((1003 / 1000) * ((370079 / 125000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5824701 / 1000000000)) ^ 2 * ((1003 / 1000) * ((7975819 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345314477 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4904987071 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5824701 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((254585289 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345314477 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3012300431 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5824701 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((625394003 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12931) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12931} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12931} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12931 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((7975819 / 250000000000000)) /
        (2 * (1 - eta) * ((5824701 / 1000000000)) ^ 2) +
        12931 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5824701 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12931} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12931) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12931 - 1))).real
      {v | sgA (paperDesignP 12931) c a v < rowSigma} ∂BstLean.Part161.muI 12931 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12931 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12931 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12931 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12931

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12931) : Prop :=
  ∫ a, (stdGauss (Fin (12931 - 1))).real
    {v | sgA (paperDesignP 12931) c a v < rowSigma} ∂muI 12931 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12931) : SplitData 12931 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12931}
    (hw : WINDOW (paperDesignP 12931) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12931)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12931).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12931} (t : ℝ)
    (hw : WINDOW (paperDesignP 12931) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12931)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12931) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12931) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12931} (hw : WINDOW (paperDesignP 12931) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12931) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12931) c (hqSplit c) ⊆ bulkIx (paperDesignP 12931) c :=
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
noncomputable def hqRootInputs {c : Ret 12931} (t : ℝ)
    (hw : WINDOW (paperDesignP 12931) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12931))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12931 t c BstLean.Part266.agent12931.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12931] at h ⊢
    linarith

end BstLean.Part266.Row12931

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12931) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12931) c (rowSplit c wl ws),
    ((12931 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12931 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12931) c (rowSplit c wl ws),
    ((12931 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12931 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12931 - 1)))
    (rowSplit c wl ws).good a ∂muI 12931 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12931) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12931 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12931) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12931 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12931) c (rowSplit c wl ws),
    hellG2 12931 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12931 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12931}
    (hw : WINDOW (paperDesignP 12931) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12931}
    (hw : WINDOW (paperDesignP 12931) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12931 t c BstLean.Part266.agent12931.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12931

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12931) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12931)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12931)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12931)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12931)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12931)

theorem paidBaseCertificate (H : Set (Ret 12931)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12931

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12931) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12931)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12931)} (h : TablePayment H) :
    (retDist (paperCentres 12931)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12931))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12931} (t : ℝ)
    (hw : WINDOW (paperDesignP 12931) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12931 t c BstLean.Part266.agent12931.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12931

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12931) (a : Ix 12931) : Fin (Js 12931) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12931) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12931) : Measure (Fin (Js 12931)) :=
  (muI 12931).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12931) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12931) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12931) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12931)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12931) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12931)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12931)
    (M : Matrix (Fin (mA 12931)) (Fin (mA 12931)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12931) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12931) (mA 12931) (tA 12931) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12931) (mA 12931) (tA 12931)).real
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

theorem table_second_layer_bad_subset (c : Ret 12931) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12931

/-! A first-layer variance payment from dimension 12931. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12931
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

theorem row_node_geometry {wr : WRet 12931} (hw : windowW wr)
    (θ : AHid 12931) {g : ℕ} (hg : g < Js 12931) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12931 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12931 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12931 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12931 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12931 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12931 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12931)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12931} (hw : windowW wr) :
    (gaussMat (mA 12931) 12931 (2 / (12931 : ℝ))).real {X | ∃ g < Js 12931,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12931 : ℝ)) ∨
      42 / (10 * (12931 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12931

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12932) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12932) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12932} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((14906394473 / 125000) : ℝ) * ((1003 / 1000) * ((1479973 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1456119 / 250000000)) ^ 2 * ((1003 / 1000) * ((15949171 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172663833 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2452209007 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1456119 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((509131191 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172663833 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6023901839 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1456119 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((625345619 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12932) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12932} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12932} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12932 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((15949171 / 500000000000000)) /
        (2 * (1 - eta) * ((1456119 / 250000000)) ^ 2) +
        12932 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1456119 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12932} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12932) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12932 - 1))).real
      {v | sgA (paperDesignP 12932) c a v < rowSigma} ∂BstLean.Part161.muI 12932 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12932 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12932 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12932 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12932

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12932) : Prop :=
  ∫ a, (stdGauss (Fin (12932 - 1))).real
    {v | sgA (paperDesignP 12932) c a v < rowSigma} ∂muI 12932 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12932) : SplitData 12932 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12932}
    (hw : WINDOW (paperDesignP 12932) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12932)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12932).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12932} (t : ℝ)
    (hw : WINDOW (paperDesignP 12932) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12932)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12932) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12932) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12932} (hw : WINDOW (paperDesignP 12932) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12932) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12932) c (hqSplit c) ⊆ bulkIx (paperDesignP 12932) c :=
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
noncomputable def hqRootInputs {c : Ret 12932} (t : ℝ)
    (hw : WINDOW (paperDesignP 12932) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12932))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12932 t c BstLean.Part266.agent12932.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12932] at h ⊢
    linarith

end BstLean.Part266.Row12932

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12932) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12932) c (rowSplit c wl ws),
    ((12932 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12932 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12932) c (rowSplit c wl ws),
    ((12932 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12932 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12932 - 1)))
    (rowSplit c wl ws).good a ∂muI 12932 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12932) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12932 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12932) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12932 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12932) c (rowSplit c wl ws),
    hellG2 12932 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12932 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12932}
    (hw : WINDOW (paperDesignP 12932) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12932}
    (hw : WINDOW (paperDesignP 12932) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12932 t c BstLean.Part266.agent12932.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12932

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12932) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12932)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12932)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12932)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12932)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12932)

theorem paidBaseCertificate (H : Set (Ret 12932)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12932

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12932) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12932)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12932)} (h : TablePayment H) :
    (retDist (paperCentres 12932)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12932))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12932} (t : ℝ)
    (hw : WINDOW (paperDesignP 12932) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12932 t c BstLean.Part266.agent12932.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12932

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12932) (a : Ix 12932) : Fin (Js 12932) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12932) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12932) : Measure (Fin (Js 12932)) :=
  (muI 12932).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12932) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12932) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12932) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12932)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12932) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12932)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12932)
    (M : Matrix (Fin (mA 12932)) (Fin (mA 12932)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12932) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12932) (mA 12932) (tA 12932) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12932) (mA 12932) (tA 12932)).real
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

theorem table_second_layer_bad_subset (c : Ret 12932) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12932

/-! A first-layer variance payment from dimension 12932. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12932
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

theorem row_node_geometry {wr : WRet 12932} (hw : windowW wr)
    (θ : AHid 12932) {g : ℕ} (hg : g < Js 12932) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12932 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12932 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12932 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12932 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12932 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12932 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12932)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12932} (hw : windowW wr) :
    (gaussMat (mA 12932) 12932 (2 / (12932 : ℝ))).real {X | ∃ g < Js 12932,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12932 : ℝ)) ∨
      42 / (10 * (12932 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12932

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12933) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12933) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12933} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((23852053089 / 200000) : ℝ) * ((1003 / 1000) * ((2959259 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5824251 / 1000000000)) ^ 2 * ((1003 / 1000) * ((996669 / 31250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((43167607 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4903849067 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5824251 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((509091811 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((43167607 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((752900369 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5824251 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((312648621 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12933) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12933} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12933} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12933 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((996669 / 31250000000000)) /
        (2 * (1 - eta) * ((5824251 / 1000000000)) ^ 2) +
        12933 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5824251 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12933} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12933) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12933 - 1))).real
      {v | sgA (paperDesignP 12933) c a v < rowSigma} ∂BstLean.Part161.muI 12933 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12933 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12933 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12933 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12933

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12933) : Prop :=
  ∫ a, (stdGauss (Fin (12933 - 1))).real
    {v | sgA (paperDesignP 12933) c a v < rowSigma} ∂muI 12933 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12933) : SplitData 12933 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12933}
    (hw : WINDOW (paperDesignP 12933) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12933)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12933).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12933} (t : ℝ)
    (hw : WINDOW (paperDesignP 12933) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12933)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12933) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12933) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12933} (hw : WINDOW (paperDesignP 12933) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12933) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12933) c (hqSplit c) ⊆ bulkIx (paperDesignP 12933) c :=
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
noncomputable def hqRootInputs {c : Ret 12933} (t : ℝ)
    (hw : WINDOW (paperDesignP 12933) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12933))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12933 t c BstLean.Part266.agent12933.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12933] at h ⊢
    linarith

end BstLean.Part266.Row12933

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12933) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12933) c (rowSplit c wl ws),
    ((12933 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12933 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12933) c (rowSplit c wl ws),
    ((12933 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12933 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12933 - 1)))
    (rowSplit c wl ws).good a ∂muI 12933 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12933) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12933 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12933) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12933 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12933) c (rowSplit c wl ws),
    hellG2 12933 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12933 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12933}
    (hw : WINDOW (paperDesignP 12933) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12933}
    (hw : WINDOW (paperDesignP 12933) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12933 t c BstLean.Part266.agent12933.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12933

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12933) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12933)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12933)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12933)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12933)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12933)

theorem paidBaseCertificate (H : Set (Ret 12933)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12933

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12933) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12933)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12933)} (h : TablePayment H) :
    (retDist (paperCentres 12933)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12933))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12933} (t : ℝ)
    (hw : WINDOW (paperDesignP 12933) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12933 t c BstLean.Part266.agent12933.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12933

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12933) (a : Ix 12933) : Fin (Js 12933) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12933) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12933) : Measure (Fin (Js 12933)) :=
  (muI 12933).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12933) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12933) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12933) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12933)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12933) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12933)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12933)
    (M : Matrix (Fin (mA 12933)) (Fin (mA 12933)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12933) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12933) (mA 12933) (tA 12933) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12933) (mA 12933) (tA 12933)).real
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

theorem table_second_layer_bad_subset (c : Ret 12933) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12933

/-! A first-layer variance payment from dimension 12933. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12933
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

theorem row_node_geometry {wr : WRet 12933} (hw : windowW wr)
    (θ : AHid 12933) {g : ℕ} (hg : g < Js 12933) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12933 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12933 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12933 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12933 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12933 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12933 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12933)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12933} (hw : windowW wr) :
    (gaussMat (mA 12933) 12933 (2 / (12933 : ℝ))).real {X | ∃ g < Js 12933,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12933 : ℝ)) ∨
      42 / (10 * (12933 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12933

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12934) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12934) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12934} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((119269376181 / 1000000) : ℝ) * ((1003 / 1000) * ((2958573 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2912013 / 500000000)) ^ 2 * ((1003 / 1000) * ((7972119 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172677023 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((490328023 / 100000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2912013 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((127263109 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172677023 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((30112521 / 5000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2912013 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((78156109 / 125000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12934) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12934} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12934} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12934 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((7972119 / 250000000000000)) /
        (2 * (1 - eta) * ((2912013 / 500000000)) ^ 2) +
        12934 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2912013 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12934} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12934) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12934 - 1))).real
      {v | sgA (paperDesignP 12934) c a v < rowSigma} ∂BstLean.Part161.muI 12934 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12934 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12934 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12934 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12934

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12934) : Prop :=
  ∫ a, (stdGauss (Fin (12934 - 1))).real
    {v | sgA (paperDesignP 12934) c a v < rowSigma} ∂muI 12934 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12934) : SplitData 12934 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12934}
    (hw : WINDOW (paperDesignP 12934) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12934)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12934).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12934} (t : ℝ)
    (hw : WINDOW (paperDesignP 12934) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12934)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12934) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12934) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12934} (hw : WINDOW (paperDesignP 12934) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12934) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12934) c (hqSplit c) ⊆ bulkIx (paperDesignP 12934) c :=
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
noncomputable def hqRootInputs {c : Ret 12934} (t : ℝ)
    (hw : WINDOW (paperDesignP 12934) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12934))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12934 t c BstLean.Part266.agent12934.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12934] at h ⊢
    linarith

end BstLean.Part266.Row12934

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12934) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12934) c (rowSplit c wl ws),
    ((12934 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12934 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12934) c (rowSplit c wl ws),
    ((12934 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12934 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12934 - 1)))
    (rowSplit c wl ws).good a ∂muI 12934 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12934) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12934 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12934) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12934 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12934) c (rowSplit c wl ws),
    hellG2 12934 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12934 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12934}
    (hw : WINDOW (paperDesignP 12934) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12934}
    (hw : WINDOW (paperDesignP 12934) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12934 t c BstLean.Part266.agent12934.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12934

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12934) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12934)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12934)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12934)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12934)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12934)

theorem paidBaseCertificate (H : Set (Ret 12934)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12934

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12934) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12934)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12934)} (h : TablePayment H) :
    (retDist (paperCentres 12934)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12934))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12934} (t : ℝ)
    (hw : WINDOW (paperDesignP 12934) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12934 t c BstLean.Part266.agent12934.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12934

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12934) (a : Ix 12934) : Fin (Js 12934) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12934) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12934) : Measure (Fin (Js 12934)) :=
  (muI 12934).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12934) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12934) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12934) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12934)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12934) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12934)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12934)
    (M : Matrix (Fin (mA 12934)) (Fin (mA 12934)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12934) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12934) (mA 12934) (tA 12934) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12934) (mA 12934) (tA 12934)).real
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

theorem table_second_layer_bad_subset (c : Ret 12934) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12934

/-! A first-layer variance payment from dimension 12934. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12934
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

theorem row_node_geometry {wr : WRet 12934} (hw : windowW wr)
    (θ : AHid 12934) {g : ℕ} (hg : g < Js 12934) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12934 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12934 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12934 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12934 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12934 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12934 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12934)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12934} (hw : windowW wr) :
    (gaussMat (mA 12934) 12934 (2 / (12934 : ℝ))).real {X | ∃ g < Js 12934,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12934 : ℝ)) ∨
      42 / (10 * (12934 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12934

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12935) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12935) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12935} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((11927848799 / 100000) : ℝ) * ((1003 / 1000) * ((1478943 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5823801 / 1000000000)) ^ 2 * ((1003 / 1000) * ((6376709 / 200000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172683619 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4902711503 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5823801 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((127253267 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172683619 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6021805583 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5823801 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((62520051 / 100000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12935) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12935} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12935} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12935 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((6376709 / 200000000000000)) /
        (2 * (1 - eta) * ((5823801 / 1000000000)) ^ 2) +
        12935 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5823801 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12935} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12935) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12935 - 1))).real
      {v | sgA (paperDesignP 12935) c a v < rowSigma} ∂BstLean.Part161.muI 12935 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12935 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12935 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12935 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12935

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12935) : Prop :=
  ∫ a, (stdGauss (Fin (12935 - 1))).real
    {v | sgA (paperDesignP 12935) c a v < rowSigma} ∂muI 12935 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12935) : SplitData 12935 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12935}
    (hw : WINDOW (paperDesignP 12935) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12935)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12935).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12935} (t : ℝ)
    (hw : WINDOW (paperDesignP 12935) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12935)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12935) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12935) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12935} (hw : WINDOW (paperDesignP 12935) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12935) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12935) c (hqSplit c) ⊆ bulkIx (paperDesignP 12935) c :=
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
noncomputable def hqRootInputs {c : Ret 12935} (t : ℝ)
    (hw : WINDOW (paperDesignP 12935) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12935))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12935 t c BstLean.Part266.agent12935.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12935] at h ⊢
    linarith

end BstLean.Part266.Row12935

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12935) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12935) c (rowSplit c wl ws),
    ((12935 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12935 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12935) c (rowSplit c wl ws),
    ((12935 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12935 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12935 - 1)))
    (rowSplit c wl ws).good a ∂muI 12935 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12935) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12935 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12935) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12935 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12935) c (rowSplit c wl ws),
    hellG2 12935 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12935 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12935}
    (hw : WINDOW (paperDesignP 12935) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12935}
    (hw : WINDOW (paperDesignP 12935) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12935 t c BstLean.Part266.agent12935.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12935

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12935) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12935)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12935)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12935)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12935)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12935)

theorem paidBaseCertificate (H : Set (Ret 12935)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12935

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12935) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12935)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12935)} (h : TablePayment H) :
    (retDist (paperCentres 12935)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12935))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12935} (t : ℝ)
    (hw : WINDOW (paperDesignP 12935) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12935 t c BstLean.Part266.agent12935.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12935

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12935) (a : Ix 12935) : Fin (Js 12935) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12935) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12935) : Measure (Fin (Js 12935)) :=
  (muI 12935).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12935) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12935) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12935) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12935)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12935) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12935)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12935)
    (M : Matrix (Fin (mA 12935)) (Fin (mA 12935)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12935) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12935) (mA 12935) (tA 12935) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12935) (mA 12935) (tA 12935)).real
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

theorem table_second_layer_bad_subset (c : Ret 12935) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12935

/-! A first-layer variance payment from dimension 12935. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12935
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

theorem row_node_geometry {wr : WRet 12935} (hw : windowW wr)
    (θ : AHid 12935) {g : ℕ} (hg : g < Js 12935) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12935 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12935 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12935 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12935 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12935 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12935 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12935)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12935} (hw : windowW wr) :
    (gaussMat (mA 12935) 12935 (2 / (12935 : ℝ))).real {X | ∃ g < Js 12935,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12935 : ℝ)) ∨
      42 / (10 * (12935 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12935

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12936) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12936) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12936} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59643800437 / 500000) : ℝ) * ((1003 / 1000) * ((7393 / 2500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((727947 / 125000000)) ^ 2 * ((1003 / 1000) * ((6375723 / 200000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345380431 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2451071443 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((727947 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((254486853 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345380431 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6021107101 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((727947 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((156288039 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12936) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12936} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12936} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12936 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((6375723 / 200000000000000)) /
        (2 * (1 - eta) * ((727947 / 125000000)) ^ 2) +
        12936 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((727947 / 125000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12936} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12936) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12936 - 1))).real
      {v | sgA (paperDesignP 12936) c a v < rowSigma} ∂BstLean.Part161.muI 12936 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12936 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12936 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12936 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12936

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12936) : Prop :=
  ∫ a, (stdGauss (Fin (12936 - 1))).real
    {v | sgA (paperDesignP 12936) c a v < rowSigma} ∂muI 12936 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12936) : SplitData 12936 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12936}
    (hw : WINDOW (paperDesignP 12936) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12936)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12936).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12936} (t : ℝ)
    (hw : WINDOW (paperDesignP 12936) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12936)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12936) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12936) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12936} (hw : WINDOW (paperDesignP 12936) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12936) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12936) c (hqSplit c) ⊆ bulkIx (paperDesignP 12936) c :=
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
noncomputable def hqRootInputs {c : Ret 12936} (t : ℝ)
    (hw : WINDOW (paperDesignP 12936) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12936))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12936 t c BstLean.Part266.agent12936.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12936] at h ⊢
    linarith

end BstLean.Part266.Row12936

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12936) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12936) c (rowSplit c wl ws),
    ((12936 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12936 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12936) c (rowSplit c wl ws),
    ((12936 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12936 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12936 - 1)))
    (rowSplit c wl ws).good a ∂muI 12936 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12936) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12936 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12936) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12936 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12936) c (rowSplit c wl ws),
    hellG2 12936 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12936 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12936}
    (hw : WINDOW (paperDesignP 12936) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12936}
    (hw : WINDOW (paperDesignP 12936) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12936 t c BstLean.Part266.agent12936.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12936

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12936) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12936)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12936)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12936)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12936)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12936)

theorem paidBaseCertificate (H : Set (Ret 12936)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12936

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12936) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12936)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12936)} (h : TablePayment H) :
    (retDist (paperCentres 12936)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12936))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12936} (t : ℝ)
    (hw : WINDOW (paperDesignP 12936) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12936 t c BstLean.Part266.agent12936.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12936

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12936) (a : Ix 12936) : Fin (Js 12936) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12936) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12936) : Measure (Fin (Js 12936)) :=
  (muI 12936).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12936) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12936) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12936) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12936)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12936) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12936)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12936)
    (M : Matrix (Fin (mA 12936)) (Fin (mA 12936)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12936) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12936) (mA 12936) (tA 12936) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12936) (mA 12936) (tA 12936)).real
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

theorem table_second_layer_bad_subset (c : Ret 12936) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12936

/-! A first-layer variance payment from dimension 12936. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12936
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

theorem row_node_geometry {wr : WRet 12936} (hw : windowW wr)
    (θ : AHid 12936) {g : ℕ} (hg : g < Js 12936) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12936 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12936 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12936 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12936 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12936 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12936 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12936)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12936} (hw : windowW wr) :
    (gaussMat (mA 12936) 12936 (2 / (12936 : ℝ))).real {X | ∃ g < Js 12936,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12936 : ℝ)) ∨
      42 / (10 * (12936 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12936

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12937) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12937) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12937} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((29824189009 / 250000) : ℝ) * ((1003 / 1000) * ((591303 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((116467 / 20000000)) ^ 2 * ((1003 / 1000) * ((31873687 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((86348421 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2450787189 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((116467 / 20000000)) * ((1001 / 1000 + 52 / 1000) * ((508934349 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((86348421 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3010204377 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((116467 / 20000000)) * ((1001 / 1000 + 52 / 1000) * ((625103809 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12937) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12937} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12937} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12937 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31873687 / 1000000000000000)) /
        (2 * (1 - eta) * ((116467 / 20000000)) ^ 2) +
        12937 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((116467 / 20000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12937} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12937) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12937 - 1))).real
      {v | sgA (paperDesignP 12937) c a v < rowSigma} ∂BstLean.Part161.muI 12937 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12937 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12937 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12937 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12937

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12937) : Prop :=
  ∫ a, (stdGauss (Fin (12937 - 1))).real
    {v | sgA (paperDesignP 12937) c a v < rowSigma} ∂muI 12937 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12937) : SplitData 12937 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12937}
    (hw : WINDOW (paperDesignP 12937) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12937)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12937).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12937} (t : ℝ)
    (hw : WINDOW (paperDesignP 12937) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12937)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12937) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12937) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12937} (hw : WINDOW (paperDesignP 12937) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12937) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12937) c (hqSplit c) ⊆ bulkIx (paperDesignP 12937) c :=
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
noncomputable def hqRootInputs {c : Ret 12937} (t : ℝ)
    (hw : WINDOW (paperDesignP 12937) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12937))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12937 t c BstLean.Part266.agent12937.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12937] at h ⊢
    linarith

end BstLean.Part266.Row12937

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12937) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12937) c (rowSplit c wl ws),
    ((12937 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12937 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12937) c (rowSplit c wl ws),
    ((12937 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12937 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12937 - 1)))
    (rowSplit c wl ws).good a ∂muI 12937 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12937) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12937 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12937) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12937 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12937) c (rowSplit c wl ws),
    hellG2 12937 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12937 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12937}
    (hw : WINDOW (paperDesignP 12937) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12937}
    (hw : WINDOW (paperDesignP 12937) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12937 t c BstLean.Part266.agent12937.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12937

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12937) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12937)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12937)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12937)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12937)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12937)

theorem paidBaseCertificate (H : Set (Ret 12937)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12937

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12937) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12937)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12937)} (h : TablePayment H) :
    (retDist (paperCentres 12937)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12937))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12937} (t : ℝ)
    (hw : WINDOW (paperDesignP 12937) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12937 t c BstLean.Part266.agent12937.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12937

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12937) (a : Ix 12937) : Fin (Js 12937) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12937) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12937) : Measure (Fin (Js 12937)) :=
  (muI 12937).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12937) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12937) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12937) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12937)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12937) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12937)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12937)
    (M : Matrix (Fin (mA 12937)) (Fin (mA 12937)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12937) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12937) (mA 12937) (tA 12937) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12937) (mA 12937) (tA 12937)).real
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

theorem table_second_layer_bad_subset (c : Ret 12937) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12937

/-! A first-layer variance payment from dimension 12937. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12937
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

theorem row_node_geometry {wr : WRet 12937} (hw : windowW wr)
    (θ : AHid 12937) {g : ℕ} (hg : g < Js 12937) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12937 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12937 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12937 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12937 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12937 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12937 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12937)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12937} (hw : windowW wr) :
    (gaussMat (mA 12937) 12937 (2 / (12937 : ℝ))).real {X | ∃ g < Js 12937,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12937 : ℝ)) ∨
      42 / (10 * (12937 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12937

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12938) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12938) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12938} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59652935537 / 500000) : ℝ) * ((1003 / 1000) * ((2955829 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((9317 / 1600000)) ^ 2 * ((1003 / 1000) * ((31868759 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345406879 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4901005981 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((9317 / 1600000)) * ((1001 / 1000 + 52 / 1000) * ((508894999 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345406879 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3009855271 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((9317 / 1600000)) * ((1001 / 1000 + 52 / 1000) * ((625055469 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12938) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12938} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12938} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12938 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31868759 / 1000000000000000)) /
        (2 * (1 - eta) * ((9317 / 1600000)) ^ 2) +
        12938 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((9317 / 1600000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12938} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12938) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12938 - 1))).real
      {v | sgA (paperDesignP 12938) c a v < rowSigma} ∂BstLean.Part161.muI 12938 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12938 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12938 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12938 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12938

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12938) : Prop :=
  ∫ a, (stdGauss (Fin (12938 - 1))).real
    {v | sgA (paperDesignP 12938) c a v < rowSigma} ∂muI 12938 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12938) : SplitData 12938 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12938}
    (hw : WINDOW (paperDesignP 12938) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12938)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12938).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12938} (t : ℝ)
    (hw : WINDOW (paperDesignP 12938) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12938)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12938) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12938) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12938} (hw : WINDOW (paperDesignP 12938) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12938) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12938) c (hqSplit c) ⊆ bulkIx (paperDesignP 12938) c :=
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
noncomputable def hqRootInputs {c : Ret 12938} (t : ℝ)
    (hw : WINDOW (paperDesignP 12938) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12938))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12938 t c BstLean.Part266.agent12938.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12938] at h ⊢
    linarith

end BstLean.Part266.Row12938

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12938) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12938) c (rowSplit c wl ws),
    ((12938 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12938 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12938) c (rowSplit c wl ws),
    ((12938 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12938 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12938 - 1)))
    (rowSplit c wl ws).good a ∂muI 12938 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12938) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12938 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12938) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12938 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12938) c (rowSplit c wl ws),
    hellG2 12938 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12938 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12938}
    (hw : WINDOW (paperDesignP 12938) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12938}
    (hw : WINDOW (paperDesignP 12938) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12938 t c BstLean.Part266.agent12938.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12938

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12938) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12938)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12938)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12938)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12938)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12938)

theorem paidBaseCertificate (H : Set (Ret 12938)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12938

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12938) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12938)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12938)} (h : TablePayment H) :
    (retDist (paperCentres 12938)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12938))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12938} (t : ℝ)
    (hw : WINDOW (paperDesignP 12938) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12938 t c BstLean.Part266.agent12938.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12938

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12938) (a : Ix 12938) : Fin (Js 12938) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12938) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12938) : Measure (Fin (Js 12938)) :=
  (muI 12938).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12938) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12938) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12938) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12938)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12938) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12938)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12938)
    (M : Matrix (Fin (mA 12938)) (Fin (mA 12938)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12938) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12938) (mA 12938) (tA 12938) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12938) (mA 12938) (tA 12938)).real
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

theorem table_second_layer_bad_subset (c : Ret 12938) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12938

/-! A first-layer variance payment from dimension 12938. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12938
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

theorem row_node_geometry {wr : WRet 12938} (hw : windowW wr)
    (θ : AHid 12938) {g : ℕ} (hg : g < Js 12938) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12938 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12938 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12938 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12938 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12938 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12938 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12938)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12938} (hw : windowW wr) :
    (gaussMat (mA 12938) 12938 (2 / (12938 : ℝ))).real {X | ∃ g < Js 12938,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12938 : ℝ)) ∨
      42 / (10 * (12938 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12938

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12939) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12939) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12939} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59657493593 / 500000) : ℝ) * ((1003 / 1000) * ((369393 / 125000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((58229 / 10000000)) ^ 2 * ((1003 / 1000) * ((31863833 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((13816803 / 40000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4900437693 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((58229 / 10000000)) * ((1001 / 1000 + 52 / 1000) * ((101771131 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((13816803 / 40000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1203802493 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((58229 / 10000000)) * ((1001 / 1000 + 52 / 1000) * ((625007137 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12939) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12939} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12939} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12939 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31863833 / 1000000000000000)) /
        (2 * (1 - eta) * ((58229 / 10000000)) ^ 2) +
        12939 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((58229 / 10000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12939} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12939) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12939 - 1))).real
      {v | sgA (paperDesignP 12939) c a v < rowSigma} ∂BstLean.Part161.muI 12939 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12939 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12939 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12939 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12939

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12939) : Prop :=
  ∫ a, (stdGauss (Fin (12939 - 1))).real
    {v | sgA (paperDesignP 12939) c a v < rowSigma} ∂muI 12939 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12939) : SplitData 12939 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12939}
    (hw : WINDOW (paperDesignP 12939) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12939)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12939).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12939} (t : ℝ)
    (hw : WINDOW (paperDesignP 12939) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12939)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12939) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12939) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12939} (hw : WINDOW (paperDesignP 12939) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12939) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12939) c (hqSplit c) ⊆ bulkIx (paperDesignP 12939) c :=
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
noncomputable def hqRootInputs {c : Ret 12939} (t : ℝ)
    (hw : WINDOW (paperDesignP 12939) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12939))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12939 t c BstLean.Part266.agent12939.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12939] at h ⊢
    linarith

end BstLean.Part266.Row12939

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12939) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12939) c (rowSplit c wl ws),
    ((12939 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12939 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12939) c (rowSplit c wl ws),
    ((12939 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12939 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12939 - 1)))
    (rowSplit c wl ws).good a ∂muI 12939 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12939) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12939 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12939) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12939 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12939) c (rowSplit c wl ws),
    hellG2 12939 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12939 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12939}
    (hw : WINDOW (paperDesignP 12939) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12939}
    (hw : WINDOW (paperDesignP 12939) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12939 t c BstLean.Part266.agent12939.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12939

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12939) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12939)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12939)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12939)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12939)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12939)

theorem paidBaseCertificate (H : Set (Ret 12939)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12939

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12939) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12939)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12939)} (h : TablePayment H) :
    (retDist (paperCentres 12939)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12939))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12939} (t : ℝ)
    (hw : WINDOW (paperDesignP 12939) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12939 t c BstLean.Part266.agent12939.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12939

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12939) (a : Ix 12939) : Fin (Js 12939) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12939) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12939) : Measure (Fin (Js 12939)) :=
  (muI 12939).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12939) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12939) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12939) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12939)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12939) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12939)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12939)
    (M : Matrix (Fin (mA 12939)) (Fin (mA 12939)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12939) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12939) (mA 12939) (tA 12939) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12939) (mA 12939) (tA 12939)).real
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

theorem table_second_layer_bad_subset (c : Ret 12939) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12939

/-! A first-layer variance payment from dimension 12939. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12939
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

theorem row_node_geometry {wr : WRet 12939} (hw : windowW wr)
    (θ : AHid 12939) {g : ℕ} (hg : g < Js 12939) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12939 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12939 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12939 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12939 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12939 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12939 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12939)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12939} (hw : windowW wr) :
    (gaussMat (mA 12939) 12939 (2 / (12939 : ℝ))).real {X | ∃ g < Js 12939,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12939 : ℝ)) ∨
      42 / (10 * (12939 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12939

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12940) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12940) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12940} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59662052187 / 500000) : ℝ) * ((1003 / 1000) * ((2954459 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((232907 / 40000000)) ^ 2 * ((1003 / 1000) * ((7964727 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((43179159 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1224967379 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((232907 / 40000000)) * ((1001 / 1000 + 52 / 1000) * ((508816317 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((43179159 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6018314523 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((232907 / 40000000)) * ((1001 / 1000 + 52 / 1000) * ((156239703 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12940) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12940} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12940} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12940 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((7964727 / 250000000000000)) /
        (2 * (1 - eta) * ((232907 / 40000000)) ^ 2) +
        12940 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((232907 / 40000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12940} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12940) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12940 - 1))).real
      {v | sgA (paperDesignP 12940) c a v < rowSigma} ∂BstLean.Part161.muI 12940 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12940 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12940 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12940 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12940

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12940) : Prop :=
  ∫ a, (stdGauss (Fin (12940 - 1))).real
    {v | sgA (paperDesignP 12940) c a v < rowSigma} ∂muI 12940 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12940) : SplitData 12940 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12940}
    (hw : WINDOW (paperDesignP 12940) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12940)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12940).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12940} (t : ℝ)
    (hw : WINDOW (paperDesignP 12940) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12940)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12940) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12940) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12940} (hw : WINDOW (paperDesignP 12940) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12940) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12940) c (hqSplit c) ⊆ bulkIx (paperDesignP 12940) c :=
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
noncomputable def hqRootInputs {c : Ret 12940} (t : ℝ)
    (hw : WINDOW (paperDesignP 12940) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12940))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12940 t c BstLean.Part266.agent12940.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12940] at h ⊢
    linarith

end BstLean.Part266.Row12940

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12940) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12940) c (rowSplit c wl ws),
    ((12940 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12940 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12940) c (rowSplit c wl ws),
    ((12940 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12940 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12940 - 1)))
    (rowSplit c wl ws).good a ∂muI 12940 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12940) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12940 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12940) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12940 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12940) c (rowSplit c wl ws),
    hellG2 12940 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12940 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12940}
    (hw : WINDOW (paperDesignP 12940) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12940}
    (hw : WINDOW (paperDesignP 12940) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12940 t c BstLean.Part266.agent12940.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12940

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12940) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12940)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12940)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12940)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12940)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12940)

theorem paidBaseCertificate (H : Set (Ret 12940)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12940

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12940) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12940)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12940)} (h : TablePayment H) :
    (retDist (paperCentres 12940)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12940))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12940} (t : ℝ)
    (hw : WINDOW (paperDesignP 12940) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12940 t c BstLean.Part266.agent12940.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12940

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12940) (a : Ix 12940) : Fin (Js 12940) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12940) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12940) : Measure (Fin (Js 12940)) :=
  (muI 12940).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12940) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12940) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12940) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12940)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12940) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12940)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12940)
    (M : Matrix (Fin (mA 12940)) (Fin (mA 12940)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12940) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12940) (mA 12940) (tA 12940) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12940) (mA 12940) (tA 12940)).real
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

theorem table_second_layer_bad_subset (c : Ret 12940) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12940

/-! A first-layer variance payment from dimension 12940. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12940
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

theorem row_node_geometry {wr : WRet 12940} (hw : windowW wr)
    (θ : AHid 12940) {g : ℕ} (hg : g < Js 12940) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12940 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12940 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12940 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12940 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12940 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12940 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12940)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12940} (hw : windowW wr) :
    (gaussMat (mA 12940) 12940 (2 / (12940 : ℝ))).real {X | ∃ g < Js 12940,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12940 : ℝ)) ∨
      42 / (10 * (12940 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12940

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12941) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12941) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12941} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((119333222637 / 1000000) : ℝ) * ((1003 / 1000) * ((1476887 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((116449 / 20000000)) ^ 2 * ((1003 / 1000) * ((31853983 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34544647 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((612412681 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((116449 / 20000000)) * ((1001 / 1000 + 52 / 1000) * ((254388493 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34544647 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1504404179 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((116449 / 20000000)) * ((1001 / 1000 + 52 / 1000) * ((124982099 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12941) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12941} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12941} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12941 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31853983 / 1000000000000000)) /
        (2 * (1 - eta) * ((116449 / 20000000)) ^ 2) +
        12941 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((116449 / 20000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12941} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12941) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12941 - 1))).real
      {v | sgA (paperDesignP 12941) c a v < rowSigma} ∂BstLean.Part161.muI 12941 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12941 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12941 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12941 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12941

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12941) : Prop :=
  ∫ a, (stdGauss (Fin (12941 - 1))).real
    {v | sgA (paperDesignP 12941) c a v < rowSigma} ∂muI 12941 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12941) : SplitData 12941 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12941}
    (hw : WINDOW (paperDesignP 12941) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12941)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12941).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12941} (t : ℝ)
    (hw : WINDOW (paperDesignP 12941) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12941)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12941) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12941) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12941} (hw : WINDOW (paperDesignP 12941) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12941) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12941) c (hqSplit c) ⊆ bulkIx (paperDesignP 12941) c :=
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
noncomputable def hqRootInputs {c : Ret 12941} (t : ℝ)
    (hw : WINDOW (paperDesignP 12941) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12941))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12941 t c BstLean.Part266.agent12941.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12941] at h ⊢
    linarith

end BstLean.Part266.Row12941

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12941) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12941) c (rowSplit c wl ws),
    ((12941 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12941 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12941) c (rowSplit c wl ws),
    ((12941 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12941 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12941 - 1)))
    (rowSplit c wl ws).good a ∂muI 12941 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12941) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12941 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12941) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12941 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12941) c (rowSplit c wl ws),
    hellG2 12941 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12941 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12941}
    (hw : WINDOW (paperDesignP 12941) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12941}
    (hw : WINDOW (paperDesignP 12941) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12941 t c BstLean.Part266.agent12941.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12941

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12941) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12941)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12941)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12941)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12941)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12941)

theorem paidBaseCertificate (H : Set (Ret 12941)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12941

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12941) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12941)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12941)} (h : TablePayment H) :
    (retDist (paperCentres 12941)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12941))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12941} (t : ℝ)
    (hw : WINDOW (paperDesignP 12941) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12941 t c BstLean.Part266.agent12941.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12941

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12941) (a : Ix 12941) : Fin (Js 12941) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12941) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12941) : Measure (Fin (Js 12941)) :=
  (muI 12941).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12941) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12941) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12941) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12941)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12941) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12941)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12941)
    (M : Matrix (Fin (mA 12941)) (Fin (mA 12941)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12941) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12941) (mA 12941) (tA 12941) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12941) (mA 12941) (tA 12941)).real
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

theorem table_second_layer_bad_subset (c : Ret 12941) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12941

/-! A first-layer variance payment from dimension 12941. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12941
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

theorem row_node_geometry {wr : WRet 12941} (hw : windowW wr)
    (θ : AHid 12941) {g : ℕ} (hg : g < Js 12941) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12941 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12941 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12941 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12941 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12941 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12941 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12941)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12941} (hw : windowW wr) :
    (gaussMat (mA 12941) 12941 (2 / (12941 : ℝ))).real {X | ∃ g < Js 12941,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12941 : ℝ)) ∨
      42 / (10 * (12941 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12941

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12942) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12942) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12942} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((4773693679 / 40000) : ℝ) * ((1003 / 1000) * ((2953089 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((232889 / 40000000)) ^ 2 * ((1003 / 1000) * ((31849061 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345459669 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((489873349 / 100000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((232889 / 40000000)) * ((1001 / 1000 + 52 / 1000) * ((25436883 / 50000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345459669 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6016919043 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((232889 / 40000000)) * ((1001 / 1000 + 52 / 1000) * ((124972437 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12942) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12942} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12942} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12942 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31849061 / 1000000000000000)) /
        (2 * (1 - eta) * ((232889 / 40000000)) ^ 2) +
        12942 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((232889 / 40000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12942} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12942) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12942 - 1))).real
      {v | sgA (paperDesignP 12942) c a v < rowSigma} ∂BstLean.Part161.muI 12942 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12942 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12942 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12942 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12942

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12942) : Prop :=
  ∫ a, (stdGauss (Fin (12942 - 1))).real
    {v | sgA (paperDesignP 12942) c a v < rowSigma} ∂muI 12942 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12942) : SplitData 12942 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12942}
    (hw : WINDOW (paperDesignP 12942) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12942)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12942).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12942} (t : ℝ)
    (hw : WINDOW (paperDesignP 12942) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12942)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12942) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12942) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12942} (hw : WINDOW (paperDesignP 12942) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12942) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12942) c (hqSplit c) ⊆ bulkIx (paperDesignP 12942) c :=
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
noncomputable def hqRootInputs {c : Ret 12942} (t : ℝ)
    (hw : WINDOW (paperDesignP 12942) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12942))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12942 t c BstLean.Part266.agent12942.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12942] at h ⊢
    linarith

end BstLean.Part266.Row12942

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12942) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12942) c (rowSplit c wl ws),
    ((12942 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12942 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12942) c (rowSplit c wl ws),
    ((12942 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12942 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12942 - 1)))
    (rowSplit c wl ws).good a ∂muI 12942 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12942) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12942 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12942) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12942 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12942) c (rowSplit c wl ws),
    hellG2 12942 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12942 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12942}
    (hw : WINDOW (paperDesignP 12942) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12942}
    (hw : WINDOW (paperDesignP 12942) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12942 t c BstLean.Part266.agent12942.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12942

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12942) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12942)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12942)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12942)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12942)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12942)

theorem paidBaseCertificate (H : Set (Ret 12942)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12942

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12942) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12942)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12942)} (h : TablePayment H) :
    (retDist (paperCentres 12942)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12942))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12942} (t : ℝ)
    (hw : WINDOW (paperDesignP 12942) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12942 t c BstLean.Part266.agent12942.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12942

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12942) (a : Ix 12942) : Fin (Js 12942) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12942) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12942) : Measure (Fin (Js 12942)) :=
  (muI 12942).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12942) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12942) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12942) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12942)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12942) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12942)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12942)
    (M : Matrix (Fin (mA 12942)) (Fin (mA 12942)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12942) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12942) (mA 12942) (tA 12942) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12942) (mA 12942) (tA 12942)).real
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

theorem table_second_layer_bad_subset (c : Ret 12942) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12942

/-! A first-layer variance payment from dimension 12942. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12942
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

theorem row_node_geometry {wr : WRet 12942} (hw : windowW wr)
    (θ : AHid 12942) {g : ℕ} (hg : g < Js 12942) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12942 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12942 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12942 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12942 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12942 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12942 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12942)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12942} (hw : windowW wr) :
    (gaussMat (mA 12942) 12942 (2 / (12942 : ℝ))).real {X | ∃ g < Js 12942,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12942 : ℝ)) ∨
      42 / (10 * (12942 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12942

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12943) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12943) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12943} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((119351421157 / 1000000) : ℝ) * ((1003 / 1000) * ((590481 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5822001 / 1000000000)) ^ 2 * ((1003 / 1000) * ((31844139 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34547281 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4898165641 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5822001 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((25434917 / 50000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34547281 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3008110753 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5822001 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((624813883 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12943) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12943} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12943} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12943 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31844139 / 1000000000000000)) /
        (2 * (1 - eta) * ((5822001 / 1000000000)) ^ 2) +
        12943 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5822001 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12943} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12943) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12943 - 1))).real
      {v | sgA (paperDesignP 12943) c a v < rowSigma} ∂BstLean.Part161.muI 12943 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12943 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12943 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12943 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12943

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12943) : Prop :=
  ∫ a, (stdGauss (Fin (12943 - 1))).real
    {v | sgA (paperDesignP 12943) c a v < rowSigma} ∂muI 12943 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12943) : SplitData 12943 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12943}
    (hw : WINDOW (paperDesignP 12943) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12943)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12943).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12943} (t : ℝ)
    (hw : WINDOW (paperDesignP 12943) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12943)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12943) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12943) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12943} (hw : WINDOW (paperDesignP 12943) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12943) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12943) c (hqSplit c) ⊆ bulkIx (paperDesignP 12943) c :=
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
noncomputable def hqRootInputs {c : Ret 12943} (t : ℝ)
    (hw : WINDOW (paperDesignP 12943) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12943))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12943 t c BstLean.Part266.agent12943.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12943] at h ⊢
    linarith

end BstLean.Part266.Row12943

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12943) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12943) c (rowSplit c wl ws),
    ((12943 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12943 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12943) c (rowSplit c wl ws),
    ((12943 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12943 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12943 - 1)))
    (rowSplit c wl ws).good a ∂muI 12943 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12943) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12943 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12943) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12943 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12943) c (rowSplit c wl ws),
    hellG2 12943 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12943 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12943}
    (hw : WINDOW (paperDesignP 12943) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12943}
    (hw : WINDOW (paperDesignP 12943) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12943 t c BstLean.Part266.agent12943.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12943

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12943) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12943)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12943)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12943)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12943)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12943)

theorem paidBaseCertificate (H : Set (Ret 12943)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12943

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12943) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12943)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12943)} (h : TablePayment H) :
    (retDist (paperCentres 12943)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12943))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12943} (t : ℝ)
    (hw : WINDOW (paperDesignP 12943) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12943 t c BstLean.Part266.agent12943.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12943

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12943) (a : Ix 12943) : Fin (Js 12943) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12943) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12943) : Measure (Fin (Js 12943)) :=
  (muI 12943).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12943) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12943) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12943) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12943)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12943) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12943)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12943)
    (M : Matrix (Fin (mA 12943)) (Fin (mA 12943)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12943) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12943) (mA 12943) (tA 12943) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12943) (mA 12943) (tA 12943)).real
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

theorem table_second_layer_bad_subset (c : Ret 12943) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12943

/-! A first-layer variance payment from dimension 12943. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12943
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

theorem row_node_geometry {wr : WRet 12943} (hw : windowW wr)
    (θ : AHid 12943) {g : ℕ} (hg : g < Js 12943) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12943 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12943 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12943 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12943 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12943 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12943 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12943)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12943} (hw : windowW wr) :
    (gaussMat (mA 12943) 12943 (2 / (12943 : ℝ))).real {X | ∃ g < Js 12943,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12943 : ℝ)) ∨
      42 / (10 * (12943 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12943

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12944) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12944) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12944} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59680271321 / 500000) : ℝ) * ((1003 / 1000) * ((73793 / 25000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((363861 / 62500000)) ^ 2 * ((1003 / 1000) * ((15919609 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345486011 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2448798951 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((363861 / 62500000)) * ((1001 / 1000 + 52 / 1000) * ((254329513 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345486011 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6015524103 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((363861 / 62500000)) * ((1001 / 1000 + 52 / 1000) * ((156191397 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12944) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12944} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12944} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12944 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((15919609 / 500000000000000)) /
        (2 * (1 - eta) * ((363861 / 62500000)) ^ 2) +
        12944 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((363861 / 62500000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12944} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12944) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12944 - 1))).real
      {v | sgA (paperDesignP 12944) c a v < rowSigma} ∂BstLean.Part161.muI 12944 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12944 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12944 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12944 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12944

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12944) : Prop :=
  ∫ a, (stdGauss (Fin (12944 - 1))).real
    {v | sgA (paperDesignP 12944) c a v < rowSigma} ∂muI 12944 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12944) : SplitData 12944 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12944}
    (hw : WINDOW (paperDesignP 12944) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12944)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12944).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12944} (t : ℝ)
    (hw : WINDOW (paperDesignP 12944) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12944)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12944) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12944) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12944} (hw : WINDOW (paperDesignP 12944) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12944) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12944) c (hqSplit c) ⊆ bulkIx (paperDesignP 12944) c :=
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
noncomputable def hqRootInputs {c : Ret 12944} (t : ℝ)
    (hw : WINDOW (paperDesignP 12944) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12944))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12944 t c BstLean.Part266.agent12944.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12944] at h ⊢
    linarith

end BstLean.Part266.Row12944

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12944) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12944) c (rowSplit c wl ws),
    ((12944 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12944 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12944) c (rowSplit c wl ws),
    ((12944 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12944 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12944 - 1)))
    (rowSplit c wl ws).good a ∂muI 12944 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12944) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12944 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12944) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12944 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12944) c (rowSplit c wl ws),
    hellG2 12944 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12944 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12944}
    (hw : WINDOW (paperDesignP 12944) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12944}
    (hw : WINDOW (paperDesignP 12944) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12944 t c BstLean.Part266.agent12944.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12944

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12944) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12944)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12944)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12944)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12944)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12944)

theorem paidBaseCertificate (H : Set (Ret 12944)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12944

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12944) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12944)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12944)} (h : TablePayment H) :
    (retDist (paperCentres 12944)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12944))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12944} (t : ℝ)
    (hw : WINDOW (paperDesignP 12944) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12944 t c BstLean.Part266.agent12944.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12944

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12944) (a : Ix 12944) : Fin (Js 12944) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12944) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12944) : Measure (Fin (Js 12944)) :=
  (muI 12944).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12944) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12944) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12944) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12944)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12944) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12944)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12944)
    (M : Matrix (Fin (mA 12944)) (Fin (mA 12944)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12944) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12944) (mA 12944) (tA 12944) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12944) (mA 12944) (tA 12944)).real
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

theorem table_second_layer_bad_subset (c : Ret 12944) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12944

/-! A first-layer variance payment from dimension 12944. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12944
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

theorem row_node_geometry {wr : WRet 12944} (hw : windowW wr)
    (θ : AHid 12944) {g : ℕ} (hg : g < Js 12944) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12944 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12944 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12944 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12944 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12944 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12944 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12944)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12944} (hw : windowW wr) :
    (gaussMat (mA 12944) 12944 (2 / (12944 : ℝ))).real {X | ∃ g < Js 12944,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12944 : ℝ)) ∨
      42 / (10 * (12944 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12944

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12945) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12945) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12945} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59684832601 / 500000) : ℝ) * ((1003 / 1000) * ((737759 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5821551 / 1000000000)) ^ 2 * ((1003 / 1000) * ((31834299 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345499213 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4897030273 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5821551 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((508619719 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345499213 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1202965367 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5821551 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((624717301 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12945) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12945} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12945} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12945 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31834299 / 1000000000000000)) /
        (2 * (1 - eta) * ((5821551 / 1000000000)) ^ 2) +
        12945 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5821551 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12945} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12945) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12945 - 1))).real
      {v | sgA (paperDesignP 12945) c a v < rowSigma} ∂BstLean.Part161.muI 12945 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12945 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12945 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12945 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12945

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12945) : Prop :=
  ∫ a, (stdGauss (Fin (12945 - 1))).real
    {v | sgA (paperDesignP 12945) c a v < rowSigma} ∂muI 12945 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12945) : SplitData 12945 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12945}
    (hw : WINDOW (paperDesignP 12945) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12945)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12945).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12945} (t : ℝ)
    (hw : WINDOW (paperDesignP 12945) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12945)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12945) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12945) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12945} (hw : WINDOW (paperDesignP 12945) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12945) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12945) c (hqSplit c) ⊆ bulkIx (paperDesignP 12945) c :=
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
noncomputable def hqRootInputs {c : Ret 12945} (t : ℝ)
    (hw : WINDOW (paperDesignP 12945) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12945))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12945 t c BstLean.Part266.agent12945.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12945] at h ⊢
    linarith

end BstLean.Part266.Row12945

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12945) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12945) c (rowSplit c wl ws),
    ((12945 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12945 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12945) c (rowSplit c wl ws),
    ((12945 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12945 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12945 - 1)))
    (rowSplit c wl ws).good a ∂muI 12945 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12945) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12945 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12945) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12945 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12945) c (rowSplit c wl ws),
    hellG2 12945 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12945 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12945}
    (hw : WINDOW (paperDesignP 12945) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12945}
    (hw : WINDOW (paperDesignP 12945) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12945 t c BstLean.Part266.agent12945.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12945

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12945) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12945)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12945)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12945)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12945)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12945)

theorem paidBaseCertificate (H : Set (Ret 12945)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12945

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12945) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12945)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12945)} (h : TablePayment H) :
    (retDist (paperCentres 12945)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12945))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12945} (t : ℝ)
    (hw : WINDOW (paperDesignP 12945) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12945 t c BstLean.Part266.agent12945.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12945

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12945) (a : Ix 12945) : Fin (Js 12945) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12945) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12945) : Measure (Fin (Js 12945)) :=
  (muI 12945).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12945) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12945) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12945) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12945)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12945) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12945)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12945)
    (M : Matrix (Fin (mA 12945)) (Fin (mA 12945)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12945) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12945) (mA 12945) (tA 12945) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12945) (mA 12945) (tA 12945)).real
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

theorem table_second_layer_bad_subset (c : Ret 12945) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12945

/-! A first-layer variance payment from dimension 12945. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12945
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

theorem row_node_geometry {wr : WRet 12945} (hw : windowW wr)
    (θ : AHid 12945) {g : ℕ} (hg : g < Js 12945) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12945 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12945 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12945 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12945 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12945 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12945 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12945)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12945} (hw : windowW wr) :
    (gaussMat (mA 12945) 12945 (2 / (12945 : ℝ))).real {X | ∃ g < Js 12945,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12945 : ℝ)) ∨
      42 / (10 * (12945 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12945

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12946) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12946) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12946} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((59689394419 / 500000) : ℝ) * ((1003 / 1000) * ((184397 / 62500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2910663 / 500000000)) ^ 2 * ((1003 / 1000) * ((1591469 / 50000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345512417 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2448231377 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2910663 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((254290209 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345512417 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6014129701 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2910663 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((624669021 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12946) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12946} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12946} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12946 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((1591469 / 50000000000000)) /
        (2 * (1 - eta) * ((2910663 / 500000000)) ^ 2) +
        12946 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2910663 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12946} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12946) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12946 - 1))).real
      {v | sgA (paperDesignP 12946) c a v < rowSigma} ∂BstLean.Part161.muI 12946 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12946 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12946 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12946 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12946

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12946) : Prop :=
  ∫ a, (stdGauss (Fin (12946 - 1))).real
    {v | sgA (paperDesignP 12946) c a v < rowSigma} ∂muI 12946 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12946) : SplitData 12946 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12946}
    (hw : WINDOW (paperDesignP 12946) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12946)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12946).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12946} (t : ℝ)
    (hw : WINDOW (paperDesignP 12946) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12946)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12946) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12946) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12946} (hw : WINDOW (paperDesignP 12946) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12946) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12946) c (hqSplit c) ⊆ bulkIx (paperDesignP 12946) c :=
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
noncomputable def hqRootInputs {c : Ret 12946} (t : ℝ)
    (hw : WINDOW (paperDesignP 12946) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12946))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12946 t c BstLean.Part266.agent12946.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12946] at h ⊢
    linarith

end BstLean.Part266.Row12946

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12946) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12946) c (rowSplit c wl ws),
    ((12946 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12946 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12946) c (rowSplit c wl ws),
    ((12946 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12946 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12946 - 1)))
    (rowSplit c wl ws).good a ∂muI 12946 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12946) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12946 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12946) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12946 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12946) c (rowSplit c wl ws),
    hellG2 12946 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12946 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12946}
    (hw : WINDOW (paperDesignP 12946) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12946}
    (hw : WINDOW (paperDesignP 12946) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12946 t c BstLean.Part266.agent12946.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12946

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12946) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12946)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12946)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12946)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12946)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12946)

theorem paidBaseCertificate (H : Set (Ret 12946)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12946

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12946) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12946)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12946)} (h : TablePayment H) :
    (retDist (paperCentres 12946)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12946))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12946} (t : ℝ)
    (hw : WINDOW (paperDesignP 12946) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12946 t c BstLean.Part266.agent12946.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12946

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12946) (a : Ix 12946) : Fin (Js 12946) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12946) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12946) : Measure (Fin (Js 12946)) :=
  (muI 12946).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12946) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12946) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12946) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12946)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12946) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12946)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12946)
    (M : Matrix (Fin (mA 12946)) (Fin (mA 12946)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12946) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12946) (mA 12946) (tA 12946) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12946) (mA 12946) (tA 12946)).real
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

theorem table_second_layer_bad_subset (c : Ret 12946) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12946

/-! A first-layer variance payment from dimension 12946. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12946
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

theorem row_node_geometry {wr : WRet 12946} (hw : windowW wr)
    (θ : AHid 12946) {g : ℕ} (hg : g < Js 12946) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12946 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12946 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12946 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12946 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12946 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12946 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12946)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12946} (hw : windowW wr) :
    (gaussMat (mA 12946) 12946 (2 / (12946 : ℝ))).real {X | ∃ g < Js 12946,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12946 : ℝ)) ∨
      42 / (10 * (12946 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12946

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12947) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12947) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12947} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((2387758271 / 20000) : ℝ) * ((1003 / 1000) * ((2949669 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5821101 / 1000000000)) ^ 2 * ((1003 / 1000) * ((31824463 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345525621 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((305993459 / 62500000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5821101 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((254270561 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345525621 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6013432703 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5821101 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((156155187 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12947) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12947} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12947} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12947 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31824463 / 1000000000000000)) /
        (2 * (1 - eta) * ((5821101 / 1000000000)) ^ 2) +
        12947 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5821101 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12947} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12947) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12947 - 1))).real
      {v | sgA (paperDesignP 12947) c a v < rowSigma} ∂BstLean.Part161.muI 12947 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12947 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12947 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12947 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12947

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12947) : Prop :=
  ∫ a, (stdGauss (Fin (12947 - 1))).real
    {v | sgA (paperDesignP 12947) c a v < rowSigma} ∂muI 12947 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12947) : SplitData 12947 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12947}
    (hw : WINDOW (paperDesignP 12947) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12947)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12947).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12947} (t : ℝ)
    (hw : WINDOW (paperDesignP 12947) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12947)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12947) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12947) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12947} (hw : WINDOW (paperDesignP 12947) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12947) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12947) c (hqSplit c) ⊆ bulkIx (paperDesignP 12947) c :=
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
noncomputable def hqRootInputs {c : Ret 12947} (t : ℝ)
    (hw : WINDOW (paperDesignP 12947) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12947))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12947 t c BstLean.Part266.agent12947.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12947] at h ⊢
    linarith

end BstLean.Part266.Row12947

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12947) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12947) c (rowSplit c wl ws),
    ((12947 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12947 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12947) c (rowSplit c wl ws),
    ((12947 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12947 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12947 - 1)))
    (rowSplit c wl ws).good a ∂muI 12947 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12947) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12947 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12947) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12947 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12947) c (rowSplit c wl ws),
    hellG2 12947 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12947 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12947}
    (hw : WINDOW (paperDesignP 12947) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12947}
    (hw : WINDOW (paperDesignP 12947) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12947 t c BstLean.Part266.agent12947.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12947

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12947) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12947)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12947)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12947)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12947)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12947)

theorem paidBaseCertificate (H : Set (Ret 12947)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12947

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12947) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12947)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12947)} (h : TablePayment H) :
    (retDist (paperCentres 12947)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12947))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12947} (t : ℝ)
    (hw : WINDOW (paperDesignP 12947) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12947 t c BstLean.Part266.agent12947.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12947

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12947) (a : Ix 12947) : Fin (Js 12947) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12947) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12947) : Measure (Fin (Js 12947)) :=
  (muI 12947).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12947) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12947) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12947) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12947)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12947) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12947)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12947)
    (M : Matrix (Fin (mA 12947)) (Fin (mA 12947)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12947) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12947) (mA 12947) (tA 12947) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12947) (mA 12947) (tA 12947)).real
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

theorem table_second_layer_bad_subset (c : Ret 12947) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12947

/-! A first-layer variance payment from dimension 12947. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12947
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

theorem row_node_geometry {wr : WRet 12947} (hw : windowW wr)
    (θ : AHid 12947) {g : ℕ} (hg : g < Js 12947) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12947 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12947 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12947 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12947 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12947 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12947 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12947)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12947} (hw : windowW wr) :
    (gaussMat (mA 12947) 12947 (2 / (12947 : ℝ))).real {X | ∃ g < Js 12947,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12947 : ℝ)) ∨
      42 / (10 * (12947 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12947

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12948) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12948) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12948} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((119397039339 / 1000000) : ℝ) * ((1003 / 1000) * ((589797 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1455219 / 250000000)) ^ 2 * ((1003 / 1000) * ((31819547 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172769413 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1223832011 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1455219 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((508501833 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((172769413 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6012735839 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1455219 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((624572483 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12948) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12948} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12948} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12948 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((31819547 / 1000000000000000)) /
        (2 * (1 - eta) * ((1455219 / 250000000)) ^ 2) +
        12948 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1455219 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12948} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12948) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12948 - 1))).real
      {v | sgA (paperDesignP 12948) c a v < rowSigma} ∂BstLean.Part161.muI 12948 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12948 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12948 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12948 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12948

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12948) : Prop :=
  ∫ a, (stdGauss (Fin (12948 - 1))).real
    {v | sgA (paperDesignP 12948) c a v < rowSigma} ∂muI 12948 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12948) : SplitData 12948 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12948}
    (hw : WINDOW (paperDesignP 12948) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12948)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12948).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12948} (t : ℝ)
    (hw : WINDOW (paperDesignP 12948) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12948)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12948) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12948) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12948} (hw : WINDOW (paperDesignP 12948) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12948) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12948) c (hqSplit c) ⊆ bulkIx (paperDesignP 12948) c :=
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
noncomputable def hqRootInputs {c : Ret 12948} (t : ℝ)
    (hw : WINDOW (paperDesignP 12948) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12948))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12948 t c BstLean.Part266.agent12948.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12948] at h ⊢
    linarith

end BstLean.Part266.Row12948

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12948) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12948) c (rowSplit c wl ws),
    ((12948 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12948 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12948) c (rowSplit c wl ws),
    ((12948 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12948 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12948 - 1)))
    (rowSplit c wl ws).good a ∂muI 12948 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12948) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12948 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12948) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12948 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12948) c (rowSplit c wl ws),
    hellG2 12948 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12948 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12948}
    (hw : WINDOW (paperDesignP 12948) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12948}
    (hw : WINDOW (paperDesignP 12948) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12948 t c BstLean.Part266.agent12948.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12948

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12948) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12948)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12948)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12948)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12948)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12948)

theorem paidBaseCertificate (H : Set (Ret 12948)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12948

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12948) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12948)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12948)} (h : TablePayment H) :
    (retDist (paperCentres 12948)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12948))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12948} (t : ℝ)
    (hw : WINDOW (paperDesignP 12948) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12948 t c BstLean.Part266.agent12948.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12948

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12948) (a : Ix 12948) : Fin (Js 12948) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12948) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12948) : Measure (Fin (Js 12948)) :=
  (muI 12948).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12948) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12948) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12948) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12948)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12948) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12948)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12948)
    (M : Matrix (Fin (mA 12948)) (Fin (mA 12948)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12948) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12948) (mA 12948) (tA 12948) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12948) (mA 12948) (tA 12948)).real
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

theorem table_second_layer_bad_subset (c : Ret 12948) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12948

/-! A first-layer variance payment from dimension 12948. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12948
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

theorem row_node_geometry {wr : WRet 12948} (hw : windowW wr)
    (θ : AHid 12948) {g : ℕ} (hg : g < Js 12948) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12948 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12948 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12948 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12948 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12948 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12948 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12948)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12948} (hw : windowW wr) :
    (gaussMat (mA 12948) 12948 (2 / (12948 : ℝ))).real {X | ∃ g < Js 12948,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12948 : ℝ)) ∨
      42 / (10 * (12948 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12948

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12949) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12949) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12949} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((7462882809 / 62500) : ℝ) * ((1003 / 1000) * ((1474151 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1455163 / 250000000)) ^ 2 * ((1003 / 1000) * ((3976829 / 125000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345551973 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4894760853 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1455163 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((10169251 / 20000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((345551973 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6012039109 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1455163 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((312262113 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12949) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12949} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12949} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12949 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((3976829 / 125000000000000)) /
        (2 * (1 - eta) * ((1455163 / 250000000)) ^ 2) +
        12949 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1455163 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12949} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12949) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12949 - 1))).real
      {v | sgA (paperDesignP 12949) c a v < rowSigma} ∂BstLean.Part161.muI 12949 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12949 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12949 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12949 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12949

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12949) : Prop :=
  ∫ a, (stdGauss (Fin (12949 - 1))).real
    {v | sgA (paperDesignP 12949) c a v < rowSigma} ∂muI 12949 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12949) : SplitData 12949 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12949}
    (hw : WINDOW (paperDesignP 12949) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12949)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12949).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12949} (t : ℝ)
    (hw : WINDOW (paperDesignP 12949) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12949)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12949) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12949) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12949} (hw : WINDOW (paperDesignP 12949) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12949) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12949) c (hqSplit c) ⊆ bulkIx (paperDesignP 12949) c :=
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
noncomputable def hqRootInputs {c : Ret 12949} (t : ℝ)
    (hw : WINDOW (paperDesignP 12949) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12949))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12949 t c BstLean.Part266.agent12949.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12949] at h ⊢
    linarith

end BstLean.Part266.Row12949

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12949) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12949) c (rowSplit c wl ws),
    ((12949 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12949 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12949) c (rowSplit c wl ws),
    ((12949 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12949 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12949 - 1)))
    (rowSplit c wl ws).good a ∂muI 12949 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12949) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12949 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12949) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12949 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12949) c (rowSplit c wl ws),
    hellG2 12949 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12949 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12949}
    (hw : WINDOW (paperDesignP 12949) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12949}
    (hw : WINDOW (paperDesignP 12949) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12949 t c BstLean.Part266.agent12949.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12949

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12949) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12949)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12949)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12949)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12949)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12949)

theorem paidBaseCertificate (H : Set (Ret 12949)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12949

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12949) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12949)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12949)} (h : TablePayment H) :
    (retDist (paperCentres 12949)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12949))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12949} (t : ℝ)
    (hw : WINDOW (paperDesignP 12949) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12949 t c BstLean.Part266.agent12949.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12949

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12949) (a : Ix 12949) : Fin (Js 12949) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12949) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12949) : Measure (Fin (Js 12949)) :=
  (muI 12949).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12949) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12949) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12949) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12949)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12949) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12949)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12949)
    (M : Matrix (Fin (mA 12949)) (Fin (mA 12949)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12949) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12949) (mA 12949) (tA 12949) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12949) (mA 12949) (tA 12949)).real
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

theorem table_second_layer_bad_subset (c : Ret 12949) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12949

/-! A first-layer variance payment from dimension 12949. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12949
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

theorem row_node_geometry {wr : WRet 12949} (hw : windowW wr)
    (θ : AHid 12949) {g : ℕ} (hg : g < Js 12949) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12949 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12949 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12949 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12949 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12949 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12949 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12949)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12949} (hw : windowW wr) :
    (gaussMat (mA 12949) 12949 (2 / (12949 : ℝ))).real {X | ∃ g < Js 12949,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12949 : ℝ)) ∨
      42 / (10 * (12949 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12949
