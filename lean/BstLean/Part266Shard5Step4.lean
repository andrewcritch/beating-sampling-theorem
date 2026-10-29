import BstLean.Part266Shard5Step3


/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12475) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12475) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12475} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((23016921659 / 200000) : ℝ) * ((1003 / 1000) * ((3297333 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5930201 / 1000000000)) ^ 2 * ((1003 / 1000) * ((34278521 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169620641 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((25882173 / 5000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5930201 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((263894531 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169620641 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6358045091 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5930201 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((32413301 / 50000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12475) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12475} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12475} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12475 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34278521 / 1000000000000000)) /
        (2 * (1 - eta) * ((5930201 / 1000000000)) ^ 2) +
        12475 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5930201 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12475} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12475) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12475 - 1))).real
      {v | sgA (paperDesignP 12475) c a v < rowSigma} ∂BstLean.Part161.muI 12475 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12475 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12475 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12475 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12475

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12475) : Prop :=
  ∫ a, (stdGauss (Fin (12475 - 1))).real
    {v | sgA (paperDesignP 12475) c a v < rowSigma} ∂muI 12475 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12475) : SplitData 12475 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12475}
    (hw : WINDOW (paperDesignP 12475) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12475)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12475).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12475} (t : ℝ)
    (hw : WINDOW (paperDesignP 12475) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12475)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12475) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12475) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12475} (hw : WINDOW (paperDesignP 12475) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12475) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12475) c (hqSplit c) ⊆ bulkIx (paperDesignP 12475) c :=
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
noncomputable def hqRootInputs {c : Ret 12475} (t : ℝ)
    (hw : WINDOW (paperDesignP 12475) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12475))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12475 t c BstLean.Part266.agent12475.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12475] at h ⊢
    linarith

end BstLean.Part266.Row12475

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12475) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12475) c (rowSplit c wl ws),
    ((12475 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12475 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12475) c (rowSplit c wl ws),
    ((12475 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12475 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12475 - 1)))
    (rowSplit c wl ws).good a ∂muI 12475 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12475) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12475 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12475) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12475 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12475) c (rowSplit c wl ws),
    hellG2 12475 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12475 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12475}
    (hw : WINDOW (paperDesignP 12475) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12475}
    (hw : WINDOW (paperDesignP 12475) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12475 t c BstLean.Part266.agent12475.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12475

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12475) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12475)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12475)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12475)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12475)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12475)

theorem paidBaseCertificate (H : Set (Ret 12475)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12475

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12475) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12475)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12475)} (h : TablePayment H) :
    (retDist (paperCentres 12475)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12475))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12475} (t : ℝ)
    (hw : WINDOW (paperDesignP 12475) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12475 t c BstLean.Part266.agent12475.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12475

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12475) (a : Ix 12475) : Fin (Js 12475) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12475) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12475) : Measure (Fin (Js 12475)) :=
  (muI 12475).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12475) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12475) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12475) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12475)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12475) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12475)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12475)
    (M : Matrix (Fin (mA 12475)) (Fin (mA 12475)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12475) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12475) (mA 12475) (tA 12475) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12475) (mA 12475) (tA 12475)).real
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

theorem table_second_layer_bad_subset (c : Ret 12475) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12475

/-! A first-layer variance payment from dimension 12475. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12475
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

theorem row_node_geometry {wr : WRet 12475} (hw : windowW wr)
    (θ : AHid 12475) {g : ℕ} (hg : g < Js 12475) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12475 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12475 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12475 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12475 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12475 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12475 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12475)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12475} (hw : windowW wr) :
    (gaussMat (mA 12475) 12475 (2 / (12475 : ℝ))).real {X | ∃ g < Js 12475,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12475 : ℝ)) ∨
      42 / (10 * (12475 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12475

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12476) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12476) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12476} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115093699347 / 1000000) : ℝ) * ((1003 / 1000) * ((164827 / 50000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1482491 / 250000000)) ^ 2 * ((1003 / 1000) * ((17136513 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339254681 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((631813 / 122070312500))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1482491 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((527746743 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339254681 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((794660051 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1482491 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((40513377 / 62500000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12476) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12476} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12476} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12476 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((17136513 / 500000000000000)) /
        (2 * (1 - eta) * ((1482491 / 250000000)) ^ 2) +
        12476 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1482491 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12476} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12476) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12476 - 1))).real
      {v | sgA (paperDesignP 12476) c a v < rowSigma} ∂BstLean.Part161.muI 12476 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12476 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12476 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12476 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12476

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12476) : Prop :=
  ∫ a, (stdGauss (Fin (12476 - 1))).real
    {v | sgA (paperDesignP 12476) c a v < rowSigma} ∂muI 12476 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12476) : SplitData 12476 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12476}
    (hw : WINDOW (paperDesignP 12476) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12476)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12476).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12476} (t : ℝ)
    (hw : WINDOW (paperDesignP 12476) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12476)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12476) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12476) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12476} (hw : WINDOW (paperDesignP 12476) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12476) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12476) c (hqSplit c) ⊆ bulkIx (paperDesignP 12476) c :=
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
noncomputable def hqRootInputs {c : Ret 12476} (t : ℝ)
    (hw : WINDOW (paperDesignP 12476) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12476))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12476 t c BstLean.Part266.agent12476.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12476] at h ⊢
    linarith

end BstLean.Part266.Row12476

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12476) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12476) c (rowSplit c wl ws),
    ((12476 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12476 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12476) c (rowSplit c wl ws),
    ((12476 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12476 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12476 - 1)))
    (rowSplit c wl ws).good a ∂muI 12476 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12476) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12476 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12476) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12476 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12476) c (rowSplit c wl ws),
    hellG2 12476 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12476 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12476}
    (hw : WINDOW (paperDesignP 12476) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12476}
    (hw : WINDOW (paperDesignP 12476) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12476 t c BstLean.Part266.agent12476.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12476

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12476) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12476)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12476)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12476)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12476)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12476)

theorem paidBaseCertificate (H : Set (Ret 12476)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12476

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12476) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12476)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12476)} (h : TablePayment H) :
    (retDist (paperCentres 12476)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12476))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12476} (t : ℝ)
    (hw : WINDOW (paperDesignP 12476) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12476 t c BstLean.Part266.agent12476.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12476

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12476) (a : Ix 12476) : Fin (Js 12476) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12476) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12476) : Measure (Fin (Js 12476)) :=
  (muI 12476).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12476) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12476) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12476) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12476)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12476) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12476)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12476)
    (M : Matrix (Fin (mA 12476)) (Fin (mA 12476)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12476) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12476) (mA 12476) (tA 12476) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12476) (mA 12476) (tA 12476)).real
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

theorem table_second_layer_bad_subset (c : Ret 12476) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12476

/-! A first-layer variance payment from dimension 12476. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12476
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

theorem row_node_geometry {wr : WRet 12476} (hw : windowW wr)
    (θ : AHid 12476) {g : ℕ} (hg : g < Js 12476) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12476 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12476 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12476 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12476 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12476 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12476 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12476)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12476} (hw : windowW wr) :
    (gaussMat (mA 12476) 12476 (2 / (12476 : ℝ))).real {X | ∃ g < Js 12476,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12476 : ℝ)) ∨
      42 / (10 * (12476 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12476

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12477) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12477) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12477} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((57551415279 / 500000) : ℝ) * ((1003 / 1000) * ((823937 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2964863 / 500000000)) ^ 2 * ((1003 / 1000) * ((34267531 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169634069 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1293797429 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2964863 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((52770443 / 100000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169634069 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3178257939 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2964863 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((162040513 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12477) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12477} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12477} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12477 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34267531 / 1000000000000000)) /
        (2 * (1 - eta) * ((2964863 / 500000000)) ^ 2) +
        12477 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2964863 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12477} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12477) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12477 - 1))).real
      {v | sgA (paperDesignP 12477) c a v < rowSigma} ∂BstLean.Part161.muI 12477 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12477 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12477 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12477 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12477

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12477) : Prop :=
  ∫ a, (stdGauss (Fin (12477 - 1))).real
    {v | sgA (paperDesignP 12477) c a v < rowSigma} ∂muI 12477 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12477) : SplitData 12477 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12477}
    (hw : WINDOW (paperDesignP 12477) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12477)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12477).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12477} (t : ℝ)
    (hw : WINDOW (paperDesignP 12477) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12477)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12477) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12477) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12477} (hw : WINDOW (paperDesignP 12477) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12477) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12477) c (hqSplit c) ⊆ bulkIx (paperDesignP 12477) c :=
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
noncomputable def hqRootInputs {c : Ret 12477} (t : ℝ)
    (hw : WINDOW (paperDesignP 12477) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12477))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12477 t c BstLean.Part266.agent12477.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12477] at h ⊢
    linarith

end BstLean.Part266.Row12477

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12477) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12477) c (rowSplit c wl ws),
    ((12477 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12477 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12477) c (rowSplit c wl ws),
    ((12477 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12477 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12477 - 1)))
    (rowSplit c wl ws).good a ∂muI 12477 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12477) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12477 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12477) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12477 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12477) c (rowSplit c wl ws),
    hellG2 12477 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12477 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12477}
    (hw : WINDOW (paperDesignP 12477) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12477}
    (hw : WINDOW (paperDesignP 12477) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12477 t c BstLean.Part266.agent12477.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12477

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12477) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12477)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12477)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12477)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12477)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12477)

theorem paidBaseCertificate (H : Set (Ret 12477)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12477

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12477) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12477)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12477)} (h : TablePayment H) :
    (retDist (paperCentres 12477)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12477))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12477} (t : ℝ)
    (hw : WINDOW (paperDesignP 12477) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12477 t c BstLean.Part266.agent12477.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12477

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12477) (a : Ix 12477) : Fin (Js 12477) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12477) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12477) : Measure (Fin (Js 12477)) :=
  (muI 12477).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12477) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12477) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12477) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12477)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12477) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12477)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12477)
    (M : Matrix (Fin (mA 12477)) (Fin (mA 12477)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12477) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12477) (mA 12477) (tA 12477) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12477) (mA 12477) (tA 12477)).real
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

theorem table_second_layer_bad_subset (c : Ret 12477) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12477

/-! A first-layer variance payment from dimension 12477. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12477
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

theorem row_node_geometry {wr : WRet 12477} (hw : windowW wr)
    (θ : AHid 12477) {g : ℕ} (hg : g < Js 12477) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12477 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12477 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12477 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12477 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12477 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12477 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12477)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12477} (hw : windowW wr) :
    (gaussMat (mA 12477) 12477 (2 / (12477 : ℝ))).real {X | ∃ g < Js 12477,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12477 : ℝ)) ∨
      42 / (10 * (12477 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12477

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12478) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12478) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12478} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((14388995361 / 125000) : ℝ) * ((1003 / 1000) * ((658991 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((370593 / 62500000)) ^ 2 * ((1003 / 1000) * ((17131019 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339281597 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2587283731 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((370593 / 62500000)) * ((1001 / 1000 + 52 / 1000) * ((131915531 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339281597 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((12711503 / 2000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((370593 / 62500000)) * ((1001 / 1000 + 52 / 1000) * ((648110081 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12478) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12478} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12478} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12478 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((17131019 / 500000000000000)) /
        (2 * (1 - eta) * ((370593 / 62500000)) ^ 2) +
        12478 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((370593 / 62500000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12478} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12478) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12478 - 1))).real
      {v | sgA (paperDesignP 12478) c a v < rowSigma} ∂BstLean.Part161.muI 12478 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12478 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12478 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12478 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12478

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12478) : Prop :=
  ∫ a, (stdGauss (Fin (12478 - 1))).real
    {v | sgA (paperDesignP 12478) c a v < rowSigma} ∂muI 12478 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12478) : SplitData 12478 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12478}
    (hw : WINDOW (paperDesignP 12478) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12478)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12478).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12478} (t : ℝ)
    (hw : WINDOW (paperDesignP 12478) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12478)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12478) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12478) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12478} (hw : WINDOW (paperDesignP 12478) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12478) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12478) c (hqSplit c) ⊆ bulkIx (paperDesignP 12478) c :=
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
noncomputable def hqRootInputs {c : Ret 12478} (t : ℝ)
    (hw : WINDOW (paperDesignP 12478) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12478))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12478 t c BstLean.Part266.agent12478.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12478] at h ⊢
    linarith

end BstLean.Part266.Row12478

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12478) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12478) c (rowSplit c wl ws),
    ((12478 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12478 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12478) c (rowSplit c wl ws),
    ((12478 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12478 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12478 - 1)))
    (rowSplit c wl ws).good a ∂muI 12478 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12478) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12478 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12478) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12478 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12478) c (rowSplit c wl ws),
    hellG2 12478 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12478 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12478}
    (hw : WINDOW (paperDesignP 12478) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12478}
    (hw : WINDOW (paperDesignP 12478) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12478 t c BstLean.Part266.agent12478.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12478

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12478) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12478)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12478)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12478)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12478)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12478)

theorem paidBaseCertificate (H : Set (Ret 12478)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12478

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12478) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12478)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12478)} (h : TablePayment H) :
    (retDist (paperCentres 12478)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12478))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12478} (t : ℝ)
    (hw : WINDOW (paperDesignP 12478) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12478 t c BstLean.Part266.agent12478.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12478

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12478) (a : Ix 12478) : Fin (Js 12478) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12478) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12478) : Measure (Fin (Js 12478)) :=
  (muI 12478).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12478) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12478) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12478) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12478)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12478) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12478)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12478)
    (M : Matrix (Fin (mA 12478)) (Fin (mA 12478)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12478) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12478) (mA 12478) (tA 12478) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12478) (mA 12478) (tA 12478)).real
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

theorem table_second_layer_bad_subset (c : Ret 12478) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12478

/-! A first-layer variance payment from dimension 12478. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12478
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

theorem row_node_geometry {wr : WRet 12478} (hw : windowW wr)
    (θ : AHid 12478) {g : ℕ} (hg : g < Js 12478) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12478 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12478 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12478 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12478 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12478 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12478 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12478)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12478} (hw : windowW wr) :
    (gaussMat (mA 12478) 12478 (2 / (12478 : ℝ))).real {X | ∃ g < Js 12478,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12478 : ℝ)) ∨
      42 / (10 * (12478 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12478

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12479) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12479) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12479} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115121057279 / 1000000) : ℝ) * ((1003 / 1000) * ((3294163 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5929251 / 1000000000)) ^ 2 * ((1003 / 1000) * ((34256547 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339294999 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5173945331 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5929251 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((21104793 / 40000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339294999 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6354987277 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5929251 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((324029059 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12479) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12479} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12479} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12479 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34256547 / 1000000000000000)) /
        (2 * (1 - eta) * ((5929251 / 1000000000)) ^ 2) +
        12479 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5929251 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12479} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12479) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12479 - 1))).real
      {v | sgA (paperDesignP 12479) c a v < rowSigma} ∂BstLean.Part161.muI 12479 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12479 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12479 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12479 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12479

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12479) : Prop :=
  ∫ a, (stdGauss (Fin (12479 - 1))).real
    {v | sgA (paperDesignP 12479) c a v < rowSigma} ∂muI 12479 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12479) : SplitData 12479 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12479}
    (hw : WINDOW (paperDesignP 12479) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12479)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12479).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12479} (t : ℝ)
    (hw : WINDOW (paperDesignP 12479) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12479)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12479) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12479) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12479} (hw : WINDOW (paperDesignP 12479) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12479) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12479) c (hqSplit c) ⊆ bulkIx (paperDesignP 12479) c :=
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
noncomputable def hqRootInputs {c : Ret 12479} (t : ℝ)
    (hw : WINDOW (paperDesignP 12479) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12479))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12479 t c BstLean.Part266.agent12479.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12479] at h ⊢
    linarith

end BstLean.Part266.Row12479

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12479) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12479) c (rowSplit c wl ws),
    ((12479 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12479 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12479) c (rowSplit c wl ws),
    ((12479 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12479 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12479 - 1)))
    (rowSplit c wl ws).good a ∂muI 12479 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12479) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12479 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12479) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12479 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12479) c (rowSplit c wl ws),
    hellG2 12479 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12479 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12479}
    (hw : WINDOW (paperDesignP 12479) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12479}
    (hw : WINDOW (paperDesignP 12479) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12479 t c BstLean.Part266.agent12479.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12479

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12479) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12479)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12479)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12479)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12479)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12479)

theorem paidBaseCertificate (H : Set (Ret 12479)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12479

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12479) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12479)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12479)} (h : TablePayment H) :
    (retDist (paperCentres 12479)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12479))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12479} (t : ℝ)
    (hw : WINDOW (paperDesignP 12479) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12479 t c BstLean.Part266.agent12479.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12479

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12479) (a : Ix 12479) : Fin (Js 12479) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12479) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12479) : Measure (Fin (Js 12479)) :=
  (muI 12479).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12479) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12479) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12479) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12479)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12479) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12479)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12479)
    (M : Matrix (Fin (mA 12479)) (Fin (mA 12479)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12479) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12479) (mA 12479) (tA 12479) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12479) (mA 12479) (tA 12479)).real
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

theorem table_second_layer_bad_subset (c : Ret 12479) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12479

/-! A first-layer variance payment from dimension 12479. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12479
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

theorem row_node_geometry {wr : WRet 12479} (hw : windowW wr)
    (θ : AHid 12479) {g : ℕ} (hg : g < Js 12479) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12479 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12479 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12479 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12479 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12479 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12479 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12479)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12479} (hw : windowW wr) :
    (gaussMat (mA 12479) 12479 (2 / (12479 : ℝ))).real {X | ∃ g < Js 12479,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12479 : ℝ)) ∨
      42 / (10 * (12479 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12479

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12480) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12480) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12480} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115130191843 / 1000000) : ℝ) * ((1003 / 1000) * ((3293371 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5929013 / 1000000000)) ^ 2 * ((1003 / 1000) * ((34251057 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((16965423 / 50000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2586661663 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5929013 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((131894383 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((16965423 / 50000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3177111603 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5929013 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((648006163 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12480) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12480} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12480} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12480 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34251057 / 1000000000000000)) /
        (2 * (1 - eta) * ((5929013 / 1000000000)) ^ 2) +
        12480 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5929013 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12480} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12480) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12480 - 1))).real
      {v | sgA (paperDesignP 12480) c a v < rowSigma} ∂BstLean.Part161.muI 12480 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12480 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12480 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12480 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12480

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12480) : Prop :=
  ∫ a, (stdGauss (Fin (12480 - 1))).real
    {v | sgA (paperDesignP 12480) c a v < rowSigma} ∂muI 12480 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12480) : SplitData 12480 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12480}
    (hw : WINDOW (paperDesignP 12480) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12480)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12480).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12480} (t : ℝ)
    (hw : WINDOW (paperDesignP 12480) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12480)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12480) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12480) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12480} (hw : WINDOW (paperDesignP 12480) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12480) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12480) c (hqSplit c) ⊆ bulkIx (paperDesignP 12480) c :=
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
noncomputable def hqRootInputs {c : Ret 12480} (t : ℝ)
    (hw : WINDOW (paperDesignP 12480) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12480))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12480 t c BstLean.Part266.agent12480.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12480] at h ⊢
    linarith

end BstLean.Part266.Row12480

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12480) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12480) c (rowSplit c wl ws),
    ((12480 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12480 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12480) c (rowSplit c wl ws),
    ((12480 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12480 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12480 - 1)))
    (rowSplit c wl ws).good a ∂muI 12480 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12480) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12480 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12480) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12480 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12480) c (rowSplit c wl ws),
    hellG2 12480 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12480 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12480}
    (hw : WINDOW (paperDesignP 12480) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12480}
    (hw : WINDOW (paperDesignP 12480) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12480 t c BstLean.Part266.agent12480.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12480

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12480) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12480)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12480)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12480)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12480)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12480)

theorem paidBaseCertificate (H : Set (Ret 12480)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12480

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12480) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12480)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12480)} (h : TablePayment H) :
    (retDist (paperCentres 12480)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12480))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12480} (t : ℝ)
    (hw : WINDOW (paperDesignP 12480) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12480 t c BstLean.Part266.agent12480.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12480

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12480) (a : Ix 12480) : Fin (Js 12480) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12480) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12480) : Measure (Fin (Js 12480)) :=
  (muI 12480).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12480) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12480) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12480) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12480)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12480) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12480)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12480)
    (M : Matrix (Fin (mA 12480)) (Fin (mA 12480)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12480) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12480) (mA 12480) (tA 12480) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12480) (mA 12480) (tA 12480)).real
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

theorem table_second_layer_bad_subset (c : Ret 12480) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12480

/-! A first-layer variance payment from dimension 12480. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12480
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

theorem row_node_geometry {wr : WRet 12480} (hw : windowW wr)
    (θ : AHid 12480) {g : ℕ} (hg : g < Js 12480) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12480 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12480 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12480 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12480 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12480 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12480 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12480)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12480} (hw : windowW wr) :
    (gaussMat (mA 12480) 12480 (2 / (12480 : ℝ))).real {X | ∃ g < Js 12480,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12480 : ℝ)) ∨
      42 / (10 * (12480 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12480

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12481) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12481) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12481} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115139288459 / 1000000) : ℝ) * ((1003 / 1000) * ((164629 / 50000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((741097 / 125000000)) ^ 2 * ((1003 / 1000) * ((535087 / 15625000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42415233 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1034540289 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((741097 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((527535247 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42415233 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((794182411 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((741097 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((80994277 / 125000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12481) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12481} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12481} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12481 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((535087 / 15625000000000)) /
        (2 * (1 - eta) * ((741097 / 125000000)) ^ 2) +
        12481 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((741097 / 125000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12481} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12481) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12481 - 1))).real
      {v | sgA (paperDesignP 12481) c a v < rowSigma} ∂BstLean.Part161.muI 12481 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12481 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12481 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12481 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12481

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12481) : Prop :=
  ∫ a, (stdGauss (Fin (12481 - 1))).real
    {v | sgA (paperDesignP 12481) c a v < rowSigma} ∂muI 12481 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12481) : SplitData 12481 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12481}
    (hw : WINDOW (paperDesignP 12481) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12481)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12481).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12481} (t : ℝ)
    (hw : WINDOW (paperDesignP 12481) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12481)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12481) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12481) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12481} (hw : WINDOW (paperDesignP 12481) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12481) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12481) c (hqSplit c) ⊆ bulkIx (paperDesignP 12481) c :=
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
noncomputable def hqRootInputs {c : Ret 12481} (t : ℝ)
    (hw : WINDOW (paperDesignP 12481) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12481))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12481 t c BstLean.Part266.agent12481.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12481] at h ⊢
    linarith

end BstLean.Part266.Row12481

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12481) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12481) c (rowSplit c wl ws),
    ((12481 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12481 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12481) c (rowSplit c wl ws),
    ((12481 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12481 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12481 - 1)))
    (rowSplit c wl ws).good a ∂muI 12481 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12481) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12481 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12481) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12481 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12481) c (rowSplit c wl ws),
    hellG2 12481 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12481 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12481}
    (hw : WINDOW (paperDesignP 12481) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12481}
    (hw : WINDOW (paperDesignP 12481) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12481 t c BstLean.Part266.agent12481.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12481

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12481) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12481)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12481)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12481)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12481)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12481)

theorem paidBaseCertificate (H : Set (Ret 12481)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12481

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12481) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12481)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12481)} (h : TablePayment H) :
    (retDist (paperCentres 12481)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12481))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12481} (t : ℝ)
    (hw : WINDOW (paperDesignP 12481) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12481 t c BstLean.Part266.agent12481.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12481

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12481) (a : Ix 12481) : Fin (Js 12481) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12481) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12481) : Measure (Fin (Js 12481)) :=
  (muI 12481).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12481) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12481) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12481) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12481)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12481) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12481)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12481)
    (M : Matrix (Fin (mA 12481)) (Fin (mA 12481)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12481) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12481) (mA 12481) (tA 12481) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12481) (mA 12481) (tA 12481)).real
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

theorem table_second_layer_bad_subset (c : Ret 12481) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12481

/-! A first-layer variance payment from dimension 12481. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12481
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

theorem row_node_geometry {wr : WRet 12481} (hw : windowW wr)
    (θ : AHid 12481) {g : ℕ} (hg : g < Js 12481) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12481 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12481 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12481 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12481 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12481 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12481 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12481)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12481} (hw : windowW wr) :
    (gaussMat (mA 12481) 12481 (2 / (12481 : ℝ))).real {X | ∃ g < Js 12481,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12481 : ℝ)) ∨
      42 / (10 * (12481 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12481

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12482) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12482) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12482} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((57574212629 / 500000) : ℝ) * ((1003 / 1000) * ((822947 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2964269 / 500000000)) ^ 2 * ((1003 / 1000) * ((428001 / 12500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339335327 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5172079689 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2964269 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((65936621 / 125000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339335327 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1588173881 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2964269 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((323951139 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12482) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12482} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12482} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12482 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((428001 / 12500000000000)) /
        (2 * (1 - eta) * ((2964269 / 500000000)) ^ 2) +
        12482 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2964269 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12482} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12482) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12482 - 1))).real
      {v | sgA (paperDesignP 12482) c a v < rowSigma} ∂BstLean.Part161.muI 12482 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12482 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12482 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12482 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12482

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12482) : Prop :=
  ∫ a, (stdGauss (Fin (12482 - 1))).real
    {v | sgA (paperDesignP 12482) c a v < rowSigma} ∂muI 12482 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12482) : SplitData 12482 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12482}
    (hw : WINDOW (paperDesignP 12482) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12482)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12482).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12482} (t : ℝ)
    (hw : WINDOW (paperDesignP 12482) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12482)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12482) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12482) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12482} (hw : WINDOW (paperDesignP 12482) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12482) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12482) c (hqSplit c) ⊆ bulkIx (paperDesignP 12482) c :=
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
noncomputable def hqRootInputs {c : Ret 12482} (t : ℝ)
    (hw : WINDOW (paperDesignP 12482) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12482))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12482 t c BstLean.Part266.agent12482.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12482] at h ⊢
    linarith

end BstLean.Part266.Row12482

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12482) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12482) c (rowSplit c wl ws),
    ((12482 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12482 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12482) c (rowSplit c wl ws),
    ((12482 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12482 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12482 - 1)))
    (rowSplit c wl ws).good a ∂muI 12482 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12482) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12482 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12482) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12482 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12482) c (rowSplit c wl ws),
    hellG2 12482 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12482 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12482}
    (hw : WINDOW (paperDesignP 12482) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12482}
    (hw : WINDOW (paperDesignP 12482) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12482 t c BstLean.Part266.agent12482.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12482

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12482) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12482)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12482)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12482)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12482)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12482)

theorem paidBaseCertificate (H : Set (Ret 12482)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12482

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12482) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12482)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12482)} (h : TablePayment H) :
    (retDist (paperCentres 12482)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12482))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12482} (t : ℝ)
    (hw : WINDOW (paperDesignP 12482) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12482 t c BstLean.Part266.agent12482.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12482

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12482) (a : Ix 12482) : Fin (Js 12482) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12482) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12482) : Measure (Fin (Js 12482)) :=
  (muI 12482).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12482) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12482) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12482) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12482)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12482) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12482)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12482)
    (M : Matrix (Fin (mA 12482)) (Fin (mA 12482)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12482) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12482) (mA 12482) (tA 12482) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12482) (mA 12482) (tA 12482)).real
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

theorem table_second_layer_bad_subset (c : Ret 12482) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12482

/-! A first-layer variance payment from dimension 12482. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12482
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

theorem row_node_geometry {wr : WRet 12482} (hw : windowW wr)
    (θ : AHid 12482) {g : ℕ} (hg : g < Js 12482) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12482 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12482 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12482 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12482 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12482 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12482 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12482)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12482} (hw : windowW wr) :
    (gaussMat (mA 12482) 12482 (2 / (12482 : ℝ))).real {X | ∃ g < Js 12482,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12482 : ℝ)) ∨
      42 / (10 * (12482 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12482

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12483) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12483) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12483} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115157524099 / 1000000) : ℝ) * ((1003 / 1000) * ((3290997 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5928301 / 1000000000)) ^ 2 * ((1003 / 1000) * ((17117297 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169674367 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5171458057 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5928301 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((105490139 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169674367 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((793991489 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5928301 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((161962587 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12483) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12483} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12483} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12483 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((17117297 / 500000000000000)) /
        (2 * (1 - eta) * ((5928301 / 1000000000)) ^ 2) +
        12483 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5928301 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12483} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12483) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12483 - 1))).real
      {v | sgA (paperDesignP 12483) c a v < rowSigma} ∂BstLean.Part161.muI 12483 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12483 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12483 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12483 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12483

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12483) : Prop :=
  ∫ a, (stdGauss (Fin (12483 - 1))).real
    {v | sgA (paperDesignP 12483) c a v < rowSigma} ∂muI 12483 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12483) : SplitData 12483 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12483}
    (hw : WINDOW (paperDesignP 12483) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12483)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12483).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12483} (t : ℝ)
    (hw : WINDOW (paperDesignP 12483) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12483)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12483) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12483) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12483} (hw : WINDOW (paperDesignP 12483) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12483) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12483) c (hqSplit c) ⊆ bulkIx (paperDesignP 12483) c :=
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
noncomputable def hqRootInputs {c : Ret 12483} (t : ℝ)
    (hw : WINDOW (paperDesignP 12483) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12483))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12483 t c BstLean.Part266.agent12483.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12483] at h ⊢
    linarith

end BstLean.Part266.Row12483

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12483) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12483) c (rowSplit c wl ws),
    ((12483 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12483 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12483) c (rowSplit c wl ws),
    ((12483 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12483 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12483 - 1)))
    (rowSplit c wl ws).good a ∂muI 12483 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12483) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12483 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12483) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12483 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12483) c (rowSplit c wl ws),
    hellG2 12483 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12483 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12483}
    (hw : WINDOW (paperDesignP 12483) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12483}
    (hw : WINDOW (paperDesignP 12483) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12483 t c BstLean.Part266.agent12483.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12483

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12483) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12483)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12483)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12483)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12483)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12483)

theorem paidBaseCertificate (H : Set (Ret 12483)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12483

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12483) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12483)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12483)} (h : TablePayment H) :
    (retDist (paperCentres 12483)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12483))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12483} (t : ℝ)
    (hw : WINDOW (paperDesignP 12483) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12483 t c BstLean.Part266.agent12483.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12483

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12483) (a : Ix 12483) : Fin (Js 12483) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12483) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12483) : Measure (Fin (Js 12483)) :=
  (muI 12483).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12483) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12483) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12483) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12483)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12483) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12483)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12483)
    (M : Matrix (Fin (mA 12483)) (Fin (mA 12483)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12483) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12483) (mA 12483) (tA 12483) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12483) (mA 12483) (tA 12483)).real
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

theorem table_second_layer_bad_subset (c : Ret 12483) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12483

/-! A first-layer variance payment from dimension 12483. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12483
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

theorem row_node_geometry {wr : WRet 12483} (hw : windowW wr)
    (θ : AHid 12483) {g : ℕ} (hg : g < Js 12483) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12483 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12483 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12483 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12483 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12483 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12483 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12483)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12483} (hw : windowW wr) :
    (gaussMat (mA 12483) 12483 (2 / (12483 : ℝ))).real {X | ∃ g < Js 12483,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12483 : ℝ)) ∨
      42 / (10 * (12483 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12483

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12484) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12484) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12484} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((57583331567 / 500000) : ℝ) * ((1003 / 1000) * ((1645103 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5928063 / 1000000000)) ^ 2 * ((1003 / 1000) * ((34229109 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339362199 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5170836549 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5928063 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((52740843 / 100000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339362199 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6351168453 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5928063 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((647798427 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12484) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12484} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12484} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12484 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34229109 / 1000000000000000)) /
        (2 * (1 - eta) * ((5928063 / 1000000000)) ^ 2) +
        12484 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5928063 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12484} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12484) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12484 - 1))).real
      {v | sgA (paperDesignP 12484) c a v < rowSigma} ∂BstLean.Part161.muI 12484 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12484 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12484 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12484 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12484

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12484) : Prop :=
  ∫ a, (stdGauss (Fin (12484 - 1))).real
    {v | sgA (paperDesignP 12484) c a v < rowSigma} ∂muI 12484 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12484) : SplitData 12484 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12484}
    (hw : WINDOW (paperDesignP 12484) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12484)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12484).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12484} (t : ℝ)
    (hw : WINDOW (paperDesignP 12484) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12484)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12484) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12484) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12484} (hw : WINDOW (paperDesignP 12484) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12484) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12484) c (hqSplit c) ⊆ bulkIx (paperDesignP 12484) c :=
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
noncomputable def hqRootInputs {c : Ret 12484} (t : ℝ)
    (hw : WINDOW (paperDesignP 12484) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12484))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12484 t c BstLean.Part266.agent12484.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12484] at h ⊢
    linarith

end BstLean.Part266.Row12484

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12484) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12484) c (rowSplit c wl ws),
    ((12484 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12484 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12484) c (rowSplit c wl ws),
    ((12484 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12484 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12484 - 1)))
    (rowSplit c wl ws).good a ∂muI 12484 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12484) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12484 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12484) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12484 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12484) c (rowSplit c wl ws),
    hellG2 12484 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12484 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12484}
    (hw : WINDOW (paperDesignP 12484) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12484}
    (hw : WINDOW (paperDesignP 12484) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12484 t c BstLean.Part266.agent12484.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12484

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12484) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12484)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12484)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12484)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12484)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12484)

theorem paidBaseCertificate (H : Set (Ret 12484)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12484

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12484) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12484)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12484)} (h : TablePayment H) :
    (retDist (paperCentres 12484)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12484))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12484} (t : ℝ)
    (hw : WINDOW (paperDesignP 12484) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12484 t c BstLean.Part266.agent12484.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12484

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12484) (a : Ix 12484) : Fin (Js 12484) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12484) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12484) : Measure (Fin (Js 12484)) :=
  (muI 12484).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12484) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12484) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12484) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12484)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12484) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12484)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12484)
    (M : Matrix (Fin (mA 12484)) (Fin (mA 12484)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12484) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12484) (mA 12484) (tA 12484) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12484) (mA 12484) (tA 12484)).real
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

theorem table_second_layer_bad_subset (c : Ret 12484) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12484

/-! A first-layer variance payment from dimension 12484. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12484
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

theorem row_node_geometry {wr : WRet 12484} (hw : windowW wr)
    (θ : AHid 12484) {g : ℕ} (hg : g < Js 12484) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12484 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12484 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12484 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12484 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12484 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12484 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12484)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12484} (hw : windowW wr) :
    (gaussMat (mA 12484) 12484 (2 / (12484 : ℝ))).real {X | ∃ g < Js 12484,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12484 : ℝ)) ∨
      42 / (10 * (12484 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12484

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12485) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12485) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12485} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((57587882101 / 500000) : ℝ) * ((1003 / 1000) * ((411177 / 125000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2963913 / 500000000)) ^ 2 * ((1003 / 1000) * ((273789 / 8000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42421951 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5170215167 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2963913 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((527366171 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42421951 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1587601287 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2963913 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((323873257 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12485) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12485} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12485} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12485 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((273789 / 8000000000000)) /
        (2 * (1 - eta) * ((2963913 / 500000000)) ^ 2) +
        12485 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2963913 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12485} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12485) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12485 - 1))).real
      {v | sgA (paperDesignP 12485) c a v < rowSigma} ∂BstLean.Part161.muI 12485 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12485 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12485 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12485 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12485

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12485) : Prop :=
  ∫ a, (stdGauss (Fin (12485 - 1))).real
    {v | sgA (paperDesignP 12485) c a v < rowSigma} ∂muI 12485 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12485) : SplitData 12485 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12485}
    (hw : WINDOW (paperDesignP 12485) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12485)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12485).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12485} (t : ℝ)
    (hw : WINDOW (paperDesignP 12485) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12485)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12485) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12485) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12485} (hw : WINDOW (paperDesignP 12485) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12485) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12485) c (hqSplit c) ⊆ bulkIx (paperDesignP 12485) c :=
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
noncomputable def hqRootInputs {c : Ret 12485} (t : ℝ)
    (hw : WINDOW (paperDesignP 12485) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12485))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12485 t c BstLean.Part266.agent12485.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12485] at h ⊢
    linarith

end BstLean.Part266.Row12485

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12485) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12485) c (rowSplit c wl ws),
    ((12485 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12485 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12485) c (rowSplit c wl ws),
    ((12485 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12485 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12485 - 1)))
    (rowSplit c wl ws).good a ∂muI 12485 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12485) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12485 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12485) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12485 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12485) c (rowSplit c wl ws),
    hellG2 12485 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12485 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12485}
    (hw : WINDOW (paperDesignP 12485) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12485}
    (hw : WINDOW (paperDesignP 12485) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12485 t c BstLean.Part266.agent12485.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12485

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12485) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12485)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12485)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12485)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12485)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12485)

theorem paidBaseCertificate (H : Set (Ret 12485)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12485

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12485) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12485)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12485)} (h : TablePayment H) :
    (retDist (paperCentres 12485)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12485))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12485} (t : ℝ)
    (hw : WINDOW (paperDesignP 12485) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12485 t c BstLean.Part266.agent12485.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12485

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12485) (a : Ix 12485) : Fin (Js 12485) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12485) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12485) : Measure (Fin (Js 12485)) :=
  (muI 12485).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12485) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12485) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12485) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12485)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12485) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12485)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12485)
    (M : Matrix (Fin (mA 12485)) (Fin (mA 12485)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12485) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12485) (mA 12485) (tA 12485) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12485) (mA 12485) (tA 12485)).real
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

theorem table_second_layer_bad_subset (c : Ret 12485) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12485

/-! A first-layer variance payment from dimension 12485. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12485
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

theorem row_node_geometry {wr : WRet 12485} (hw : windowW wr)
    (θ : AHid 12485) {g : ℕ} (hg : g < Js 12485) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12485 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12485 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12485 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12485 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12485 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12485 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12485)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12485} (hw : windowW wr) :
    (gaussMat (mA 12485) 12485 (2 / (12485 : ℝ))).real {X | ∃ g < Js 12485,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12485 : ℝ)) ∨
      42 / (10 * (12485 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12485

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12486) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12486) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12486} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115184866381 / 1000000) : ℝ) * ((1003 / 1000) * ((26309 / 8000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5927589 / 1000000000)) ^ 2 * ((1003 / 1000) * ((34218143 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169694509 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1292398477 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5927589 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((6591549 / 12500000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169694509 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1269928399 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5927589 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((647694609 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12486) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12486} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12486} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12486 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34218143 / 1000000000000000)) /
        (2 * (1 - eta) * ((5927589 / 1000000000)) ^ 2) +
        12486 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5927589 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12486} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12486) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12486 - 1))).real
      {v | sgA (paperDesignP 12486) c a v < rowSigma} ∂BstLean.Part161.muI 12486 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12486 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12486 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12486 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12486

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12486) : Prop :=
  ∫ a, (stdGauss (Fin (12486 - 1))).real
    {v | sgA (paperDesignP 12486) c a v < rowSigma} ∂muI 12486 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12486) : SplitData 12486 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12486}
    (hw : WINDOW (paperDesignP 12486) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12486)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12486).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12486} (t : ℝ)
    (hw : WINDOW (paperDesignP 12486) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12486)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12486) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12486) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12486} (hw : WINDOW (paperDesignP 12486) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12486) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12486) c (hqSplit c) ⊆ bulkIx (paperDesignP 12486) c :=
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
noncomputable def hqRootInputs {c : Ret 12486} (t : ℝ)
    (hw : WINDOW (paperDesignP 12486) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12486))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12486 t c BstLean.Part266.agent12486.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12486] at h ⊢
    linarith

end BstLean.Part266.Row12486

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12486) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12486) c (rowSplit c wl ws),
    ((12486 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12486 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12486) c (rowSplit c wl ws),
    ((12486 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12486 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12486 - 1)))
    (rowSplit c wl ws).good a ∂muI 12486 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12486) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12486 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12486) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12486 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12486) c (rowSplit c wl ws),
    hellG2 12486 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12486 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12486}
    (hw : WINDOW (paperDesignP 12486) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12486}
    (hw : WINDOW (paperDesignP 12486) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12486 t c BstLean.Part266.agent12486.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12486

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12486) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12486)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12486)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12486)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12486)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12486)

theorem paidBaseCertificate (H : Set (Ret 12486)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12486

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12486) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12486)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12486)} (h : TablePayment H) :
    (retDist (paperCentres 12486)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12486))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12486} (t : ℝ)
    (hw : WINDOW (paperDesignP 12486) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12486 t c BstLean.Part266.agent12486.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12486

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12486) (a : Ix 12486) : Fin (Js 12486) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12486) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12486) : Measure (Fin (Js 12486)) :=
  (muI 12486).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12486) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12486) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12486) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12486)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12486) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12486)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12486)
    (M : Matrix (Fin (mA 12486)) (Fin (mA 12486)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12486) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12486) (mA 12486) (tA 12486) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12486) (mA 12486) (tA 12486)).real
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

theorem table_second_layer_bad_subset (c : Ret 12486) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12486

/-! A first-layer variance payment from dimension 12486. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12486
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

theorem row_node_geometry {wr : WRet 12486} (hw : windowW wr)
    (θ : AHid 12486) {g : ℕ} (hg : g < Js 12486) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12486 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12486 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12486 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12486 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12486 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12486 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12486)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12486} (hw : windowW wr) :
    (gaussMat (mA 12486) 12486 (2 / (12486 : ℝ))).real {X | ∃ g < Js 12486,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12486 : ℝ)) ∨
      42 / (10 * (12486 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12486

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12487) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12487) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12487} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((1799906387 / 15625) : ℝ) * ((1003 / 1000) * ((657567 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5927351 / 1000000000)) ^ 2 * ((1003 / 1000) * ((17106331 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169701243 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2584486387 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5927351 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((21091267 / 40000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((169701243 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1269775799 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5927351 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((80955339 / 125000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12487) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12487} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12487} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12487 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((17106331 / 500000000000000)) /
        (2 * (1 - eta) * ((5927351 / 1000000000)) ^ 2) +
        12487 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5927351 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12487} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12487) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12487 - 1))).real
      {v | sgA (paperDesignP 12487) c a v < rowSigma} ∂BstLean.Part161.muI 12487 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12487 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12487 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12487 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12487

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12487) : Prop :=
  ∫ a, (stdGauss (Fin (12487 - 1))).real
    {v | sgA (paperDesignP 12487) c a v < rowSigma} ∂muI 12487 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12487) : SplitData 12487 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12487}
    (hw : WINDOW (paperDesignP 12487) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12487)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12487).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12487} (t : ℝ)
    (hw : WINDOW (paperDesignP 12487) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12487)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12487) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12487) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12487} (hw : WINDOW (paperDesignP 12487) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12487) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12487) c (hqSplit c) ⊆ bulkIx (paperDesignP 12487) c :=
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
noncomputable def hqRootInputs {c : Ret 12487} (t : ℝ)
    (hw : WINDOW (paperDesignP 12487) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12487))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12487 t c BstLean.Part266.agent12487.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12487] at h ⊢
    linarith

end BstLean.Part266.Row12487

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12487) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12487) c (rowSplit c wl ws),
    ((12487 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12487 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12487) c (rowSplit c wl ws),
    ((12487 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12487 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12487 - 1)))
    (rowSplit c wl ws).good a ∂muI 12487 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12487) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12487 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12487) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12487 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12487) c (rowSplit c wl ws),
    hellG2 12487 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12487 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12487}
    (hw : WINDOW (paperDesignP 12487) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12487}
    (hw : WINDOW (paperDesignP 12487) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12487 t c BstLean.Part266.agent12487.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12487

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12487) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12487)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12487)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12487)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12487)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12487)

theorem paidBaseCertificate (H : Set (Ret 12487)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12487

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12487) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12487)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12487)} (h : TablePayment H) :
    (retDist (paperCentres 12487)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12487))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12487} (t : ℝ)
    (hw : WINDOW (paperDesignP 12487) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12487 t c BstLean.Part266.agent12487.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12487

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12487) (a : Ix 12487) : Fin (Js 12487) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12487) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12487) : Measure (Fin (Js 12487)) :=
  (muI 12487).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12487) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12487) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12487) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12487)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12487) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12487)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12487)
    (M : Matrix (Fin (mA 12487)) (Fin (mA 12487)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12487) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12487) (mA 12487) (tA 12487) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12487) (mA 12487) (tA 12487)).real
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

theorem table_second_layer_bad_subset (c : Ret 12487) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12487

/-! A first-layer variance payment from dimension 12487. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12487
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

theorem row_node_geometry {wr : WRet 12487} (hw : windowW wr)
    (θ : AHid 12487) {g : ℕ} (hg : g < Js 12487) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12487 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12487 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12487 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12487 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12487 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12487 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12487)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12487} (hw : windowW wr) :
    (gaussMat (mA 12487) 12487 (2 / (12487 : ℝ))).real {X | ∃ g < Js 12487,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12487 : ℝ)) ∨
      42 / (10 * (12487 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12487

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12488) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12488) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12488} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((57601556587 / 500000) : ℝ) * ((1003 / 1000) * ((657409 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2963557 / 500000000)) ^ 2 * ((1003 / 1000) * ((17103591 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339415899 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1033670353 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2963557 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((131809859 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339415899 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1587029037 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2963557 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((80948853 / 125000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12488) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12488} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12488} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12488 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((17103591 / 500000000000000)) /
        (2 * (1 - eta) * ((2963557 / 500000000)) ^ 2) +
        12488 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2963557 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12488} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12488) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12488 - 1))).real
      {v | sgA (paperDesignP 12488) c a v < rowSigma} ∂BstLean.Part161.muI 12488 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12488 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12488 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12488 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12488

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12488) : Prop :=
  ∫ a, (stdGauss (Fin (12488 - 1))).real
    {v | sgA (paperDesignP 12488) c a v < rowSigma} ∂muI 12488 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12488) : SplitData 12488 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12488}
    (hw : WINDOW (paperDesignP 12488) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12488)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12488).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12488} (t : ℝ)
    (hw : WINDOW (paperDesignP 12488) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12488)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12488) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12488) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12488} (hw : WINDOW (paperDesignP 12488) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12488) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12488) c (hqSplit c) ⊆ bulkIx (paperDesignP 12488) c :=
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
noncomputable def hqRootInputs {c : Ret 12488} (t : ℝ)
    (hw : WINDOW (paperDesignP 12488) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12488))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12488 t c BstLean.Part266.agent12488.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12488] at h ⊢
    linarith

end BstLean.Part266.Row12488

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12488) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12488) c (rowSplit c wl ws),
    ((12488 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12488 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12488) c (rowSplit c wl ws),
    ((12488 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12488 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12488 - 1)))
    (rowSplit c wl ws).good a ∂muI 12488 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12488) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12488 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12488) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12488 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12488) c (rowSplit c wl ws),
    hellG2 12488 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12488 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12488}
    (hw : WINDOW (paperDesignP 12488) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12488}
    (hw : WINDOW (paperDesignP 12488) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12488 t c BstLean.Part266.agent12488.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12488

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12488) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12488)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12488)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12488)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12488)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12488)

theorem paidBaseCertificate (H : Set (Ret 12488)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12488

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12488) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12488)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12488)} (h : TablePayment H) :
    (retDist (paperCentres 12488)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12488))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12488} (t : ℝ)
    (hw : WINDOW (paperDesignP 12488) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12488 t c BstLean.Part266.agent12488.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12488

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12488) (a : Ix 12488) : Fin (Js 12488) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12488) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12488) : Measure (Fin (Js 12488)) :=
  (muI 12488).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12488) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12488) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12488) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12488)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12488) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12488)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12488)
    (M : Matrix (Fin (mA 12488)) (Fin (mA 12488)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12488) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12488) (mA 12488) (tA 12488) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12488) (mA 12488) (tA 12488)).real
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

theorem table_second_layer_bad_subset (c : Ret 12488) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12488

/-! A first-layer variance payment from dimension 12488. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12488
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

theorem row_node_geometry {wr : WRet 12488} (hw : windowW wr)
    (θ : AHid 12488) {g : ℕ} (hg : g < Js 12488) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12488 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12488 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12488 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12488 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12488 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12488 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12488)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12488} (hw : windowW wr) :
    (gaussMat (mA 12488) 12488 (2 / (12488 : ℝ))).real {X | ∃ g < Js 12488,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12488 : ℝ)) ∨
      42 / (10 * (12488 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12488

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12489) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12489) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12489} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115212218693 / 1000000) : ℝ) * ((1003 / 1000) * ((205391 / 62500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5926877 / 1000000000)) ^ 2 * ((1003 / 1000) * ((4275213 / 125000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((5303583 / 15625) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5167730879 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5926877 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((105439441 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((5303583 / 15625) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6347353453 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5926877 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((2529449 / 3906250000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12489) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12489} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12489} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12489 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((4275213 / 125000000000000)) /
        (2 * (1 - eta) * ((5926877 / 1000000000)) ^ 2) +
        12489 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5926877 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12489} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12489) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12489 - 1))).real
      {v | sgA (paperDesignP 12489) c a v < rowSigma} ∂BstLean.Part161.muI 12489 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12489 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12489 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12489 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12489

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12489) : Prop :=
  ∫ a, (stdGauss (Fin (12489 - 1))).real
    {v | sgA (paperDesignP 12489) c a v < rowSigma} ∂muI 12489 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12489) : SplitData 12489 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12489}
    (hw : WINDOW (paperDesignP 12489) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12489)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12489).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12489} (t : ℝ)
    (hw : WINDOW (paperDesignP 12489) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12489)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12489) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12489) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12489} (hw : WINDOW (paperDesignP 12489) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12489) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12489) c (hqSplit c) ⊆ bulkIx (paperDesignP 12489) c :=
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
noncomputable def hqRootInputs {c : Ret 12489} (t : ℝ)
    (hw : WINDOW (paperDesignP 12489) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12489))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12489 t c BstLean.Part266.agent12489.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12489] at h ⊢
    linarith

end BstLean.Part266.Row12489

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12489) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12489) c (rowSplit c wl ws),
    ((12489 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12489 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12489) c (rowSplit c wl ws),
    ((12489 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12489 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12489 - 1)))
    (rowSplit c wl ws).good a ∂muI 12489 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12489) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12489 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12489) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12489 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12489) c (rowSplit c wl ws),
    hellG2 12489 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12489 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12489}
    (hw : WINDOW (paperDesignP 12489) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12489}
    (hw : WINDOW (paperDesignP 12489) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12489 t c BstLean.Part266.agent12489.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12489

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12489) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12489)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12489)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12489)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12489)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12489)

theorem paidBaseCertificate (H : Set (Ret 12489)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12489

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12489) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12489)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12489)} (h : TablePayment H) :
    (retDist (paperCentres 12489)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12489))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12489} (t : ℝ)
    (hw : WINDOW (paperDesignP 12489) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12489 t c BstLean.Part266.agent12489.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12489

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12489) (a : Ix 12489) : Fin (Js 12489) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12489) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12489) : Measure (Fin (Js 12489)) :=
  (muI 12489).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12489) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12489) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12489) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12489)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12489) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12489)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12489)
    (M : Matrix (Fin (mA 12489)) (Fin (mA 12489)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12489) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12489) (mA 12489) (tA 12489) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12489) (mA 12489) (tA 12489)).real
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

theorem table_second_layer_bad_subset (c : Ret 12489) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12489

/-! A first-layer variance payment from dimension 12489. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12489
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

theorem row_node_geometry {wr : WRet 12489} (hw : windowW wr)
    (θ : AHid 12489) {g : ℕ} (hg : g < Js 12489) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12489 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12489 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12489 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12489 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12489 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12489 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12489)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12489} (hw : windowW wr) :
    (gaussMat (mA 12489) 12489 (2 / (12489 : ℝ))).real {X | ∃ g < Js 12489,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12489 : ℝ)) ∨
      42 / (10 * (12489 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12489

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12490) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12490) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12490} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115221364433 / 1000000) : ℝ) * ((1003 / 1000) * ((3285467 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5926639 / 1000000000)) ^ 2 * ((1003 / 1000) * ((17098113 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((10607587 / 31250) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2583555059 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5926639 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((26357749 / 50000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((10607587 / 31250) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6346590911 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5926639 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((647487073 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12490) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12490} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12490} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12490 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((17098113 / 500000000000000)) /
        (2 * (1 - eta) * ((5926639 / 1000000000)) ^ 2) +
        12490 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5926639 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12490} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12490) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12490 - 1))).real
      {v | sgA (paperDesignP 12490) c a v < rowSigma} ∂BstLean.Part161.muI 12490 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12490 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12490 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12490 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12490

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12490) : Prop :=
  ∫ a, (stdGauss (Fin (12490 - 1))).real
    {v | sgA (paperDesignP 12490) c a v < rowSigma} ∂muI 12490 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12490) : SplitData 12490 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12490}
    (hw : WINDOW (paperDesignP 12490) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12490)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12490).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12490} (t : ℝ)
    (hw : WINDOW (paperDesignP 12490) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12490)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12490) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12490) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12490} (hw : WINDOW (paperDesignP 12490) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12490) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12490) c (hqSplit c) ⊆ bulkIx (paperDesignP 12490) c :=
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
noncomputable def hqRootInputs {c : Ret 12490} (t : ℝ)
    (hw : WINDOW (paperDesignP 12490) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12490))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12490 t c BstLean.Part266.agent12490.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12490] at h ⊢
    linarith

end BstLean.Part266.Row12490

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12490) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12490) c (rowSplit c wl ws),
    ((12490 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12490 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12490) c (rowSplit c wl ws),
    ((12490 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12490 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12490 - 1)))
    (rowSplit c wl ws).good a ∂muI 12490 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12490) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12490 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12490) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12490 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12490) c (rowSplit c wl ws),
    hellG2 12490 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12490 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12490}
    (hw : WINDOW (paperDesignP 12490) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12490}
    (hw : WINDOW (paperDesignP 12490) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12490 t c BstLean.Part266.agent12490.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12490

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12490) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12490)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12490)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12490)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12490)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12490)

theorem paidBaseCertificate (H : Set (Ret 12490)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12490

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12490) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12490)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12490)} (h : TablePayment H) :
    (retDist (paperCentres 12490)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12490))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12490} (t : ℝ)
    (hw : WINDOW (paperDesignP 12490) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12490 t c BstLean.Part266.agent12490.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12490

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12490) (a : Ix 12490) : Fin (Js 12490) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12490) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12490) : Measure (Fin (Js 12490)) :=
  (muI 12490).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12490) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12490) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12490) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12490)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12490) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12490)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12490)
    (M : Matrix (Fin (mA 12490)) (Fin (mA 12490)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12490) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12490) (mA 12490) (tA 12490) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12490) (mA 12490) (tA 12490)).real
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

theorem table_second_layer_bad_subset (c : Ret 12490) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12490

/-! A first-layer variance payment from dimension 12490. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12490
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

theorem row_node_geometry {wr : WRet 12490} (hw : windowW wr)
    (θ : AHid 12490) {g : ℕ} (hg : g < Js 12490) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12490 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12490 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12490 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12490 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12490 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12490 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12490)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12490} (hw : windowW wr) :
    (gaussMat (mA 12490) 12490 (2 / (12490 : ℝ))).real {X | ∃ g < Js 12490,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12490 : ℝ)) ∨
      42 / (10 * (12490 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12490

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12491) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12491) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12491} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115230472181 / 1000000) : ℝ) * ((1003 / 1000) * ((3284677 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2963201 / 500000000)) ^ 2 * ((1003 / 1000) * ((34190751 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339456199 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2583244741 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2963201 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((263556381 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339456199 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3172914261 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2963201 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((647435209 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12491) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12491} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12491} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12491 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34190751 / 1000000000000000)) /
        (2 * (1 - eta) * ((2963201 / 500000000)) ^ 2) +
        12491 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2963201 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12491} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12491) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12491 - 1))).real
      {v | sgA (paperDesignP 12491) c a v < rowSigma} ∂BstLean.Part161.muI 12491 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12491 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12491 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12491 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12491

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12491) : Prop :=
  ∫ a, (stdGauss (Fin (12491 - 1))).real
    {v | sgA (paperDesignP 12491) c a v < rowSigma} ∂muI 12491 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12491) : SplitData 12491 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12491}
    (hw : WINDOW (paperDesignP 12491) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12491)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12491).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12491} (t : ℝ)
    (hw : WINDOW (paperDesignP 12491) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12491)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12491) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12491) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12491} (hw : WINDOW (paperDesignP 12491) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12491) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12491) c (hqSplit c) ⊆ bulkIx (paperDesignP 12491) c :=
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
noncomputable def hqRootInputs {c : Ret 12491} (t : ℝ)
    (hw : WINDOW (paperDesignP 12491) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12491))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12491 t c BstLean.Part266.agent12491.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12491] at h ⊢
    linarith

end BstLean.Part266.Row12491

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12491) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12491) c (rowSplit c wl ws),
    ((12491 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12491 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12491) c (rowSplit c wl ws),
    ((12491 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12491 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12491 - 1)))
    (rowSplit c wl ws).good a ∂muI 12491 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12491) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12491 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12491) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12491 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12491) c (rowSplit c wl ws),
    hellG2 12491 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12491 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12491}
    (hw : WINDOW (paperDesignP 12491) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12491}
    (hw : WINDOW (paperDesignP 12491) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12491 t c BstLean.Part266.agent12491.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12491

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12491) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12491)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12491)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12491)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12491)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12491)

theorem paidBaseCertificate (H : Set (Ret 12491)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12491

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12491) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12491)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12491)} (h : TablePayment H) :
    (retDist (paperCentres 12491)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12491))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12491} (t : ℝ)
    (hw : WINDOW (paperDesignP 12491) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12491 t c BstLean.Part266.agent12491.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12491

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12491) (a : Ix 12491) : Fin (Js 12491) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12491) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12491) : Measure (Fin (Js 12491)) :=
  (muI 12491).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12491) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12491) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12491) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12491)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12491) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12491)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12491)
    (M : Matrix (Fin (mA 12491)) (Fin (mA 12491)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12491) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12491) (mA 12491) (tA 12491) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12491) (mA 12491) (tA 12491)).real
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

theorem table_second_layer_bad_subset (c : Ret 12491) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12491

/-! A first-layer variance payment from dimension 12491. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12491
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

theorem row_node_geometry {wr : WRet 12491} (hw : windowW wr)
    (θ : AHid 12491) {g : ℕ} (hg : g < Js 12491) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12491 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12491 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12491 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12491 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12491 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12491 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12491)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12491} (hw : windowW wr) :
    (gaussMat (mA 12491) 12491 (2 / (12491 : ℝ))).real {X | ∃ g < Js 12491,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12491 : ℝ)) ∨
      42 / (10 * (12491 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12491

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12492) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12492) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12492} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((1440494763 / 12500) : ℝ) * ((1003 / 1000) * ((3283889 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1185233 / 200000000)) ^ 2 * ((1003 / 1000) * ((8546319 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((21216851 / 62500) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5165868969 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1185233 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((527070551 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((21216851 / 62500) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3172533143 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1185233 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((323691677 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12492) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12492} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12492} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12492 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((8546319 / 250000000000000)) /
        (2 * (1 - eta) * ((1185233 / 200000000)) ^ 2) +
        12492 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1185233 / 200000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12492} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12492) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12492 - 1))).real
      {v | sgA (paperDesignP 12492) c a v < rowSigma} ∂BstLean.Part161.muI 12492 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12492 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12492 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12492 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12492

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12492) : Prop :=
  ∫ a, (stdGauss (Fin (12492 - 1))).real
    {v | sgA (paperDesignP 12492) c a v < rowSigma} ∂muI 12492 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12492) : SplitData 12492 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12492}
    (hw : WINDOW (paperDesignP 12492) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12492)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12492).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12492} (t : ℝ)
    (hw : WINDOW (paperDesignP 12492) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12492)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12492) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12492) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12492} (hw : WINDOW (paperDesignP 12492) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12492) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12492) c (hqSplit c) ⊆ bulkIx (paperDesignP 12492) c :=
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
noncomputable def hqRootInputs {c : Ret 12492} (t : ℝ)
    (hw : WINDOW (paperDesignP 12492) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12492))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12492 t c BstLean.Part266.agent12492.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12492] at h ⊢
    linarith

end BstLean.Part266.Row12492

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12492) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12492) c (rowSplit c wl ws),
    ((12492 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12492 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12492) c (rowSplit c wl ws),
    ((12492 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12492 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12492 - 1)))
    (rowSplit c wl ws).good a ∂muI 12492 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12492) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12492 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12492) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12492 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12492) c (rowSplit c wl ws),
    hellG2 12492 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12492 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12492}
    (hw : WINDOW (paperDesignP 12492) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12492}
    (hw : WINDOW (paperDesignP 12492) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12492 t c BstLean.Part266.agent12492.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12492

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12492) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12492)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12492)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12492)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12492)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12492)

theorem paidBaseCertificate (H : Set (Ret 12492)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12492

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12492) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12492)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12492)} (h : TablePayment H) :
    (retDist (paperCentres 12492)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12492))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12492} (t : ℝ)
    (hw : WINDOW (paperDesignP 12492) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12492 t c BstLean.Part266.agent12492.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12492

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12492) (a : Ix 12492) : Fin (Js 12492) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12492) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12492) : Measure (Fin (Js 12492)) :=
  (muI 12492).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12492) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12492) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12492) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12492)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12492) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12492)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12492)
    (M : Matrix (Fin (mA 12492)) (Fin (mA 12492)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12492) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12492) (mA 12492) (tA 12492) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12492) (mA 12492) (tA 12492)).real
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

theorem table_second_layer_bad_subset (c : Ret 12492) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12492

/-! A first-layer variance payment from dimension 12492. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12492
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

theorem row_node_geometry {wr : WRet 12492} (hw : windowW wr)
    (θ : AHid 12492) {g : ℕ} (hg : g < Js 12492) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12492 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12492 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12492 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12492 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12492 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12492 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12492)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12492} (hw : windowW wr) :
    (gaussMat (mA 12492) 12492 (2 / (12492 : ℝ))).real {X | ∃ g < Js 12492,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12492 : ℝ)) ∨
      42 / (10 * (12492 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12492

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12493) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12493) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12493} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((28812172753 / 250000) : ℝ) * ((1003 / 1000) * ((32831 / 10000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((740741 / 125000000)) ^ 2 * ((1003 / 1000) * ((34179803 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339483033 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5165248581 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((740741 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((263514173 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339483033 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3172152101 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((740741 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((161832877 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12493) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12493} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12493} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12493 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34179803 / 1000000000000000)) /
        (2 * (1 - eta) * ((740741 / 125000000)) ^ 2) +
        12493 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((740741 / 125000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12493} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12493) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12493 - 1))).real
      {v | sgA (paperDesignP 12493) c a v < rowSigma} ∂BstLean.Part161.muI 12493 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12493 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12493 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12493 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12493

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12493) : Prop :=
  ∫ a, (stdGauss (Fin (12493 - 1))).real
    {v | sgA (paperDesignP 12493) c a v < rowSigma} ∂muI 12493 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12493) : SplitData 12493 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12493}
    (hw : WINDOW (paperDesignP 12493) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12493)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12493).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12493} (t : ℝ)
    (hw : WINDOW (paperDesignP 12493) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12493)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12493) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12493) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12493} (hw : WINDOW (paperDesignP 12493) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12493) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12493) c (hqSplit c) ⊆ bulkIx (paperDesignP 12493) c :=
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
noncomputable def hqRootInputs {c : Ret 12493} (t : ℝ)
    (hw : WINDOW (paperDesignP 12493) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12493))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12493 t c BstLean.Part266.agent12493.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12493] at h ⊢
    linarith

end BstLean.Part266.Row12493

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12493) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12493) c (rowSplit c wl ws),
    ((12493 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12493 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12493) c (rowSplit c wl ws),
    ((12493 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12493 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12493 - 1)))
    (rowSplit c wl ws).good a ∂muI 12493 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12493) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12493 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12493) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12493 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12493) c (rowSplit c wl ws),
    hellG2 12493 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12493 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12493}
    (hw : WINDOW (paperDesignP 12493) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12493}
    (hw : WINDOW (paperDesignP 12493) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12493 t c BstLean.Part266.agent12493.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12493

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12493) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12493)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12493)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12493)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12493)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12493)

theorem paidBaseCertificate (H : Set (Ret 12493)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12493

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12493) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12493)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12493)} (h : TablePayment H) :
    (retDist (paperCentres 12493)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12493))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12493} (t : ℝ)
    (hw : WINDOW (paperDesignP 12493) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12493 t c BstLean.Part266.agent12493.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12493

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12493) (a : Ix 12493) : Fin (Js 12493) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12493) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12493) : Measure (Fin (Js 12493)) :=
  (muI 12493).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12493) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12493) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12493) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12493)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12493) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12493)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12493)
    (M : Matrix (Fin (mA 12493)) (Fin (mA 12493)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12493) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12493) (mA 12493) (tA 12493) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12493) (mA 12493) (tA 12493)).real
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

theorem table_second_layer_bad_subset (c : Ret 12493) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12493

/-! A first-layer variance payment from dimension 12493. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12493
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

theorem row_node_geometry {wr : WRet 12493} (hw : windowW wr)
    (θ : AHid 12493) {g : ℕ} (hg : g < Js 12493) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12493 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12493 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12493 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12493 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12493 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12493 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12493)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12493} (hw : windowW wr) :
    (gaussMat (mA 12493) 12493 (2 / (12493 : ℝ))).real {X | ∃ g < Js 12493,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12493 : ℝ)) ∨
      42 / (10 * (12493 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12493

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12494) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12494) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12494} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((7203612631 / 62500) : ℝ) * ((1003 / 1000) * ((410289 / 125000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5925691 / 1000000000)) ^ 2 * ((1003 / 1000) * ((34174331 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((84874113 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5164628317 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5925691 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((526986149 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((84874113 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6343542271 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5925691 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((647279669 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12494) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12494} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12494} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12494 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34174331 / 1000000000000000)) /
        (2 * (1 - eta) * ((5925691 / 1000000000)) ^ 2) +
        12494 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5925691 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12494} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12494) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12494 - 1))).real
      {v | sgA (paperDesignP 12494) c a v < rowSigma} ∂BstLean.Part161.muI 12494 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12494 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12494 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12494 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12494

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12494) : Prop :=
  ∫ a, (stdGauss (Fin (12494 - 1))).real
    {v | sgA (paperDesignP 12494) c a v < rowSigma} ∂muI 12494 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12494) : SplitData 12494 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12494}
    (hw : WINDOW (paperDesignP 12494) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12494)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12494).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12494} (t : ℝ)
    (hw : WINDOW (paperDesignP 12494) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12494)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12494) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12494) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12494} (hw : WINDOW (paperDesignP 12494) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12494) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12494) c (hqSplit c) ⊆ bulkIx (paperDesignP 12494) c :=
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
noncomputable def hqRootInputs {c : Ret 12494} (t : ℝ)
    (hw : WINDOW (paperDesignP 12494) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12494))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12494 t c BstLean.Part266.agent12494.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12494] at h ⊢
    linarith

end BstLean.Part266.Row12494

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12494) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12494) c (rowSplit c wl ws),
    ((12494 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12494 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12494) c (rowSplit c wl ws),
    ((12494 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12494 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12494 - 1)))
    (rowSplit c wl ws).good a ∂muI 12494 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12494) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12494 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12494) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12494 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12494) c (rowSplit c wl ws),
    hellG2 12494 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12494 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12494}
    (hw : WINDOW (paperDesignP 12494) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12494}
    (hw : WINDOW (paperDesignP 12494) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12494 t c BstLean.Part266.agent12494.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12494

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12494) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12494)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12494)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12494)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12494)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12494)

theorem paidBaseCertificate (H : Set (Ret 12494)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12494

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12494) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12494)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12494)} (h : TablePayment H) :
    (retDist (paperCentres 12494)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12494))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12494} (t : ℝ)
    (hw : WINDOW (paperDesignP 12494) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12494 t c BstLean.Part266.agent12494.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12494

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12494) (a : Ix 12494) : Fin (Js 12494) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12494) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12494) : Measure (Fin (Js 12494)) :=
  (muI 12494).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12494) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12494) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12494) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12494)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12494) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12494)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12494)
    (M : Matrix (Fin (mA 12494)) (Fin (mA 12494)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12494) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12494) (mA 12494) (tA 12494) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12494) (mA 12494) (tA 12494)).real
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

theorem table_second_layer_bad_subset (c : Ret 12494) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12494

/-! A first-layer variance payment from dimension 12494. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12494
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

theorem row_node_geometry {wr : WRet 12494} (hw : windowW wr)
    (θ : AHid 12494) {g : ℕ} (hg : g < Js 12494) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12494 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12494 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12494 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12494 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12494 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12494 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12494)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12494} (hw : windowW wr) :
    (gaussMat (mA 12494) 12494 (2 / (12494 : ℝ))).real {X | ∃ g < Js 12494,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12494 : ℝ)) ∨
      42 / (10 * (12494 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12494

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12495) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12495) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12495} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115266953427 / 1000000) : ℝ) * ((1003 / 1000) * ((820381 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5925453 / 1000000000)) ^ 2 * ((1003 / 1000) * ((34168861 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((33950993 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5164008177 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5925453 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((263471979 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((33950993 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1585695123 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5925453 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((647227839 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12495) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12495} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12495} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12495 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34168861 / 1000000000000000)) /
        (2 * (1 - eta) * ((5925453 / 1000000000)) ^ 2) +
        12495 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5925453 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12495} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12495) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12495 - 1))).real
      {v | sgA (paperDesignP 12495) c a v < rowSigma} ∂BstLean.Part161.muI 12495 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12495 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12495 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12495 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12495

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12495) : Prop :=
  ∫ a, (stdGauss (Fin (12495 - 1))).real
    {v | sgA (paperDesignP 12495) c a v < rowSigma} ∂muI 12495 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12495) : SplitData 12495 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12495}
    (hw : WINDOW (paperDesignP 12495) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12495)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12495).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12495} (t : ℝ)
    (hw : WINDOW (paperDesignP 12495) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12495)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12495) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12495) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12495} (hw : WINDOW (paperDesignP 12495) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12495) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12495) c (hqSplit c) ⊆ bulkIx (paperDesignP 12495) c :=
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
noncomputable def hqRootInputs {c : Ret 12495} (t : ℝ)
    (hw : WINDOW (paperDesignP 12495) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12495))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12495 t c BstLean.Part266.agent12495.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12495] at h ⊢
    linarith

end BstLean.Part266.Row12495

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12495) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12495) c (rowSplit c wl ws),
    ((12495 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12495 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12495) c (rowSplit c wl ws),
    ((12495 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12495 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12495 - 1)))
    (rowSplit c wl ws).good a ∂muI 12495 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12495) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12495 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12495) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12495 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12495) c (rowSplit c wl ws),
    hellG2 12495 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12495 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12495}
    (hw : WINDOW (paperDesignP 12495) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12495}
    (hw : WINDOW (paperDesignP 12495) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12495 t c BstLean.Part266.agent12495.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12495

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12495) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12495)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12495)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12495)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12495)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12495)

theorem paidBaseCertificate (H : Set (Ret 12495)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12495

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12495) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12495)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12495)} (h : TablePayment H) :
    (retDist (paperCentres 12495)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12495))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12495} (t : ℝ)
    (hw : WINDOW (paperDesignP 12495) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12495 t c BstLean.Part266.agent12495.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12495

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12495) (a : Ix 12495) : Fin (Js 12495) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12495) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12495) : Measure (Fin (Js 12495)) :=
  (muI 12495).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12495) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12495) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12495) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12495)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12495) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12495)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12495)
    (M : Matrix (Fin (mA 12495)) (Fin (mA 12495)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12495) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12495) (mA 12495) (tA 12495) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12495) (mA 12495) (tA 12495)).real
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

theorem table_second_layer_bad_subset (c : Ret 12495) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12495

/-! A first-layer variance payment from dimension 12495. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12495
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

theorem row_node_geometry {wr : WRet 12495} (hw : windowW wr)
    (θ : AHid 12495) {g : ℕ} (hg : g < Js 12495) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12495 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12495 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12495 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12495 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12495 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12495 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12495)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12495} (hw : windowW wr) :
    (gaussMat (mA 12495) 12495 (2 / (12495 : ℝ))).real {X | ∃ g < Js 12495,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12495 : ℝ)) ∨
      42 / (10 * (12495 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12495

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12496) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12496) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12496} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115276066741 / 1000000) : ℝ) * ((1003 / 1000) * ((102523 / 31250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((185163 / 31250000)) ^ 2 * ((1003 / 1000) * ((34163391 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339523351 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5163388161 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((185163 / 31250000)) * ((1001 / 1000 + 52 / 1000) * ((526901773 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339523351 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3171009433 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((185163 / 31250000)) * ((1001 / 1000 + 52 / 1000) * ((647176017 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12496) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12496} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12496} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12496 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34163391 / 1000000000000000)) /
        (2 * (1 - eta) * ((185163 / 31250000)) ^ 2) +
        12496 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((185163 / 31250000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12496} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12496) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12496 - 1))).real
      {v | sgA (paperDesignP 12496) c a v < rowSigma} ∂BstLean.Part161.muI 12496 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12496 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12496 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12496 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12496

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12496) : Prop :=
  ∫ a, (stdGauss (Fin (12496 - 1))).real
    {v | sgA (paperDesignP 12496) c a v < rowSigma} ∂muI 12496 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12496) : SplitData 12496 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12496}
    (hw : WINDOW (paperDesignP 12496) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12496)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12496).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12496} (t : ℝ)
    (hw : WINDOW (paperDesignP 12496) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12496)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12496) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12496) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12496} (hw : WINDOW (paperDesignP 12496) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12496) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12496) c (hqSplit c) ⊆ bulkIx (paperDesignP 12496) c :=
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
noncomputable def hqRootInputs {c : Ret 12496} (t : ℝ)
    (hw : WINDOW (paperDesignP 12496) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12496))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12496 t c BstLean.Part266.agent12496.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12496] at h ⊢
    linarith

end BstLean.Part266.Row12496

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12496) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12496) c (rowSplit c wl ws),
    ((12496 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12496 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12496) c (rowSplit c wl ws),
    ((12496 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12496 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12496 - 1)))
    (rowSplit c wl ws).good a ∂muI 12496 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12496) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12496 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12496) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12496 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12496) c (rowSplit c wl ws),
    hellG2 12496 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12496 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12496}
    (hw : WINDOW (paperDesignP 12496) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12496}
    (hw : WINDOW (paperDesignP 12496) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12496 t c BstLean.Part266.agent12496.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12496

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12496) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12496)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12496)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12496)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12496)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12496)

theorem paidBaseCertificate (H : Set (Ret 12496)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12496

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12496) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12496)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12496)} (h : TablePayment H) :
    (retDist (paperCentres 12496)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12496))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12496} (t : ℝ)
    (hw : WINDOW (paperDesignP 12496) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12496 t c BstLean.Part266.agent12496.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12496

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12496) (a : Ix 12496) : Fin (Js 12496) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12496) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12496) : Measure (Fin (Js 12496)) :=
  (muI 12496).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12496) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12496) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12496) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12496)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12496) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12496)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12496)
    (M : Matrix (Fin (mA 12496)) (Fin (mA 12496)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12496) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12496) (mA 12496) (tA 12496) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12496) (mA 12496) (tA 12496)).real
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

theorem table_second_layer_bad_subset (c : Ret 12496) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12496

/-! A first-layer variance payment from dimension 12496. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12496
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

theorem row_node_geometry {wr : WRet 12496} (hw : windowW wr)
    (θ : AHid 12496) {g : ℕ} (hg : g < Js 12496) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12496 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12496 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12496 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12496 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12496 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12496 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12496)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12496} (hw : windowW wr) :
    (gaussMat (mA 12496) 12496 (2 / (12496 : ℝ))).real {X | ∃ g < Js 12496,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12496 : ℝ)) ∨
      42 / (10 * (12496 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12496

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12497) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12497) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12497} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115285181169 / 1000000) : ℝ) * ((1003 / 1000) * ((819987 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5924979 / 1000000000)) ^ 2 * ((1003 / 1000) * ((8539481 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339536773 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5162768269 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5924979 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((131714899 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339536773 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((396328587 / 62500000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5924979 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((161781051 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12497) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12497} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12497} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12497 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((8539481 / 250000000000000)) /
        (2 * (1 - eta) * ((5924979 / 1000000000)) ^ 2) +
        12497 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5924979 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12497} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12497) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12497 - 1))).real
      {v | sgA (paperDesignP 12497) c a v < rowSigma} ∂BstLean.Part161.muI 12497 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12497 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12497 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12497 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12497

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12497) : Prop :=
  ∫ a, (stdGauss (Fin (12497 - 1))).real
    {v | sgA (paperDesignP 12497) c a v < rowSigma} ∂muI 12497 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12497) : SplitData 12497 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12497}
    (hw : WINDOW (paperDesignP 12497) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12497)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12497).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12497} (t : ℝ)
    (hw : WINDOW (paperDesignP 12497) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12497)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12497) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12497) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12497} (hw : WINDOW (paperDesignP 12497) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12497) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12497) c (hqSplit c) ⊆ bulkIx (paperDesignP 12497) c :=
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
noncomputable def hqRootInputs {c : Ret 12497} (t : ℝ)
    (hw : WINDOW (paperDesignP 12497) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12497))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12497 t c BstLean.Part266.agent12497.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12497] at h ⊢
    linarith

end BstLean.Part266.Row12497

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12497) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12497) c (rowSplit c wl ws),
    ((12497 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12497 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12497) c (rowSplit c wl ws),
    ((12497 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12497 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12497 - 1)))
    (rowSplit c wl ws).good a ∂muI 12497 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12497) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12497 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12497) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12497 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12497) c (rowSplit c wl ws),
    hellG2 12497 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12497 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12497}
    (hw : WINDOW (paperDesignP 12497) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12497}
    (hw : WINDOW (paperDesignP 12497) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12497 t c BstLean.Part266.agent12497.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12497

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12497) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12497)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12497)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12497)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12497)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12497)

theorem paidBaseCertificate (H : Set (Ret 12497)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12497

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12497) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12497)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12497)} (h : TablePayment H) :
    (retDist (paperCentres 12497)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12497))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12497} (t : ℝ)
    (hw : WINDOW (paperDesignP 12497) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12497 t c BstLean.Part266.agent12497.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12497

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12497) (a : Ix 12497) : Fin (Js 12497) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12497) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12497) : Measure (Fin (Js 12497)) :=
  (muI 12497).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12497) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12497) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12497) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12497)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12497) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12497)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12497)
    (M : Matrix (Fin (mA 12497)) (Fin (mA 12497)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12497) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12497) (mA 12497) (tA 12497) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12497) (mA 12497) (tA 12497)).real
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

theorem table_second_layer_bad_subset (c : Ret 12497) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12497

/-! A first-layer variance payment from dimension 12497. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12497
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

theorem row_node_geometry {wr : WRet 12497} (hw : windowW wr)
    (θ : AHid 12497) {g : ℕ} (hg : g < Js 12497) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12497 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12497 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12497 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12497 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12497 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12497 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12497)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12497} (hw : windowW wr) :
    (gaussMat (mA 12497) 12497 (2 / (12497 : ℝ))).real {X | ∃ g < Js 12497,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12497 : ℝ)) ∨
      42 / (10 * (12497 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12497

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12498) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12498) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12498} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((115294296711 / 1000000) : ℝ) * ((1003 / 1000) * ((3279161 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2962371 / 500000000)) ^ 2 * ((1003 / 1000) * ((34152457 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((84887549 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2581074251 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2962371 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((21072697 / 40000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((84887549 / 250000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((634049607 / 100000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2962371 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((647072399 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12498) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12498} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12498} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12498 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((34152457 / 1000000000000000)) /
        (2 * (1 - eta) * ((2962371 / 500000000)) ^ 2) +
        12498 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2962371 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12498} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12498) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12498 - 1))).real
      {v | sgA (paperDesignP 12498) c a v < rowSigma} ∂BstLean.Part161.muI 12498 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12498 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12498 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12498 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12498

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12498) : Prop :=
  ∫ a, (stdGauss (Fin (12498 - 1))).real
    {v | sgA (paperDesignP 12498) c a v < rowSigma} ∂muI 12498 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12498) : SplitData 12498 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12498}
    (hw : WINDOW (paperDesignP 12498) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12498)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12498).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12498} (t : ℝ)
    (hw : WINDOW (paperDesignP 12498) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12498)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12498) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12498) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12498} (hw : WINDOW (paperDesignP 12498) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12498) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12498) c (hqSplit c) ⊆ bulkIx (paperDesignP 12498) c :=
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
noncomputable def hqRootInputs {c : Ret 12498} (t : ℝ)
    (hw : WINDOW (paperDesignP 12498) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12498))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12498 t c BstLean.Part266.agent12498.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12498] at h ⊢
    linarith

end BstLean.Part266.Row12498

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12498) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12498) c (rowSplit c wl ws),
    ((12498 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12498 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12498) c (rowSplit c wl ws),
    ((12498 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12498 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12498 - 1)))
    (rowSplit c wl ws).good a ∂muI 12498 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12498) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12498 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12498) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12498 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12498) c (rowSplit c wl ws),
    hellG2 12498 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12498 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12498}
    (hw : WINDOW (paperDesignP 12498) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12498}
    (hw : WINDOW (paperDesignP 12498) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12498 t c BstLean.Part266.agent12498.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12498

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12498) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12498)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12498)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12498)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12498)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12498)

theorem paidBaseCertificate (H : Set (Ret 12498)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12498

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12498) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12498)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12498)} (h : TablePayment H) :
    (retDist (paperCentres 12498)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12498))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12498} (t : ℝ)
    (hw : WINDOW (paperDesignP 12498) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12498 t c BstLean.Part266.agent12498.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12498

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12498) (a : Ix 12498) : Fin (Js 12498) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12498) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12498) : Measure (Fin (Js 12498)) :=
  (muI 12498).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12498) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12498) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12498) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12498)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12498) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12498)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12498)
    (M : Matrix (Fin (mA 12498)) (Fin (mA 12498)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12498) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12498) (mA 12498) (tA 12498) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12498) (mA 12498) (tA 12498)).real
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

theorem table_second_layer_bad_subset (c : Ret 12498) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12498

/-! A first-layer variance payment from dimension 12498. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12498
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

theorem row_node_geometry {wr : WRet 12498} (hw : windowW wr)
    (θ : AHid 12498) {g : ℕ} (hg : g < Js 12498) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12498 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12498 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12498 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12498 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12498 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12498 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12498)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12498} (hw : windowW wr) :
    (gaussMat (mA 12498) 12498 (2 / (12498 : ℝ))).real {X | ∃ g < Js 12498,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12498 : ℝ)) ∨
      42 / (10 * (12498 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12498

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12499) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12499) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12499} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((23060682673 / 200000) : ℝ) * ((1003 / 1000) * ((1639187 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1184901 / 200000000)) ^ 2 * ((1003 / 1000) * ((2134187 / 62500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339563621 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2580764429 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1184901 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((526775261 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((339563621 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6339734901 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1184901 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((323510301 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12499) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12499} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12499} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12499 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((2134187 / 62500000000000)) /
        (2 * (1 - eta) * ((1184901 / 200000000)) ^ 2) +
        12499 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1184901 / 200000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12499} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12499) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12499 - 1))).real
      {v | sgA (paperDesignP 12499) c a v < rowSigma} ∂BstLean.Part161.muI 12499 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12499 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12499 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12499 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12499

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12499) : Prop :=
  ∫ a, (stdGauss (Fin (12499 - 1))).real
    {v | sgA (paperDesignP 12499) c a v < rowSigma} ∂muI 12499 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12499) : SplitData 12499 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12499}
    (hw : WINDOW (paperDesignP 12499) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12499)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12499).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12499} (t : ℝ)
    (hw : WINDOW (paperDesignP 12499) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12499)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12499) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12499) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12499} (hw : WINDOW (paperDesignP 12499) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12499) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12499) c (hqSplit c) ⊆ bulkIx (paperDesignP 12499) c :=
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
noncomputable def hqRootInputs {c : Ret 12499} (t : ℝ)
    (hw : WINDOW (paperDesignP 12499) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12499))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12499 t c BstLean.Part266.agent12499.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12499] at h ⊢
    linarith

end BstLean.Part266.Row12499

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12499) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12499) c (rowSplit c wl ws),
    ((12499 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12499 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12499) c (rowSplit c wl ws),
    ((12499 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12499 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12499 - 1)))
    (rowSplit c wl ws).good a ∂muI 12499 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12499) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12499 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12499) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12499 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12499) c (rowSplit c wl ws),
    hellG2 12499 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12499 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12499}
    (hw : WINDOW (paperDesignP 12499) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12499}
    (hw : WINDOW (paperDesignP 12499) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12499 t c BstLean.Part266.agent12499.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12499

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12499) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12499)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12499)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12499)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12499)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12499)

theorem paidBaseCertificate (H : Set (Ret 12499)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12499

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12499) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12499)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12499)} (h : TablePayment H) :
    (retDist (paperCentres 12499)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12499))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12499} (t : ℝ)
    (hw : WINDOW (paperDesignP 12499) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12499 t c BstLean.Part266.agent12499.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12499

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12499) (a : Ix 12499) : Fin (Js 12499) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12499) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12499) : Measure (Fin (Js 12499)) :=
  (muI 12499).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12499) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12499) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12499) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12499)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12499) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12499)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12499)
    (M : Matrix (Fin (mA 12499)) (Fin (mA 12499)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12499) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12499) (mA 12499) (tA 12499) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12499) (mA 12499) (tA 12499)).real
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

theorem table_second_layer_bad_subset (c : Ret 12499) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12499

/-! A first-layer variance payment from dimension 12499. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12499
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

theorem row_node_geometry {wr : WRet 12499} (hw : windowW wr)
    (θ : AHid 12499) {g : ℕ} (hg : g < Js 12499) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12499 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12499 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12499 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12499 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12499 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12499 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12499)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12499} (hw : windowW wr) :
    (gaussMat (mA 12499) 12499 (2 / (12499 : ℝ))).real {X | ∃ g < Js 12499,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12499 : ℝ)) ∨
      42 / (10 * (12499 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12499
