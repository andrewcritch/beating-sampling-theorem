import BstLean.Part266Shard10Step3


/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12600) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12600) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12600} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((58112128019 / 500000) : ℝ) * ((1003 / 1000) * ((3200161 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((737589 / 125000000)) ^ 2 * ((1003 / 1000) * ((6720337 / 200000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((68183369 / 200000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2549788713 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((737589 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((522551189 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((68183369 / 200000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6263633961 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((737589 / 125000000)) * ((1001 / 1000 + 52 / 1000) * ((641831489 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12600) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12600} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12600} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12600 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((6720337 / 200000000000000)) /
        (2 * (1 - eta) * ((737589 / 125000000)) ^ 2) +
        12600 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((737589 / 125000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12600} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12600) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12600 - 1))).real
      {v | sgA (paperDesignP 12600) c a v < rowSigma} ∂BstLean.Part161.muI 12600 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12600 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12600 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12600 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12600

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12600) : Prop :=
  ∫ a, (stdGauss (Fin (12600 - 1))).real
    {v | sgA (paperDesignP 12600) c a v < rowSigma} ∂muI 12600 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12600) : SplitData 12600 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12600}
    (hw : WINDOW (paperDesignP 12600) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12600)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12600).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12600} (t : ℝ)
    (hw : WINDOW (paperDesignP 12600) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12600)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12600) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12600) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12600} (hw : WINDOW (paperDesignP 12600) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12600) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12600) c (hqSplit c) ⊆ bulkIx (paperDesignP 12600) c :=
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
noncomputable def hqRootInputs {c : Ret 12600} (t : ℝ)
    (hw : WINDOW (paperDesignP 12600) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12600))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12600 t c BstLean.Part266.agent12600.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12600] at h ⊢
    linarith

end BstLean.Part266.Row12600

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12600) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12600) c (rowSplit c wl ws),
    ((12600 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12600 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12600) c (rowSplit c wl ws),
    ((12600 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12600 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12600 - 1)))
    (rowSplit c wl ws).good a ∂muI 12600 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12600) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12600 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12600) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12600 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12600) c (rowSplit c wl ws),
    hellG2 12600 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12600 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12600}
    (hw : WINDOW (paperDesignP 12600) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12600}
    (hw : WINDOW (paperDesignP 12600) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12600 t c BstLean.Part266.agent12600.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12600

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12600) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12600)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12600)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12600)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12600)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12600)

theorem paidBaseCertificate (H : Set (Ret 12600)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12600

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12600) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12600)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12600)} (h : TablePayment H) :
    (retDist (paperCentres 12600)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12600))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12600} (t : ℝ)
    (hw : WINDOW (paperDesignP 12600) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12600 t c BstLean.Part266.agent12600.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12600

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12600
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12600) (a : Ix 12600) : Fin (Js 12600) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12600) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12600) : Measure (Fin (Js 12600)) :=
  (muI 12600).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12600) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12600) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12600) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12600)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12600) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12600)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12600)
    (M : Matrix (Fin (mA 12600)) (Fin (mA 12600)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12600) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12600) (mA 12600) (tA 12600) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12600) (mA 12600) (tA 12600)).real
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

theorem table_second_layer_bad_subset (c : Ret 12600) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12600

/-! A first-layer variance payment from dimension 12600. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12600
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

theorem row_node_geometry {wr : WRet 12600} (hw : windowW wr)
    (θ : AHid 12600) {g : ℕ} (hg : g < Js 12600) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12600 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12600 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12600 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12600 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12600 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12600 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12600)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12600} (hw : windowW wr) :
    (gaussMat (mA 12600) 12600 (2 / (12600 : ℝ))).real {X | ∃ g < Js 12600,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12600 : ℝ)) ∨
      42 / (10 * (12600 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12600

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12601) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12601) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12601} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((929866941 / 8000) : ℝ) * ((1003 / 1000) * ((3199399 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2950239 / 500000000)) ^ 2 * ((1003 / 1000) * ((524943 / 15625000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((340930209 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5098970249 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2950239 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((104501941 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((340930209 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1565722027 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2950239 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((641780527 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12601) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12601} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12601} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12601 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((524943 / 15625000000000)) /
        (2 * (1 - eta) * ((2950239 / 500000000)) ^ 2) +
        12601 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2950239 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12601} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12601) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12601 - 1))).real
      {v | sgA (paperDesignP 12601) c a v < rowSigma} ∂BstLean.Part161.muI 12601 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12601 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12601 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12601 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12601

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12601) : Prop :=
  ∫ a, (stdGauss (Fin (12601 - 1))).real
    {v | sgA (paperDesignP 12601) c a v < rowSigma} ∂muI 12601 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12601) : SplitData 12601 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12601}
    (hw : WINDOW (paperDesignP 12601) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12601)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12601).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12601} (t : ℝ)
    (hw : WINDOW (paperDesignP 12601) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12601)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12601) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12601) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12601} (hw : WINDOW (paperDesignP 12601) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12601) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12601) c (hqSplit c) ⊆ bulkIx (paperDesignP 12601) c :=
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
noncomputable def hqRootInputs {c : Ret 12601} (t : ℝ)
    (hw : WINDOW (paperDesignP 12601) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12601))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12601 t c BstLean.Part266.agent12601.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12601] at h ⊢
    linarith

end BstLean.Part266.Row12601

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12601) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12601) c (rowSplit c wl ws),
    ((12601 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12601 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12601) c (rowSplit c wl ws),
    ((12601 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12601 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12601 - 1)))
    (rowSplit c wl ws).good a ∂muI 12601 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12601) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12601 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12601) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12601 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12601) c (rowSplit c wl ws),
    hellG2 12601 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12601 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12601}
    (hw : WINDOW (paperDesignP 12601) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12601}
    (hw : WINDOW (paperDesignP 12601) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12601 t c BstLean.Part266.agent12601.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12601

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12601) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12601)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12601)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12601)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12601)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12601)

theorem paidBaseCertificate (H : Set (Ret 12601)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12601

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12601) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12601)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12601)} (h : TablePayment H) :
    (retDist (paperCentres 12601)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12601))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12601} (t : ℝ)
    (hw : WINDOW (paperDesignP 12601) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12601 t c BstLean.Part266.agent12601.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12601

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12601
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12601) (a : Ix 12601) : Fin (Js 12601) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12601) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12601) : Measure (Fin (Js 12601)) :=
  (muI 12601).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12601) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12601) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12601) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12601)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12601) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12601)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12601)
    (M : Matrix (Fin (mA 12601)) (Fin (mA 12601)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12601) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12601) (mA 12601) (tA 12601) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12601) (mA 12601) (tA 12601)).real
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

theorem table_second_layer_bad_subset (c : Ret 12601) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12601

/-! A first-layer variance payment from dimension 12601. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12601
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

theorem row_node_geometry {wr : WRet 12601} (hw : windowW wr)
    (θ : AHid 12601) {g : ℕ} (hg : g < Js 12601) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12601 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12601 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12601 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12601 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12601 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12601 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12601)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12601} (hw : windowW wr) :
    (gaussMat (mA 12601) 12601 (2 / (12601 : ℝ))).real {X | ∃ g < Js 12601,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12601 : ℝ)) ∨
      42 / (10 * (12601 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12601

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12602) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12602) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12602} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((23248496063 / 200000) : ℝ) * ((1003 / 1000) * ((3198637 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1475061 / 250000000)) ^ 2 * ((1003 / 1000) * ((33591019 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((340943573 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((637295399 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1475061 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((522468227 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((340943573 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3131071201 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1475061 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((320864787 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12602) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12602} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12602} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12602 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33591019 / 1000000000000000)) /
        (2 * (1 - eta) * ((1475061 / 250000000)) ^ 2) +
        12602 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1475061 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12602} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12602) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12602 - 1))).real
      {v | sgA (paperDesignP 12602) c a v < rowSigma} ∂BstLean.Part161.muI 12602 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12602 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12602 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12602 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12602

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12602) : Prop :=
  ∫ a, (stdGauss (Fin (12602 - 1))).real
    {v | sgA (paperDesignP 12602) c a v < rowSigma} ∂muI 12602 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12602) : SplitData 12602 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12602}
    (hw : WINDOW (paperDesignP 12602) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12602)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12602).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12602} (t : ℝ)
    (hw : WINDOW (paperDesignP 12602) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12602)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12602) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12602) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12602} (hw : WINDOW (paperDesignP 12602) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12602) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12602) c (hqSplit c) ⊆ bulkIx (paperDesignP 12602) c :=
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
noncomputable def hqRootInputs {c : Ret 12602} (t : ℝ)
    (hw : WINDOW (paperDesignP 12602) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12602))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12602 t c BstLean.Part266.agent12602.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12602] at h ⊢
    linarith

end BstLean.Part266.Row12602

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12602) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12602) c (rowSplit c wl ws),
    ((12602 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12602 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12602) c (rowSplit c wl ws),
    ((12602 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12602 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12602 - 1)))
    (rowSplit c wl ws).good a ∂muI 12602 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12602) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12602 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12602) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12602 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12602) c (rowSplit c wl ws),
    hellG2 12602 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12602 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12602}
    (hw : WINDOW (paperDesignP 12602) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12602}
    (hw : WINDOW (paperDesignP 12602) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12602 t c BstLean.Part266.agent12602.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12602

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12602) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12602)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12602)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12602)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12602)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12602)

theorem paidBaseCertificate (H : Set (Ret 12602)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12602

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12602) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12602)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12602)} (h : TablePayment H) :
    (retDist (paperCentres 12602)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12602))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12602} (t : ℝ)
    (hw : WINDOW (paperDesignP 12602) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12602 t c BstLean.Part266.agent12602.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12602

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12602
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12602) (a : Ix 12602) : Fin (Js 12602) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12602) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12602) : Measure (Fin (Js 12602)) :=
  (muI 12602).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12602) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12602) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12602) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12602)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12602) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12602)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12602)
    (M : Matrix (Fin (mA 12602)) (Fin (mA 12602)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12602) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12602) (mA 12602) (tA 12602) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12602) (mA 12602) (tA 12602)).real
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

theorem table_second_layer_bad_subset (c : Ret 12602) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12602

/-! A first-layer variance payment from dimension 12602. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12602
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

theorem row_node_geometry {wr : WRet 12602} (hw : windowW wr)
    (θ : AHid 12602) {g : ℕ} (hg : g < Js 12602) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12602 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12602 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12602 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12602 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12602 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12602 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12602)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12602} (hw : windowW wr) :
    (gaussMat (mA 12602) 12602 (2 / (12602 : ℝ))).real {X | ∃ g < Js 12602,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12602 : ℝ)) ∨
      42 / (10 * (12602 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12602

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12603) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12603) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12603} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((29062898527 / 250000) : ℝ) * ((1003 / 1000) * ((799469 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((590001 / 100000000)) ^ 2 * ((1003 / 1000) * ((4198211 / 125000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170478469 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((159304883 / 31250000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((590001 / 100000000)) * ((1001 / 1000 + 52 / 1000) * ((522426757 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170478469 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1252279369 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((590001 / 100000000)) * ((1001 / 1000 + 52 / 1000) * ((641678629 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12603) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12603} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12603} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12603 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((4198211 / 125000000000000)) /
        (2 * (1 - eta) * ((590001 / 100000000)) ^ 2) +
        12603 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((590001 / 100000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12603} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12603) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12603 - 1))).real
      {v | sgA (paperDesignP 12603) c a v < rowSigma} ∂BstLean.Part161.muI 12603 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12603 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12603 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12603 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12603

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12603) : Prop :=
  ∫ a, (stdGauss (Fin (12603 - 1))).real
    {v | sgA (paperDesignP 12603) c a v < rowSigma} ∂muI 12603 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12603) : SplitData 12603 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12603}
    (hw : WINDOW (paperDesignP 12603) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12603)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12603).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12603} (t : ℝ)
    (hw : WINDOW (paperDesignP 12603) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12603)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12603) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12603) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12603} (hw : WINDOW (paperDesignP 12603) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12603) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12603) c (hqSplit c) ⊆ bulkIx (paperDesignP 12603) c :=
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
noncomputable def hqRootInputs {c : Ret 12603} (t : ℝ)
    (hw : WINDOW (paperDesignP 12603) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12603))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12603 t c BstLean.Part266.agent12603.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12603] at h ⊢
    linarith

end BstLean.Part266.Row12603

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12603) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12603) c (rowSplit c wl ws),
    ((12603 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12603 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12603) c (rowSplit c wl ws),
    ((12603 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12603 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12603 - 1)))
    (rowSplit c wl ws).good a ∂muI 12603 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12603) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12603 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12603) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12603 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12603) c (rowSplit c wl ws),
    hellG2 12603 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12603 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12603}
    (hw : WINDOW (paperDesignP 12603) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12603}
    (hw : WINDOW (paperDesignP 12603) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12603 t c BstLean.Part266.agent12603.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12603

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12603) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12603)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12603)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12603)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12603)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12603)

theorem paidBaseCertificate (H : Set (Ret 12603)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12603

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12603) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12603)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12603)} (h : TablePayment H) :
    (retDist (paperCentres 12603)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12603))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12603} (t : ℝ)
    (hw : WINDOW (paperDesignP 12603) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12603 t c BstLean.Part266.agent12603.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12603

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12603
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12603) (a : Ix 12603) : Fin (Js 12603) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12603) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12603) : Measure (Fin (Js 12603)) :=
  (muI 12603).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12603) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12603) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12603) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12603)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12603) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12603)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12603)
    (M : Matrix (Fin (mA 12603)) (Fin (mA 12603)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12603) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12603) (mA 12603) (tA 12603) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12603) (mA 12603) (tA 12603)).real
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

theorem table_second_layer_bad_subset (c : Ret 12603) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12603

/-! A first-layer variance payment from dimension 12603. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12603
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

theorem row_node_geometry {wr : WRet 12603} (hw : windowW wr)
    (θ : AHid 12603) {g : ℕ} (hg : g < Js 12603) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12603 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12603 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12603 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12603 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12603 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12603 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12603)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12603} (hw : windowW wr) :
    (gaussMat (mA 12603) 12603 (2 / (12603 : ℝ))).real {X | ∃ g < Js 12603,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12603 : ℝ)) ∨
      42 / (10 * (12603 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12603

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12604) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12604) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12604} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((23252141801 / 200000) : ℝ) * ((1003 / 1000) * ((639423 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((11523 / 1953125)) ^ 2 * ((1003 / 1000) * ((33580359 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((5327661 / 15625) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5097149441 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((11523 / 1953125)) * ((1001 / 1000 + 52 / 1000) * ((522385293 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((5327661 / 15625) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1252130287 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((11523 / 1953125)) * ((1001 / 1000 + 52 / 1000) * ((160406923 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12604) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12604} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12604} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12604 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33580359 / 1000000000000000)) /
        (2 * (1 - eta) * ((11523 / 1953125)) ^ 2) +
        12604 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((11523 / 1953125)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12604} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12604) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12604 - 1))).real
      {v | sgA (paperDesignP 12604) c a v < rowSigma} ∂BstLean.Part161.muI 12604 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12604 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12604 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12604 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12604

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12604) : Prop :=
  ∫ a, (stdGauss (Fin (12604 - 1))).real
    {v | sgA (paperDesignP 12604) c a v < rowSigma} ∂muI 12604 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12604) : SplitData 12604 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12604}
    (hw : WINDOW (paperDesignP 12604) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12604)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12604).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12604} (t : ℝ)
    (hw : WINDOW (paperDesignP 12604) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12604)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12604) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12604) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12604} (hw : WINDOW (paperDesignP 12604) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12604) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12604) c (hqSplit c) ⊆ bulkIx (paperDesignP 12604) c :=
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
noncomputable def hqRootInputs {c : Ret 12604} (t : ℝ)
    (hw : WINDOW (paperDesignP 12604) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12604))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12604 t c BstLean.Part266.agent12604.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12604] at h ⊢
    linarith

end BstLean.Part266.Row12604

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12604) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12604) c (rowSplit c wl ws),
    ((12604 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12604 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12604) c (rowSplit c wl ws),
    ((12604 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12604 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12604 - 1)))
    (rowSplit c wl ws).good a ∂muI 12604 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12604) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12604 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12604) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12604 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12604) c (rowSplit c wl ws),
    hellG2 12604 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12604 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12604}
    (hw : WINDOW (paperDesignP 12604) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12604}
    (hw : WINDOW (paperDesignP 12604) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12604 t c BstLean.Part266.agent12604.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12604

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12604) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12604)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12604)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12604)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12604)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12604)

theorem paidBaseCertificate (H : Set (Ret 12604)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12604

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12604) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12604)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12604)} (h : TablePayment H) :
    (retDist (paperCentres 12604)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12604))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12604} (t : ℝ)
    (hw : WINDOW (paperDesignP 12604) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12604 t c BstLean.Part266.agent12604.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12604

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12604
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12604) (a : Ix 12604) : Fin (Js 12604) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12604) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12604) : Measure (Fin (Js 12604)) :=
  (muI 12604).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12604) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12604) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12604) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12604)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12604) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12604)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12604)
    (M : Matrix (Fin (mA 12604)) (Fin (mA 12604)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12604) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12604) (mA 12604) (tA 12604) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12604) (mA 12604) (tA 12604)).real
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

theorem table_second_layer_bad_subset (c : Ret 12604) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12604

/-! A first-layer variance payment from dimension 12604. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12604
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

theorem row_node_geometry {wr : WRet 12604} (hw : windowW wr)
    (θ : AHid 12604) {g : ℕ} (hg : g < Js 12604) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12604 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12604 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12604 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12604 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12604 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12604 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12604)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12604} (hw : windowW wr) :
    (gaussMat (mA 12604) 12604 (2 / (12604 : ℝ))).real {X | ∃ g < Js 12604,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12604 : ℝ)) ∨
      42 / (10 * (12604 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12604

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12605) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12605) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12605} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((58134912503 / 500000) : ℝ) * ((1003 / 1000) * ((1598177 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2949771 / 500000000)) ^ 2 * ((1003 / 1000) * ((3357503 / 100000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42622959 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1019308549 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949771 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((104468767 / 200000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42622959 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3129953087 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949771 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((641576763 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12605) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12605} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12605} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12605 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((3357503 / 100000000000000)) /
        (2 * (1 - eta) * ((2949771 / 500000000)) ^ 2) +
        12605 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2949771 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12605} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12605) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12605 - 1))).real
      {v | sgA (paperDesignP 12605) c a v < rowSigma} ∂BstLean.Part161.muI 12605 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12605 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12605 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12605 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12605

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12605) : Prop :=
  ∫ a, (stdGauss (Fin (12605 - 1))).real
    {v | sgA (paperDesignP 12605) c a v < rowSigma} ∂muI 12605 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12605) : SplitData 12605 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12605}
    (hw : WINDOW (paperDesignP 12605) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12605)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12605).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12605} (t : ℝ)
    (hw : WINDOW (paperDesignP 12605) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12605)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12605) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12605) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12605} (hw : WINDOW (paperDesignP 12605) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12605) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12605) c (hqSplit c) ⊆ bulkIx (paperDesignP 12605) c :=
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
noncomputable def hqRootInputs {c : Ret 12605} (t : ℝ)
    (hw : WINDOW (paperDesignP 12605) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12605))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12605 t c BstLean.Part266.agent12605.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12605] at h ⊢
    linarith

end BstLean.Part266.Row12605

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12605) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12605) c (rowSplit c wl ws),
    ((12605 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12605 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12605) c (rowSplit c wl ws),
    ((12605 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12605 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12605 - 1)))
    (rowSplit c wl ws).good a ∂muI 12605 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12605) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12605 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12605) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12605 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12605) c (rowSplit c wl ws),
    hellG2 12605 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12605 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12605}
    (hw : WINDOW (paperDesignP 12605) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12605}
    (hw : WINDOW (paperDesignP 12605) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12605 t c BstLean.Part266.agent12605.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12605

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12605) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12605)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12605)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12605)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12605)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12605)

theorem paidBaseCertificate (H : Set (Ret 12605)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12605

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12605) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12605)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12605)} (h : TablePayment H) :
    (retDist (paperCentres 12605)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12605))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12605} (t : ℝ)
    (hw : WINDOW (paperDesignP 12605) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12605 t c BstLean.Part266.agent12605.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12605

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12605
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12605) (a : Ix 12605) : Fin (Js 12605) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12605) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12605) : Measure (Fin (Js 12605)) :=
  (muI 12605).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12605) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12605) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12605) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12605)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12605) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12605)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12605)
    (M : Matrix (Fin (mA 12605)) (Fin (mA 12605)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12605) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12605) (mA 12605) (tA 12605) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12605) (mA 12605) (tA 12605)).real
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

theorem table_second_layer_bad_subset (c : Ret 12605) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12605

/-! A first-layer variance payment from dimension 12605. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12605
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

theorem row_node_geometry {wr : WRet 12605} (hw : windowW wr)
    (θ : AHid 12605) {g : ℕ} (hg : g < Js 12605) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12605 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12605 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12605 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12605 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12605 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12605 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12605)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12605} (hw : windowW wr) :
    (gaussMat (mA 12605) 12605 (2 / (12605 : ℝ))).real {X | ∃ g < Js 12605,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12605 : ℝ)) ∨
      42 / (10 * (12605 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12605

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12606) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12606) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12606} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((11627894211 / 100000) : ℝ) * ((1003 / 1000) * ((3195593 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1474827 / 250000000)) ^ 2 * ((1003 / 1000) * ((33569703 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((340997041 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((509593617 / 100000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1474827 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((32643899 / 62500000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((340997041 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((312958053 / 50000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1474827 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((320762921 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12606) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12606} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12606} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12606 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33569703 / 1000000000000000)) /
        (2 * (1 - eta) * ((1474827 / 250000000)) ^ 2) +
        12606 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1474827 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12606} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12606) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12606 - 1))).real
      {v | sgA (paperDesignP 12606) c a v < rowSigma} ∂BstLean.Part161.muI 12606 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12606 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12606 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12606 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12606

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12606) : Prop :=
  ∫ a, (stdGauss (Fin (12606 - 1))).real
    {v | sgA (paperDesignP 12606) c a v < rowSigma} ∂muI 12606 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12606) : SplitData 12606 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12606}
    (hw : WINDOW (paperDesignP 12606) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12606)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12606).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12606} (t : ℝ)
    (hw : WINDOW (paperDesignP 12606) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12606)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12606) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12606) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12606} (hw : WINDOW (paperDesignP 12606) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12606) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12606) c (hqSplit c) ⊆ bulkIx (paperDesignP 12606) c :=
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
noncomputable def hqRootInputs {c : Ret 12606} (t : ℝ)
    (hw : WINDOW (paperDesignP 12606) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12606))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12606 t c BstLean.Part266.agent12606.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12606] at h ⊢
    linarith

end BstLean.Part266.Row12606

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12606) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12606) c (rowSplit c wl ws),
    ((12606 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12606 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12606) c (rowSplit c wl ws),
    ((12606 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12606 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12606 - 1)))
    (rowSplit c wl ws).good a ∂muI 12606 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12606) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12606 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12606) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12606 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12606) c (rowSplit c wl ws),
    hellG2 12606 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12606 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12606}
    (hw : WINDOW (paperDesignP 12606) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12606}
    (hw : WINDOW (paperDesignP 12606) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12606 t c BstLean.Part266.agent12606.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12606

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12606) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12606)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12606)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12606)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12606)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12606)

theorem paidBaseCertificate (H : Set (Ret 12606)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12606

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12606) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12606)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12606)} (h : TablePayment H) :
    (retDist (paperCentres 12606)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12606))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12606} (t : ℝ)
    (hw : WINDOW (paperDesignP 12606) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12606 t c BstLean.Part266.agent12606.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12606

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12606
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12606) (a : Ix 12606) : Fin (Js 12606) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12606) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12606) : Measure (Fin (Js 12606)) :=
  (muI 12606).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12606) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12606) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12606) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12606)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12606) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12606)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12606)
    (M : Matrix (Fin (mA 12606)) (Fin (mA 12606)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12606) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12606) (mA 12606) (tA 12606) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12606) (mA 12606) (tA 12606)).real
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

theorem table_second_layer_bad_subset (c : Ret 12606) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12606

/-! A first-layer variance payment from dimension 12606. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12606
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

theorem row_node_geometry {wr : WRet 12606} (hw : windowW wr)
    (θ : AHid 12606) {g : ℕ} (hg : g < Js 12606) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12606 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12606 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12606 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12606 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12606 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12606 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12606)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12606} (hw : windowW wr) :
    (gaussMat (mA 12606) 12606 (2 / (12606 : ℝ))).real {X | ∃ g < Js 12606,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12606 : ℝ)) ∨
      42 / (10 * (12606 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12606

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12607) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12607) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12607} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((116288060319 / 1000000) : ℝ) * ((1003 / 1000) * ((3194833 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2949537 / 500000000)) ^ 2 * ((1003 / 1000) * ((33564377 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34101041 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1273832429 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949537 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((26113047 / 50000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34101041 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3129208047 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949537 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((64147493 / 100000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12607) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12607} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12607} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12607 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33564377 / 1000000000000000)) /
        (2 * (1 - eta) * ((2949537 / 500000000)) ^ 2) +
        12607 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2949537 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12607} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12607) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12607 - 1))).real
      {v | sgA (paperDesignP 12607) c a v < rowSigma} ∂BstLean.Part161.muI 12607 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12607 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12607 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12607 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12607

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12607) : Prop :=
  ∫ a, (stdGauss (Fin (12607 - 1))).real
    {v | sgA (paperDesignP 12607) c a v < rowSigma} ∂muI 12607 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12607) : SplitData 12607 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12607}
    (hw : WINDOW (paperDesignP 12607) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12607)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12607).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12607} (t : ℝ)
    (hw : WINDOW (paperDesignP 12607) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12607)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12607) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12607) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12607} (hw : WINDOW (paperDesignP 12607) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12607) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12607) c (hqSplit c) ⊆ bulkIx (paperDesignP 12607) c :=
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
noncomputable def hqRootInputs {c : Ret 12607} (t : ℝ)
    (hw : WINDOW (paperDesignP 12607) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12607))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12607 t c BstLean.Part266.agent12607.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12607] at h ⊢
    linarith

end BstLean.Part266.Row12607

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12607) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12607) c (rowSplit c wl ws),
    ((12607 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12607 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12607) c (rowSplit c wl ws),
    ((12607 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12607 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12607 - 1)))
    (rowSplit c wl ws).good a ∂muI 12607 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12607) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12607 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12607) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12607 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12607) c (rowSplit c wl ws),
    hellG2 12607 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12607 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12607}
    (hw : WINDOW (paperDesignP 12607) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12607}
    (hw : WINDOW (paperDesignP 12607) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12607 t c BstLean.Part266.agent12607.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12607

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12607) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12607)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12607)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12607)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12607)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12607)

theorem paidBaseCertificate (H : Set (Ret 12607)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12607

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12607) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12607)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12607)} (h : TablePayment H) :
    (retDist (paperCentres 12607)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12607))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12607} (t : ℝ)
    (hw : WINDOW (paperDesignP 12607) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12607 t c BstLean.Part266.agent12607.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12607

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12607
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12607) (a : Ix 12607) : Fin (Js 12607) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12607) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12607) : Measure (Fin (Js 12607)) :=
  (muI 12607).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12607) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12607) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12607) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12607)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12607) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12607)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12607)
    (M : Matrix (Fin (mA 12607)) (Fin (mA 12607)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12607) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12607) (mA 12607) (tA 12607) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12607) (mA 12607) (tA 12607)).real
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

theorem table_second_layer_bad_subset (c : Ret 12607) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12607

/-! A first-layer variance payment from dimension 12607. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12607
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

theorem row_node_geometry {wr : WRet 12607} (hw : windowW wr)
    (θ : AHid 12607) {g : ℕ} (hg : g < Js 12607) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12607 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12607 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12607 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12607 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12607 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12607 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12607)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12607} (hw : windowW wr) :
    (gaussMat (mA 12607) 12607 (2 / (12607 : ℝ))).real {X | ∃ g < Js 12607,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12607 : ℝ)) ∨
      42 / (10 * (12607 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12607

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12608) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12608) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12608} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((116297179633 / 1000000) : ℝ) * ((1003 / 1000) * ((3194073 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((147471 / 25000000)) ^ 2 * ((1003 / 1000) * ((8389763 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341023781 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2547361691 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((147471 / 25000000)) * ((1001 / 1000 + 52 / 1000) * ((261109751 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341023781 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1564417819 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((147471 / 25000000)) * ((1001 / 1000 + 52 / 1000) * ((25656961 / 40000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12608) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12608} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12608} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12608 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((8389763 / 250000000000000)) /
        (2 * (1 - eta) * ((147471 / 25000000)) ^ 2) +
        12608 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((147471 / 25000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12608} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12608) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12608 - 1))).real
      {v | sgA (paperDesignP 12608) c a v < rowSigma} ∂BstLean.Part161.muI 12608 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12608 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12608 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12608 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12608

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12608) : Prop :=
  ∫ a, (stdGauss (Fin (12608 - 1))).real
    {v | sgA (paperDesignP 12608) c a v < rowSigma} ∂muI 12608 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12608) : SplitData 12608 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12608}
    (hw : WINDOW (paperDesignP 12608) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12608)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12608).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12608} (t : ℝ)
    (hw : WINDOW (paperDesignP 12608) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12608)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12608) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12608) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12608} (hw : WINDOW (paperDesignP 12608) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12608) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12608) c (hqSplit c) ⊆ bulkIx (paperDesignP 12608) c :=
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
noncomputable def hqRootInputs {c : Ret 12608} (t : ℝ)
    (hw : WINDOW (paperDesignP 12608) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12608))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12608 t c BstLean.Part266.agent12608.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12608] at h ⊢
    linarith

end BstLean.Part266.Row12608

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12608) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12608) c (rowSplit c wl ws),
    ((12608 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12608 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12608) c (rowSplit c wl ws),
    ((12608 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12608 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12608 - 1)))
    (rowSplit c wl ws).good a ∂muI 12608 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12608) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12608 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12608) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12608 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12608) c (rowSplit c wl ws),
    hellG2 12608 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12608 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12608}
    (hw : WINDOW (paperDesignP 12608) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12608}
    (hw : WINDOW (paperDesignP 12608) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12608 t c BstLean.Part266.agent12608.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12608

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12608) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12608)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12608)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12608)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12608)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12608)

theorem paidBaseCertificate (H : Set (Ret 12608)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12608

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12608) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12608)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12608)} (h : TablePayment H) :
    (retDist (paperCentres 12608)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12608))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12608} (t : ℝ)
    (hw : WINDOW (paperDesignP 12608) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12608 t c BstLean.Part266.agent12608.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12608

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12608
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12608) (a : Ix 12608) : Fin (Js 12608) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12608) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12608) : Measure (Fin (Js 12608)) :=
  (muI 12608).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12608) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12608) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12608) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12608)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12608) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12608)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12608)
    (M : Matrix (Fin (mA 12608)) (Fin (mA 12608)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12608) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12608) (mA 12608) (tA 12608) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12608) (mA 12608) (tA 12608)).real
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

theorem table_second_layer_bad_subset (c : Ret 12608) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12608

/-! A first-layer variance payment from dimension 12608. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12608
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

theorem row_node_geometry {wr : WRet 12608} (hw : windowW wr)
    (θ : AHid 12608) {g : ℕ} (hg : g < Js 12608) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12608 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12608 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12608 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12608 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12608 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12608 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12608)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12608} (hw : windowW wr) :
    (gaussMat (mA 12608) 12608 (2 / (12608 : ℝ))).real {X | ∃ g < Js 12608,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12608 : ℝ)) ∨
      42 / (10 * (12608 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12608

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12609) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12609) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12609} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((2326126001 / 20000) : ℝ) * ((1003 / 1000) * ((3193313 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2949303 / 500000000)) ^ 2 * ((1003 / 1000) * ((33553729 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341037153 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((318382323 / 62500000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949303 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((522178071 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341037153 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1251385321 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949303 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((80171641 / 125000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12609) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12609} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12609} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12609 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33553729 / 1000000000000000)) /
        (2 * (1 - eta) * ((2949303 / 500000000)) ^ 2) +
        12609 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2949303 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12609} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12609) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12609 - 1))).real
      {v | sgA (paperDesignP 12609) c a v < rowSigma} ∂BstLean.Part161.muI 12609 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12609 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12609 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12609 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12609

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12609) : Prop :=
  ∫ a, (stdGauss (Fin (12609 - 1))).real
    {v | sgA (paperDesignP 12609) c a v < rowSigma} ∂muI 12609 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12609) : SplitData 12609 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12609}
    (hw : WINDOW (paperDesignP 12609) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12609)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12609).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12609} (t : ℝ)
    (hw : WINDOW (paperDesignP 12609) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12609)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12609) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12609) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12609} (hw : WINDOW (paperDesignP 12609) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12609) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12609) c (hqSplit c) ⊆ bulkIx (paperDesignP 12609) c :=
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
noncomputable def hqRootInputs {c : Ret 12609} (t : ℝ)
    (hw : WINDOW (paperDesignP 12609) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12609))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12609 t c BstLean.Part266.agent12609.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12609] at h ⊢
    linarith

end BstLean.Part266.Row12609

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12609) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12609) c (rowSplit c wl ws),
    ((12609 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12609 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12609) c (rowSplit c wl ws),
    ((12609 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12609 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12609 - 1)))
    (rowSplit c wl ws).good a ∂muI 12609 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12609) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12609 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12609) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12609 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12609) c (rowSplit c wl ws),
    hellG2 12609 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12609 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12609}
    (hw : WINDOW (paperDesignP 12609) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12609}
    (hw : WINDOW (paperDesignP 12609) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12609 t c BstLean.Part266.agent12609.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12609

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12609) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12609)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12609)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12609)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12609)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12609)

theorem paidBaseCertificate (H : Set (Ret 12609)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12609

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12609) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12609)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12609)} (h : TablePayment H) :
    (retDist (paperCentres 12609)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12609))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12609} (t : ℝ)
    (hw : WINDOW (paperDesignP 12609) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12609 t c BstLean.Part266.agent12609.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12609

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12609
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12609) (a : Ix 12609) : Fin (Js 12609) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12609) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12609) : Measure (Fin (Js 12609)) :=
  (muI 12609).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12609) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12609) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12609) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12609)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12609) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12609)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12609)
    (M : Matrix (Fin (mA 12609)) (Fin (mA 12609)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12609) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12609) (mA 12609) (tA 12609) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12609) (mA 12609) (tA 12609)).real
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

theorem table_second_layer_bad_subset (c : Ret 12609) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12609

/-! A first-layer variance payment from dimension 12609. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12609
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

theorem row_node_geometry {wr : WRet 12609} (hw : windowW wr)
    (θ : AHid 12609) {g : ℕ} (hg : g < Js 12609) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12609 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12609 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12609 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12609 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12609 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12609 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12609)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12609} (hw : windowW wr) :
    (gaussMat (mA 12609) 12609 (2 / (12609 : ℝ))).real {X | ∃ g < Js 12609,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12609 : ℝ)) ∨
      42 / (10 * (12609 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12609

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12610) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12610) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12610} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((29078855393 / 250000) : ℝ) * ((1003 / 1000) * ((3192553 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1474593 / 250000000)) ^ 2 * ((1003 / 1000) * ((16774203 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170525263 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2546755537 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1474593 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((261068323 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170525263 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6256182083 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1474593 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((501033 / 781250000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12610) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12610} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12610} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12610 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((16774203 / 500000000000000)) /
        (2 * (1 - eta) * ((1474593 / 250000000)) ^ 2) +
        12610 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1474593 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12610} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12610) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12610 - 1))).real
      {v | sgA (paperDesignP 12610) c a v < rowSigma} ∂BstLean.Part161.muI 12610 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12610 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12610 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12610 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12610

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12610) : Prop :=
  ∫ a, (stdGauss (Fin (12610 - 1))).real
    {v | sgA (paperDesignP 12610) c a v < rowSigma} ∂muI 12610 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12610) : SplitData 12610 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12610}
    (hw : WINDOW (paperDesignP 12610) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12610)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12610).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12610} (t : ℝ)
    (hw : WINDOW (paperDesignP 12610) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12610)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12610) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12610) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12610} (hw : WINDOW (paperDesignP 12610) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12610) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12610) c (hqSplit c) ⊆ bulkIx (paperDesignP 12610) c :=
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
noncomputable def hqRootInputs {c : Ret 12610} (t : ℝ)
    (hw : WINDOW (paperDesignP 12610) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12610))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12610 t c BstLean.Part266.agent12610.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12610] at h ⊢
    linarith

end BstLean.Part266.Row12610

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12610) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12610) c (rowSplit c wl ws),
    ((12610 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12610 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12610) c (rowSplit c wl ws),
    ((12610 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12610 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12610 - 1)))
    (rowSplit c wl ws).good a ∂muI 12610 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12610) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12610 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12610) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12610 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12610) c (rowSplit c wl ws),
    hellG2 12610 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12610 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12610}
    (hw : WINDOW (paperDesignP 12610) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12610}
    (hw : WINDOW (paperDesignP 12610) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12610 t c BstLean.Part266.agent12610.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12610

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12610) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12610)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12610)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12610)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12610)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12610)

theorem paidBaseCertificate (H : Set (Ret 12610)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12610

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12610) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12610)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12610)} (h : TablePayment H) :
    (retDist (paperCentres 12610)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12610))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12610} (t : ℝ)
    (hw : WINDOW (paperDesignP 12610) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12610 t c BstLean.Part266.agent12610.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12610

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12610
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12610) (a : Ix 12610) : Fin (Js 12610) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12610) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12610) : Measure (Fin (Js 12610)) :=
  (muI 12610).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12610) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12610) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12610) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12610)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12610) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12610)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12610)
    (M : Matrix (Fin (mA 12610)) (Fin (mA 12610)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12610) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12610) (mA 12610) (tA 12610) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12610) (mA 12610) (tA 12610)).real
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

theorem table_second_layer_bad_subset (c : Ret 12610) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12610

/-! A first-layer variance payment from dimension 12610. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12610
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

theorem row_node_geometry {wr : WRet 12610} (hw : windowW wr)
    (θ : AHid 12610) {g : ℕ} (hg : g < Js 12610) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12610 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12610 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12610 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12610 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12610 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12610 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12610)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12610} (hw : windowW wr) :
    (gaussMat (mA 12610) 12610 (2 / (12610 : ℝ))).real {X | ∃ g < Js 12610,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12610 : ℝ)) ∨
      42 / (10 * (12610 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12610

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12611) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12611) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12611} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((116324544199 / 1000000) : ℝ) * ((1003 / 1000) * ((1595897 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2949069 / 500000000)) ^ 2 * ((1003 / 1000) * ((6708617 / 200000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((3410639 / 10000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((50929051 / 10000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949069 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((130523807 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((3410639 / 10000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6255437707 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2949069 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((641271359 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12611) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12611} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12611} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12611 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((6708617 / 200000000000000)) /
        (2 * (1 - eta) * ((2949069 / 500000000)) ^ 2) +
        12611 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2949069 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12611} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12611) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12611 - 1))).real
      {v | sgA (paperDesignP 12611) c a v < rowSigma} ∂BstLean.Part161.muI 12611 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12611 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12611 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12611 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12611

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12611) : Prop :=
  ∫ a, (stdGauss (Fin (12611 - 1))).real
    {v | sgA (paperDesignP 12611) c a v < rowSigma} ∂muI 12611 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12611) : SplitData 12611 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12611}
    (hw : WINDOW (paperDesignP 12611) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12611)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12611).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12611} (t : ℝ)
    (hw : WINDOW (paperDesignP 12611) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12611)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12611) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12611) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12611} (hw : WINDOW (paperDesignP 12611) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12611) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12611) c (hqSplit c) ⊆ bulkIx (paperDesignP 12611) c :=
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
noncomputable def hqRootInputs {c : Ret 12611} (t : ℝ)
    (hw : WINDOW (paperDesignP 12611) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12611))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12611 t c BstLean.Part266.agent12611.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12611] at h ⊢
    linarith

end BstLean.Part266.Row12611

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12611) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12611) c (rowSplit c wl ws),
    ((12611 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12611 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12611) c (rowSplit c wl ws),
    ((12611 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12611 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12611 - 1)))
    (rowSplit c wl ws).good a ∂muI 12611 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12611) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12611 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12611) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12611 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12611) c (rowSplit c wl ws),
    hellG2 12611 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12611 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12611}
    (hw : WINDOW (paperDesignP 12611) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12611}
    (hw : WINDOW (paperDesignP 12611) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12611 t c BstLean.Part266.agent12611.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12611

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12611) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12611)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12611)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12611)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12611)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12611)

theorem paidBaseCertificate (H : Set (Ret 12611)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12611

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12611) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12611)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12611)} (h : TablePayment H) :
    (retDist (paperCentres 12611)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12611))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12611} (t : ℝ)
    (hw : WINDOW (paperDesignP 12611) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12611 t c BstLean.Part266.agent12611.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12611

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12611
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12611) (a : Ix 12611) : Fin (Js 12611) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12611) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12611) : Measure (Fin (Js 12611)) :=
  (muI 12611).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12611) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12611) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12611) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12611)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12611) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12611)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12611)
    (M : Matrix (Fin (mA 12611)) (Fin (mA 12611)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12611) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12611) (mA 12611) (tA 12611) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12611) (mA 12611) (tA 12611)).real
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

theorem table_second_layer_bad_subset (c : Ret 12611) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12611

/-! A first-layer variance payment from dimension 12611. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12611
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

theorem row_node_geometry {wr : WRet 12611} (hw : windowW wr)
    (θ : AHid 12611) {g : ℕ} (hg : g < Js 12611) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12611 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12611 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12611 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12611 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12611 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12611 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12611)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12611} (hw : windowW wr) :
    (gaussMat (mA 12611) 12611 (2 / (12611 : ℝ))).real {X | ∃ g < Js 12611,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12611 : ℝ)) ∨
      42 / (10 * (12611 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12611

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12612) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12612) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12612} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((58166814127 / 500000) : ℝ) * ((1003 / 1000) * ((1595517 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1179581 / 200000000)) ^ 2 * ((1003 / 1000) * ((16768883 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341077217 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5092299247 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1179581 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((522053817 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341077217 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((156367337 / 25000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1179581 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((641220487 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12612) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12612} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12612} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12612 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((16768883 / 500000000000000)) /
        (2 * (1 - eta) * ((1179581 / 200000000)) ^ 2) +
        12612 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1179581 / 200000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12612} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12612) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12612 - 1))).real
      {v | sgA (paperDesignP 12612) c a v < rowSigma} ∂BstLean.Part161.muI 12612 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12612 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12612 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12612 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12612

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12612) : Prop :=
  ∫ a, (stdGauss (Fin (12612 - 1))).real
    {v | sgA (paperDesignP 12612) c a v < rowSigma} ∂muI 12612 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12612) : SplitData 12612 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12612}
    (hw : WINDOW (paperDesignP 12612) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12612)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12612).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12612} (t : ℝ)
    (hw : WINDOW (paperDesignP 12612) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12612)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12612) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12612) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12612} (hw : WINDOW (paperDesignP 12612) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12612) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12612) c (hqSplit c) ⊆ bulkIx (paperDesignP 12612) c :=
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
noncomputable def hqRootInputs {c : Ret 12612} (t : ℝ)
    (hw : WINDOW (paperDesignP 12612) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12612))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12612 t c BstLean.Part266.agent12612.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12612] at h ⊢
    linarith

end BstLean.Part266.Row12612

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12612) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12612) c (rowSplit c wl ws),
    ((12612 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12612 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12612) c (rowSplit c wl ws),
    ((12612 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12612 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12612 - 1)))
    (rowSplit c wl ws).good a ∂muI 12612 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12612) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12612 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12612) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12612 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12612) c (rowSplit c wl ws),
    hellG2 12612 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12612 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12612}
    (hw : WINDOW (paperDesignP 12612) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12612}
    (hw : WINDOW (paperDesignP 12612) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12612 t c BstLean.Part266.agent12612.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12612

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12612) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12612)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12612)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12612)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12612)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12612)

theorem paidBaseCertificate (H : Set (Ret 12612)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12612

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12612) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12612)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12612)} (h : TablePayment H) :
    (retDist (paperCentres 12612)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12612))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12612} (t : ℝ)
    (hw : WINDOW (paperDesignP 12612) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12612 t c BstLean.Part266.agent12612.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12612

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12612
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12612) (a : Ix 12612) : Fin (Js 12612) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12612) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12612) : Measure (Fin (Js 12612)) :=
  (muI 12612).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12612) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12612) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12612) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12612)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12612) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12612)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12612)
    (M : Matrix (Fin (mA 12612)) (Fin (mA 12612)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12612) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12612) (mA 12612) (tA 12612) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12612) (mA 12612) (tA 12612)).real
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

theorem table_second_layer_bad_subset (c : Ret 12612) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12612

/-! A first-layer variance payment from dimension 12612. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12612
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

theorem row_node_geometry {wr : WRet 12612} (hw : windowW wr)
    (θ : AHid 12612) {g : ℕ} (hg : g < Js 12612) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12612 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12612 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12612 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12612 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12612 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12612 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12612)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12612} (hw : windowW wr) :
    (gaussMat (mA 12612) 12612 (2 / (12612 : ℝ))).real {X | ∃ g < Js 12612,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12612 : ℝ)) ∨
      42 / (10 * (12612 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12612

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12613) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12613) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12613} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((58171376543 / 500000) : ℝ) * ((1003 / 1000) * ((127611 / 40000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5897671 / 1000000000)) ^ 2 * ((1003 / 1000) * ((33532447 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341090593 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5091693513 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5897671 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((130503103 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341090593 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((31269747 / 5000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5897671 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((641169623 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12613) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12613} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12613} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12613 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33532447 / 1000000000000000)) /
        (2 * (1 - eta) * ((5897671 / 1000000000)) ^ 2) +
        12613 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5897671 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12613} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12613) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12613 - 1))).real
      {v | sgA (paperDesignP 12613) c a v < rowSigma} ∂BstLean.Part161.muI 12613 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12613 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12613 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12613 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12613

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12613) : Prop :=
  ∫ a, (stdGauss (Fin (12613 - 1))).real
    {v | sgA (paperDesignP 12613) c a v < rowSigma} ∂muI 12613 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12613) : SplitData 12613 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12613}
    (hw : WINDOW (paperDesignP 12613) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12613)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12613).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12613} (t : ℝ)
    (hw : WINDOW (paperDesignP 12613) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12613)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12613) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12613) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12613} (hw : WINDOW (paperDesignP 12613) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12613) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12613) c (hqSplit c) ⊆ bulkIx (paperDesignP 12613) c :=
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
noncomputable def hqRootInputs {c : Ret 12613} (t : ℝ)
    (hw : WINDOW (paperDesignP 12613) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12613))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12613 t c BstLean.Part266.agent12613.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12613] at h ⊢
    linarith

end BstLean.Part266.Row12613

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12613) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12613) c (rowSplit c wl ws),
    ((12613 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12613 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12613) c (rowSplit c wl ws),
    ((12613 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12613 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12613 - 1)))
    (rowSplit c wl ws).good a ∂muI 12613 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12613) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12613 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12613) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12613 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12613) c (rowSplit c wl ws),
    hellG2 12613 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12613 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12613}
    (hw : WINDOW (paperDesignP 12613) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12613}
    (hw : WINDOW (paperDesignP 12613) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12613 t c BstLean.Part266.agent12613.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12613

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12613) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12613)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12613)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12613)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12613)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12613)

theorem paidBaseCertificate (H : Set (Ret 12613)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12613

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12613) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12613)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12613)} (h : TablePayment H) :
    (retDist (paperCentres 12613)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12613))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12613} (t : ℝ)
    (hw : WINDOW (paperDesignP 12613) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12613 t c BstLean.Part266.agent12613.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12613

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12613
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12613) (a : Ix 12613) : Fin (Js 12613) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12613) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12613) : Measure (Fin (Js 12613)) :=
  (muI 12613).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12613) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12613) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12613) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12613)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12613) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12613)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12613)
    (M : Matrix (Fin (mA 12613)) (Fin (mA 12613)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12613) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12613) (mA 12613) (tA 12613) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12613) (mA 12613) (tA 12613)).real
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

theorem table_second_layer_bad_subset (c : Ret 12613) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12613

/-! A first-layer variance payment from dimension 12613. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12613
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

theorem row_node_geometry {wr : WRet 12613} (hw : windowW wr)
    (θ : AHid 12613) {g : ℕ} (hg : g < Js 12613) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12613 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12613 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12613 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12613 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12613 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12613 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12613)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12613} (hw : windowW wr) :
    (gaussMat (mA 12613) 12613 (2 / (12613 : ℝ))).real {X | ∃ g < Js 12613,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12613 : ℝ)) ∨
      42 / (10 * (12613 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12613

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12614) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12614) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12614} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((7271992439 / 62500) : ℝ) * ((1003 / 1000) * ((3189517 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5897437 / 1000000000)) ^ 2 * ((1003 / 1000) * ((3352713 / 100000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34110397 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((50910879 / 10000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5897437 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((521971013 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((34110397 / 100000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6253205467 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5897437 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((641118767 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12614) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12614} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12614} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12614 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((3352713 / 100000000000000)) /
        (2 * (1 - eta) * ((5897437 / 1000000000)) ^ 2) +
        12614 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5897437 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12614} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12614) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12614 - 1))).real
      {v | sgA (paperDesignP 12614) c a v < rowSigma} ∂BstLean.Part161.muI 12614 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12614 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12614 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12614 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12614

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12614) : Prop :=
  ∫ a, (stdGauss (Fin (12614 - 1))).real
    {v | sgA (paperDesignP 12614) c a v < rowSigma} ∂muI 12614 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12614) : SplitData 12614 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12614}
    (hw : WINDOW (paperDesignP 12614) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12614)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12614).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12614} (t : ℝ)
    (hw : WINDOW (paperDesignP 12614) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12614)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12614) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12614) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12614} (hw : WINDOW (paperDesignP 12614) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12614) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12614) c (hqSplit c) ⊆ bulkIx (paperDesignP 12614) c :=
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
noncomputable def hqRootInputs {c : Ret 12614} (t : ℝ)
    (hw : WINDOW (paperDesignP 12614) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12614))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12614 t c BstLean.Part266.agent12614.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12614] at h ⊢
    linarith

end BstLean.Part266.Row12614

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12614) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12614) c (rowSplit c wl ws),
    ((12614 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12614 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12614) c (rowSplit c wl ws),
    ((12614 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12614 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12614 - 1)))
    (rowSplit c wl ws).good a ∂muI 12614 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12614) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12614 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12614) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12614 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12614) c (rowSplit c wl ws),
    hellG2 12614 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12614 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12614}
    (hw : WINDOW (paperDesignP 12614) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12614}
    (hw : WINDOW (paperDesignP 12614) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12614 t c BstLean.Part266.agent12614.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12614

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12614) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12614)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12614)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12614)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12614)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12614)

theorem paidBaseCertificate (H : Set (Ret 12614)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12614

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12614) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12614)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12614)} (h : TablePayment H) :
    (retDist (paperCentres 12614)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12614))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12614} (t : ℝ)
    (hw : WINDOW (paperDesignP 12614) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12614 t c BstLean.Part266.agent12614.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12614

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12614
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12614) (a : Ix 12614) : Fin (Js 12614) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12614) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12614) : Measure (Fin (Js 12614)) :=
  (muI 12614).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12614) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12614) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12614) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12614)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12614) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12614)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12614)
    (M : Matrix (Fin (mA 12614)) (Fin (mA 12614)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12614) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12614) (mA 12614) (tA 12614) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12614) (mA 12614) (tA 12614)).real
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

theorem table_second_layer_bad_subset (c : Ret 12614) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12614

/-! A first-layer variance payment from dimension 12614. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12614
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

theorem row_node_geometry {wr : WRet 12614} (hw : windowW wr)
    (θ : AHid 12614) {g : ℕ} (hg : g < Js 12614) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12614 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12614 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12614 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12614 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12614 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12614 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12614)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12614} (hw : windowW wr) :
    (gaussMat (mA 12614) 12614 (2 / (12614 : ℝ))).real {X | ∃ g < Js 12614,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12614 : ℝ)) ∨
      42 / (10 * (12614 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12614

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12615) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12615) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12615} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((116361006067 / 1000000) : ℝ) * ((1003 / 1000) * ((1594379 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5897203 / 1000000000)) ^ 2 * ((1003 / 1000) * ((16760907 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341117349 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2545241203 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5897203 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((260964811 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341117349 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3126230841 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5897203 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((320533959 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12615) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12615} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12615} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12615 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((16760907 / 500000000000000)) /
        (2 * (1 - eta) * ((5897203 / 1000000000)) ^ 2) +
        12615 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5897203 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12615} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12615) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12615 - 1))).real
      {v | sgA (paperDesignP 12615) c a v < rowSigma} ∂BstLean.Part161.muI 12615 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12615 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12615 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12615 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12615

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12615) : Prop :=
  ∫ a, (stdGauss (Fin (12615 - 1))).real
    {v | sgA (paperDesignP 12615) c a v < rowSigma} ∂muI 12615 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12615) : SplitData 12615 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12615}
    (hw : WINDOW (paperDesignP 12615) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12615)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12615).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12615} (t : ℝ)
    (hw : WINDOW (paperDesignP 12615) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12615)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12615) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12615) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12615} (hw : WINDOW (paperDesignP 12615) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12615) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12615) c (hqSplit c) ⊆ bulkIx (paperDesignP 12615) c :=
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
noncomputable def hqRootInputs {c : Ret 12615} (t : ℝ)
    (hw : WINDOW (paperDesignP 12615) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12615))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12615 t c BstLean.Part266.agent12615.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12615] at h ⊢
    linarith

end BstLean.Part266.Row12615

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12615) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12615) c (rowSplit c wl ws),
    ((12615 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12615 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12615) c (rowSplit c wl ws),
    ((12615 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12615 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12615 - 1)))
    (rowSplit c wl ws).good a ∂muI 12615 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12615) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12615 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12615) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12615 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12615) c (rowSplit c wl ws),
    hellG2 12615 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12615 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12615}
    (hw : WINDOW (paperDesignP 12615) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12615}
    (hw : WINDOW (paperDesignP 12615) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12615 t c BstLean.Part266.agent12615.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12615

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12615) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12615)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12615)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12615)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12615)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12615)

theorem paidBaseCertificate (H : Set (Ret 12615)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12615

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12615) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12615)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12615)} (h : TablePayment H) :
    (retDist (paperCentres 12615)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12615))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12615} (t : ℝ)
    (hw : WINDOW (paperDesignP 12615) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12615 t c BstLean.Part266.agent12615.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12615

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12615
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12615) (a : Ix 12615) : Fin (Js 12615) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12615) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12615) : Measure (Fin (Js 12615)) :=
  (muI 12615).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12615) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12615) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12615) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12615)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12615) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12615)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12615)
    (M : Matrix (Fin (mA 12615)) (Fin (mA 12615)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12615) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12615) (mA 12615) (tA 12615) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12615) (mA 12615) (tA 12615)).real
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

theorem table_second_layer_bad_subset (c : Ret 12615) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12615

/-! A first-layer variance payment from dimension 12615. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12615
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

theorem row_node_geometry {wr : WRet 12615} (hw : windowW wr)
    (θ : AHid 12615) {g : ℕ} (hg : g < Js 12615) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12615 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12615 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12615 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12615 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12615 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12615 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12615)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12615} (hw : windowW wr) :
    (gaussMat (mA 12615) 12615 (2 / (12615 : ℝ))).real {X | ∃ g < Js 12615,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12615 : ℝ)) ∨
      42 / (10 * (12615 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12615

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12616) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12616) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12616} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((14546266777 / 125000) : ℝ) * ((1003 / 1000) * ((797 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5896969 / 1000000000)) ^ 2 * ((1003 / 1000) * ((67033 / 2000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42641341 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5089877033 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5896969 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((130472059 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42641341 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1250343609 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5896969 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((320508539 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12616) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12616} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12616} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12616 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((67033 / 2000000000000)) /
        (2 * (1 - eta) * ((5896969 / 1000000000)) ^ 2) +
        12616 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5896969 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12616} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12616) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12616 - 1))).real
      {v | sgA (paperDesignP 12616) c a v < rowSigma} ∂BstLean.Part161.muI 12616 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12616 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12616 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12616 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12616

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12616) : Prop :=
  ∫ a, (stdGauss (Fin (12616 - 1))).real
    {v | sgA (paperDesignP 12616) c a v < rowSigma} ∂muI 12616 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12616) : SplitData 12616 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12616}
    (hw : WINDOW (paperDesignP 12616) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12616)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12616).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12616} (t : ℝ)
    (hw : WINDOW (paperDesignP 12616) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12616)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12616) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12616) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12616} (hw : WINDOW (paperDesignP 12616) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12616) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12616) c (hqSplit c) ⊆ bulkIx (paperDesignP 12616) c :=
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
noncomputable def hqRootInputs {c : Ret 12616} (t : ℝ)
    (hw : WINDOW (paperDesignP 12616) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12616))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12616 t c BstLean.Part266.agent12616.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12616] at h ⊢
    linarith

end BstLean.Part266.Row12616

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12616) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12616) c (rowSplit c wl ws),
    ((12616 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12616 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12616) c (rowSplit c wl ws),
    ((12616 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12616 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12616 - 1)))
    (rowSplit c wl ws).good a ∂muI 12616 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12616) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12616 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12616) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12616 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12616) c (rowSplit c wl ws),
    hellG2 12616 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12616 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12616}
    (hw : WINDOW (paperDesignP 12616) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12616}
    (hw : WINDOW (paperDesignP 12616) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12616 t c BstLean.Part266.agent12616.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12616

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12616) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12616)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12616)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12616)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12616)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12616)

theorem paidBaseCertificate (H : Set (Ret 12616)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12616

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12616) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12616)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12616)} (h : TablePayment H) :
    (retDist (paperCentres 12616)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12616))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12616} (t : ℝ)
    (hw : WINDOW (paperDesignP 12616) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12616 t c BstLean.Part266.agent12616.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12616

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12616
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12616) (a : Ix 12616) : Fin (Js 12616) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12616) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12616) : Measure (Fin (Js 12616)) :=
  (muI 12616).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12616) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12616) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12616) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12616)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12616) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12616)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12616)
    (M : Matrix (Fin (mA 12616)) (Fin (mA 12616)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12616) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12616) (mA 12616) (tA 12616) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12616) (mA 12616) (tA 12616)).real
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

theorem table_second_layer_bad_subset (c : Ret 12616) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12616

/-! A first-layer variance payment from dimension 12616. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12616
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

theorem row_node_geometry {wr : WRet 12616} (hw : windowW wr)
    (θ : AHid 12616) {g : ℕ} (hg : g < Js 12616) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12616 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12616 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12616 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12616 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12616 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12616 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12616)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12616} (hw : windowW wr) :
    (gaussMat (mA 12616) 12616 (2 / (12616 : ℝ))).real {X | ∃ g < Js 12616,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12616 : ℝ)) ∨
      42 / (10 * (12616 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12616

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12617) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12617) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12617} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((11637922377 / 100000) : ℝ) * ((1003 / 1000) * ((1593621 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((184273 / 31250000)) ^ 2 * ((1003 / 1000) * ((16755593 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341144051 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((254463589 / 50000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((184273 / 31250000)) * ((1001 / 1000 + 52 / 1000) * ((260923429 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341144051 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1250194911 / 200000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((184273 / 31250000)) * ((1001 / 1000 + 52 / 1000) * ((320483123 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12617) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12617} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12617} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12617 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((16755593 / 500000000000000)) /
        (2 * (1 - eta) * ((184273 / 31250000)) ^ 2) +
        12617 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((184273 / 31250000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12617} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12617) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12617 - 1))).real
      {v | sgA (paperDesignP 12617) c a v < rowSigma} ∂BstLean.Part161.muI 12617 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12617 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12617 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12617 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12617

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12617) : Prop :=
  ∫ a, (stdGauss (Fin (12617 - 1))).real
    {v | sgA (paperDesignP 12617) c a v < rowSigma} ∂muI 12617 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12617) : SplitData 12617 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12617}
    (hw : WINDOW (paperDesignP 12617) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12617)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12617).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12617} (t : ℝ)
    (hw : WINDOW (paperDesignP 12617) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12617)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12617) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12617) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12617} (hw : WINDOW (paperDesignP 12617) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12617) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12617) c (hqSplit c) ⊆ bulkIx (paperDesignP 12617) c :=
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
noncomputable def hqRootInputs {c : Ret 12617} (t : ℝ)
    (hw : WINDOW (paperDesignP 12617) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12617))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12617 t c BstLean.Part266.agent12617.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12617] at h ⊢
    linarith

end BstLean.Part266.Row12617

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12617) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12617) c (rowSplit c wl ws),
    ((12617 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12617 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12617) c (rowSplit c wl ws),
    ((12617 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12617 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12617 - 1)))
    (rowSplit c wl ws).good a ∂muI 12617 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12617) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12617 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12617) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12617 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12617) c (rowSplit c wl ws),
    hellG2 12617 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12617 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12617}
    (hw : WINDOW (paperDesignP 12617) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12617}
    (hw : WINDOW (paperDesignP 12617) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12617 t c BstLean.Part266.agent12617.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12617

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12617) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12617)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12617)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12617)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12617)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12617)

theorem paidBaseCertificate (H : Set (Ret 12617)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12617

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12617) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12617)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12617)} (h : TablePayment H) :
    (retDist (paperCentres 12617)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12617))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12617} (t : ℝ)
    (hw : WINDOW (paperDesignP 12617) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12617 t c BstLean.Part266.agent12617.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12617

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12617
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12617) (a : Ix 12617) : Fin (Js 12617) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12617) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12617) : Measure (Fin (Js 12617)) :=
  (muI 12617).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12617) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12617) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12617) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12617)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12617) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12617)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12617)
    (M : Matrix (Fin (mA 12617)) (Fin (mA 12617)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12617) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12617) (mA 12617) (tA 12617) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12617) (mA 12617) (tA 12617)).real
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

theorem table_second_layer_bad_subset (c : Ret 12617) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12617

/-! A first-layer variance payment from dimension 12617. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12617
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

theorem row_node_geometry {wr : WRet 12617} (hw : windowW wr)
    (θ : AHid 12617) {g : ℕ} (hg : g < Js 12617) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12617 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12617 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12617 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12617 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12617 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12617 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12617)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12617} (hw : windowW wr) :
    (gaussMat (mA 12617) 12617 (2 / (12617 : ℝ))).real {X | ∃ g < Js 12617,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12617 : ℝ)) ∨
      42 / (10 * (12617 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12617

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12618) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12618) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12618} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((58194177063 / 500000) : ℝ) * ((1003 / 1000) * ((796621 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2948251 / 500000000)) ^ 2 * ((1003 / 1000) * ((16752937 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42644679 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5088666647 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2948251 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((260902743 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((42644679 / 125000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((1562557803 / 250000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2948251 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((320457711 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12618) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12618} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12618} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12618 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((16752937 / 500000000000000)) /
        (2 * (1 - eta) * ((2948251 / 500000000)) ^ 2) +
        12618 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2948251 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12618} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12618) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12618 - 1))).real
      {v | sgA (paperDesignP 12618) c a v < rowSigma} ∂BstLean.Part161.muI 12618 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12618 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12618 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12618 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12618

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12618) : Prop :=
  ∫ a, (stdGauss (Fin (12618 - 1))).real
    {v | sgA (paperDesignP 12618) c a v < rowSigma} ∂muI 12618 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12618) : SplitData 12618 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12618}
    (hw : WINDOW (paperDesignP 12618) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12618)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12618).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12618} (t : ℝ)
    (hw : WINDOW (paperDesignP 12618) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12618)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12618) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12618) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12618} (hw : WINDOW (paperDesignP 12618) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12618) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12618) c (hqSplit c) ⊆ bulkIx (paperDesignP 12618) c :=
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
noncomputable def hqRootInputs {c : Ret 12618} (t : ℝ)
    (hw : WINDOW (paperDesignP 12618) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12618))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12618 t c BstLean.Part266.agent12618.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12618] at h ⊢
    linarith

end BstLean.Part266.Row12618

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12618) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12618) c (rowSplit c wl ws),
    ((12618 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12618 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12618) c (rowSplit c wl ws),
    ((12618 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12618 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12618 - 1)))
    (rowSplit c wl ws).good a ∂muI 12618 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12618) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12618 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12618) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12618 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12618) c (rowSplit c wl ws),
    hellG2 12618 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12618 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12618}
    (hw : WINDOW (paperDesignP 12618) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12618}
    (hw : WINDOW (paperDesignP 12618) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12618 t c BstLean.Part266.agent12618.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12618

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12618) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12618)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12618)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12618)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12618)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12618)

theorem paidBaseCertificate (H : Set (Ret 12618)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12618

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12618) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12618)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12618)} (h : TablePayment H) :
    (retDist (paperCentres 12618)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12618))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12618} (t : ℝ)
    (hw : WINDOW (paperDesignP 12618) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12618 t c BstLean.Part266.agent12618.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12618

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12618
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12618) (a : Ix 12618) : Fin (Js 12618) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12618) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12618) : Measure (Fin (Js 12618)) :=
  (muI 12618).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12618) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12618) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12618) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12618)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12618) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12618)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12618)
    (M : Matrix (Fin (mA 12618)) (Fin (mA 12618)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12618) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12618) (mA 12618) (tA 12618) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12618) (mA 12618) (tA 12618)).real
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

theorem table_second_layer_bad_subset (c : Ret 12618) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12618

/-! A first-layer variance payment from dimension 12618. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12618
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

theorem row_node_geometry {wr : WRet 12618} (hw : windowW wr)
    (θ : AHid 12618) {g : ℕ} (hg : g < Js 12618) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12618 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12618 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12618 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12618 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12618 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12618 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12618)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12618} (hw : windowW wr) :
    (gaussMat (mA 12618) 12618 (2 / (12618 : ℝ))).real {X | ∃ g < Js 12618,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12618 : ℝ)) ∨
      42 / (10 * (12618 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12618

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12619) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12619) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12619} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((29099371397 / 250000) : ℝ) * ((1003 / 1000) * ((1592863 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1474067 / 250000000)) ^ 2 * ((1003 / 1000) * ((8375141 / 250000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((68234163 / 200000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5088061633 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1474067 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((13044103 / 25000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((68234163 / 200000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6249488017 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1474067 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((320432303 / 500000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12619) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12619} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12619} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12619 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((8375141 / 250000000000000)) /
        (2 * (1 - eta) * ((1474067 / 250000000)) ^ 2) +
        12619 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1474067 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12619} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12619) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12619 - 1))).real
      {v | sgA (paperDesignP 12619) c a v < rowSigma} ∂BstLean.Part161.muI 12619 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12619 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12619 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12619 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12619

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12619) : Prop :=
  ∫ a, (stdGauss (Fin (12619 - 1))).real
    {v | sgA (paperDesignP 12619) c a v < rowSigma} ∂muI 12619 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12619) : SplitData 12619 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12619}
    (hw : WINDOW (paperDesignP 12619) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12619)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12619).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12619} (t : ℝ)
    (hw : WINDOW (paperDesignP 12619) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12619)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12619) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12619) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12619} (hw : WINDOW (paperDesignP 12619) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12619) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12619) c (hqSplit c) ⊆ bulkIx (paperDesignP 12619) c :=
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
noncomputable def hqRootInputs {c : Ret 12619} (t : ℝ)
    (hw : WINDOW (paperDesignP 12619) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12619))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12619 t c BstLean.Part266.agent12619.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12619] at h ⊢
    linarith

end BstLean.Part266.Row12619

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12619) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12619) c (rowSplit c wl ws),
    ((12619 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12619 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12619) c (rowSplit c wl ws),
    ((12619 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12619 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12619 - 1)))
    (rowSplit c wl ws).good a ∂muI 12619 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12619) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12619 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12619) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12619 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12619) c (rowSplit c wl ws),
    hellG2 12619 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12619 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12619}
    (hw : WINDOW (paperDesignP 12619) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12619}
    (hw : WINDOW (paperDesignP 12619) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12619 t c BstLean.Part266.agent12619.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12619

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12619) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12619)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12619)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12619)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12619)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12619)

theorem paidBaseCertificate (H : Set (Ret 12619)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12619

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12619) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12619)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12619)} (h : TablePayment H) :
    (retDist (paperCentres 12619)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12619))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12619} (t : ℝ)
    (hw : WINDOW (paperDesignP 12619) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12619 t c BstLean.Part266.agent12619.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12619

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12619
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12619) (a : Ix 12619) : Fin (Js 12619) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12619) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12619) : Measure (Fin (Js 12619)) :=
  (muI 12619).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12619) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12619) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12619) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12619)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12619) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12619)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12619)
    (M : Matrix (Fin (mA 12619)) (Fin (mA 12619)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12619) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12619) (mA 12619) (tA 12619) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12619) (mA 12619) (tA 12619)).real
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

theorem table_second_layer_bad_subset (c : Ret 12619) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12619

/-! A first-layer variance payment from dimension 12619. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12619
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

theorem row_node_geometry {wr : WRet 12619} (hw : windowW wr)
    (θ : AHid 12619) {g : ℕ} (hg : g < Js 12619) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12619 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12619 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12619 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12619 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12619 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12619 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12619)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12619} (hw : windowW wr) :
    (gaussMat (mA 12619) 12619 (2 / (12619 : ℝ))).real {X | ∃ g < Js 12619,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12619 : ℝ)) ∨
      42 / (10 * (12619 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12619

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12620) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12620) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12620} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((58203289221 / 500000) : ℝ) * ((1003 / 1000) * ((3184969 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1179207 / 200000000)) ^ 2 * ((1003 / 1000) * ((16747627 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341184141 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((254372837 / 50000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1179207 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((521722761 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341184141 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((781093121 / 125000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1179207 / 200000000)) * ((1001 / 1000 + 52 / 1000) * ((640813799 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12620) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12620} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12620} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12620 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((16747627 / 500000000000000)) /
        (2 * (1 - eta) * ((1179207 / 200000000)) ^ 2) +
        12620 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1179207 / 200000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12620} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12620) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12620 - 1))).real
      {v | sgA (paperDesignP 12620) c a v < rowSigma} ∂BstLean.Part161.muI 12620 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12620 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12620 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12620 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12620

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12620) : Prop :=
  ∫ a, (stdGauss (Fin (12620 - 1))).real
    {v | sgA (paperDesignP 12620) c a v < rowSigma} ∂muI 12620 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12620) : SplitData 12620 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12620}
    (hw : WINDOW (paperDesignP 12620) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12620)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12620).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12620} (t : ℝ)
    (hw : WINDOW (paperDesignP 12620) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12620)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12620) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12620) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12620} (hw : WINDOW (paperDesignP 12620) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12620) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12620) c (hqSplit c) ⊆ bulkIx (paperDesignP 12620) c :=
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
noncomputable def hqRootInputs {c : Ret 12620} (t : ℝ)
    (hw : WINDOW (paperDesignP 12620) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12620))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12620 t c BstLean.Part266.agent12620.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12620] at h ⊢
    linarith

end BstLean.Part266.Row12620

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12620) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12620) c (rowSplit c wl ws),
    ((12620 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12620 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12620) c (rowSplit c wl ws),
    ((12620 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12620 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12620 - 1)))
    (rowSplit c wl ws).good a ∂muI 12620 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12620) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12620 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12620) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12620 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12620) c (rowSplit c wl ws),
    hellG2 12620 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12620 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12620}
    (hw : WINDOW (paperDesignP 12620) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12620}
    (hw : WINDOW (paperDesignP 12620) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12620 t c BstLean.Part266.agent12620.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12620

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12620) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12620)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12620)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12620)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12620)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12620)

theorem paidBaseCertificate (H : Set (Ret 12620)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12620

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12620) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12620)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12620)} (h : TablePayment H) :
    (retDist (paperCentres 12620)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12620))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12620} (t : ℝ)
    (hw : WINDOW (paperDesignP 12620) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12620 t c BstLean.Part266.agent12620.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12620

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12620
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12620) (a : Ix 12620) : Fin (Js 12620) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12620) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12620) : Measure (Fin (Js 12620)) :=
  (muI 12620).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12620) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12620) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12620) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12620)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12620) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12620)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12620)
    (M : Matrix (Fin (mA 12620)) (Fin (mA 12620)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12620) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12620) (mA 12620) (tA 12620) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12620) (mA 12620) (tA 12620)).real
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

theorem table_second_layer_bad_subset (c : Ret 12620) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12620

/-! A first-layer variance payment from dimension 12620. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12620
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

theorem row_node_geometry {wr : WRet 12620} (hw : windowW wr)
    (θ : AHid 12620) {g : ℕ} (hg : g < Js 12620) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12620 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12620 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12620 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12620 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12620 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12620 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12620)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12620} (hw : windowW wr) :
    (gaussMat (mA 12620) 12620 (2 / (12620 : ℝ))).real {X | ∃ g < Js 12620,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12620 : ℝ)) ∨
      42 / (10 * (12620 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12620

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12621) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12621) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12621} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((7275982007 / 62500) : ℝ) * ((1003 / 1000) * ((796053 / 250000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5895801 / 1000000000)) ^ 2 * ((1003 / 1000) * ((16744973 / 500000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170598763 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2543425983 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5895801 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((521681409 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170598763 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6248002067 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5895801 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((640762999 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12621) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12621} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12621} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12621 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((16744973 / 500000000000000)) /
        (2 * (1 - eta) * ((5895801 / 1000000000)) ^ 2) +
        12621 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5895801 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12621} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12621) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12621 - 1))).real
      {v | sgA (paperDesignP 12621) c a v < rowSigma} ∂BstLean.Part161.muI 12621 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12621 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12621 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12621 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12621

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12621) : Prop :=
  ∫ a, (stdGauss (Fin (12621 - 1))).real
    {v | sgA (paperDesignP 12621) c a v < rowSigma} ∂muI 12621 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12621) : SplitData 12621 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12621}
    (hw : WINDOW (paperDesignP 12621) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12621)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12621).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12621} (t : ℝ)
    (hw : WINDOW (paperDesignP 12621) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12621)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12621) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12621) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12621} (hw : WINDOW (paperDesignP 12621) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12621) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12621) c (hqSplit c) ⊆ bulkIx (paperDesignP 12621) c :=
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
noncomputable def hqRootInputs {c : Ret 12621} (t : ℝ)
    (hw : WINDOW (paperDesignP 12621) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12621))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12621 t c BstLean.Part266.agent12621.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12621] at h ⊢
    linarith

end BstLean.Part266.Row12621

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12621) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12621) c (rowSplit c wl ws),
    ((12621 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12621 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12621) c (rowSplit c wl ws),
    ((12621 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12621 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12621 - 1)))
    (rowSplit c wl ws).good a ∂muI 12621 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12621) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12621 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12621) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12621 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12621) c (rowSplit c wl ws),
    hellG2 12621 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12621 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12621}
    (hw : WINDOW (paperDesignP 12621) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12621}
    (hw : WINDOW (paperDesignP 12621) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12621 t c BstLean.Part266.agent12621.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12621

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12621) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12621)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12621)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12621)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12621)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12621)

theorem paidBaseCertificate (H : Set (Ret 12621)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12621

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12621) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12621)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12621)} (h : TablePayment H) :
    (retDist (paperCentres 12621)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12621))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12621} (t : ℝ)
    (hw : WINDOW (paperDesignP 12621) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12621 t c BstLean.Part266.agent12621.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12621

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12621
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12621) (a : Ix 12621) : Fin (Js 12621) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12621) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12621) : Measure (Fin (Js 12621)) :=
  (muI 12621).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12621) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12621) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12621) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12621)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12621) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12621)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12621)
    (M : Matrix (Fin (mA 12621)) (Fin (mA 12621)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12621) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12621) (mA 12621) (tA 12621) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12621) (mA 12621) (tA 12621)).real
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

theorem table_second_layer_bad_subset (c : Ret 12621) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12621

/-! A first-layer variance payment from dimension 12621. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12621
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

theorem row_node_geometry {wr : WRet 12621} (hw : windowW wr)
    (θ : AHid 12621) {g : ℕ} (hg : g < Js 12621) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12621 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12621 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12621 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12621 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12621 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12621 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12621)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12621} (hw : windowW wr) :
    (gaussMat (mA 12621) 12621 (2 / (12621 : ℝ))).real {X | ∃ g < Js 12621,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12621 : ℝ)) ∨
      42 / (10 * (12621 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12621

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12622) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12622) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12622} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((23284961433 / 200000) : ℝ) * ((1003 / 1000) * ((636691 / 200000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((368473 / 62500000)) ^ 2 * ((1003 / 1000) * ((33484639 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170605427 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((317890457 / 62500000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((368473 / 62500000)) * ((1001 / 1000 + 52 / 1000) * ((521640063 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((170605427 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((3123629657 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((368473 / 62500000)) * ((1001 / 1000 + 52 / 1000) * ((640712207 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12622) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12622} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12622} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12622 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33484639 / 1000000000000000)) /
        (2 * (1 - eta) * ((368473 / 62500000)) ^ 2) +
        12622 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((368473 / 62500000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12622} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12622) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12622 - 1))).real
      {v | sgA (paperDesignP 12622) c a v < rowSigma} ∂BstLean.Part161.muI 12622 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12622 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12622 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12622 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12622

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12622) : Prop :=
  ∫ a, (stdGauss (Fin (12622 - 1))).real
    {v | sgA (paperDesignP 12622) c a v < rowSigma} ∂muI 12622 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12622) : SplitData 12622 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12622}
    (hw : WINDOW (paperDesignP 12622) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12622)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12622).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12622} (t : ℝ)
    (hw : WINDOW (paperDesignP 12622) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12622)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12622) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12622) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12622} (hw : WINDOW (paperDesignP 12622) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12622) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12622) c (hqSplit c) ⊆ bulkIx (paperDesignP 12622) c :=
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
noncomputable def hqRootInputs {c : Ret 12622} (t : ℝ)
    (hw : WINDOW (paperDesignP 12622) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12622))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12622 t c BstLean.Part266.agent12622.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12622] at h ⊢
    linarith

end BstLean.Part266.Row12622

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12622) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12622) c (rowSplit c wl ws),
    ((12622 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12622 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12622) c (rowSplit c wl ws),
    ((12622 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12622 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12622 - 1)))
    (rowSplit c wl ws).good a ∂muI 12622 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12622) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12622 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12622) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12622 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12622) c (rowSplit c wl ws),
    hellG2 12622 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12622 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12622}
    (hw : WINDOW (paperDesignP 12622) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12622}
    (hw : WINDOW (paperDesignP 12622) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12622 t c BstLean.Part266.agent12622.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12622

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12622) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12622)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12622)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12622)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12622)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12622)

theorem paidBaseCertificate (H : Set (Ret 12622)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12622

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12622) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12622)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12622)} (h : TablePayment H) :
    (retDist (paperCentres 12622)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12622))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12622} (t : ℝ)
    (hw : WINDOW (paperDesignP 12622) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12622 t c BstLean.Part266.agent12622.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12622

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12622
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12622) (a : Ix 12622) : Fin (Js 12622) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12622) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12622) : Measure (Fin (Js 12622)) :=
  (muI 12622).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12622) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12622) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12622) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12622)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12622) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12622)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12622)
    (M : Matrix (Fin (mA 12622)) (Fin (mA 12622)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12622) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12622) (mA 12622) (tA 12622) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12622) (mA 12622) (tA 12622)).real
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

theorem table_second_layer_bad_subset (c : Ret 12622) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12622

/-! A first-layer variance payment from dimension 12622. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12622
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

theorem row_node_geometry {wr : WRet 12622} (hw : windowW wr)
    (θ : AHid 12622) {g : ℕ} (hg : g < Js 12622) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12622 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12622 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12622 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12622 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12622 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12622 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12622)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12622} (hw : windowW wr) :
    (gaussMat (mA 12622) 12622 (2 / (12622 : ℝ))).real {X | ∃ g < Js 12622,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12622 : ℝ)) ∨
      42 / (10 * (12622 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12622

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12623) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12623) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12623} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((29108485761 / 250000) : ℝ) * ((1003 / 1000) * ((3182699 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((2947667 / 500000000)) ^ 2 * ((1003 / 1000) * ((33479333 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341224241 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((2542821389 / 500000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2947667 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((130399681 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341224241 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6246516707 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((2947667 / 500000000)) * ((1001 / 1000 + 52 / 1000) * ((640661423 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12623) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12623} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12623} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12623 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33479333 / 1000000000000000)) /
        (2 * (1 - eta) * ((2947667 / 500000000)) ^ 2) +
        12623 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((2947667 / 500000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12623} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12623) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12623 - 1))).real
      {v | sgA (paperDesignP 12623) c a v < rowSigma} ∂BstLean.Part161.muI 12623 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12623 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12623 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12623 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12623

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12623) : Prop :=
  ∫ a, (stdGauss (Fin (12623 - 1))).real
    {v | sgA (paperDesignP 12623) c a v < rowSigma} ∂muI 12623 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12623) : SplitData 12623 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12623}
    (hw : WINDOW (paperDesignP 12623) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12623)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12623).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12623} (t : ℝ)
    (hw : WINDOW (paperDesignP 12623) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12623)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12623) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12623) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12623} (hw : WINDOW (paperDesignP 12623) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12623) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12623) c (hqSplit c) ⊆ bulkIx (paperDesignP 12623) c :=
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
noncomputable def hqRootInputs {c : Ret 12623} (t : ℝ)
    (hw : WINDOW (paperDesignP 12623) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12623))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12623 t c BstLean.Part266.agent12623.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12623] at h ⊢
    linarith

end BstLean.Part266.Row12623

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12623) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12623) c (rowSplit c wl ws),
    ((12623 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12623 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12623) c (rowSplit c wl ws),
    ((12623 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12623 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12623 - 1)))
    (rowSplit c wl ws).good a ∂muI 12623 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12623) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12623 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12623) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12623 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12623) c (rowSplit c wl ws),
    hellG2 12623 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12623 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12623}
    (hw : WINDOW (paperDesignP 12623) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12623}
    (hw : WINDOW (paperDesignP 12623) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12623 t c BstLean.Part266.agent12623.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12623

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12623) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12623)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12623)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12623)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12623)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12623)

theorem paidBaseCertificate (H : Set (Ret 12623)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12623

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12623) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12623)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12623)} (h : TablePayment H) :
    (retDist (paperCentres 12623)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12623))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12623} (t : ℝ)
    (hw : WINDOW (paperDesignP 12623) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12623 t c BstLean.Part266.agent12623.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12623

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12623
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12623) (a : Ix 12623) : Fin (Js 12623) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12623) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12623) : Measure (Fin (Js 12623)) :=
  (muI 12623).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12623) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12623) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12623) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12623)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12623) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12623)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12623)
    (M : Matrix (Fin (mA 12623)) (Fin (mA 12623)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12623) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12623) (mA 12623) (tA 12623) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12623) (mA 12623) (tA 12623)).real
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

theorem table_second_layer_bad_subset (c : Ret 12623) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12623

/-! A first-layer variance payment from dimension 12623. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12623
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

theorem row_node_geometry {wr : WRet 12623} (hw : windowW wr)
    (θ : AHid 12623) {g : ℕ} (hg : g < Js 12623) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12623 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12623 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12623 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12623 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12623 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12623 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12623)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12623} (hw : windowW wr) :
    (gaussMat (mA 12623) 12623 (2 / (12623 : ℝ))).real {X | ∃ g < Js 12623,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12623 : ℝ)) ∨
      42 / (10 * (12623 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12623

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 12624) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 12624) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 12624} (he : (6 / 10 : ℝ) ≤ eR c) :
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
      _ ≤ ((116443040297 / 1000000) : ℝ) * ((1003 / 1000) * ((1590971 / 500000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((5895101 / 1000000000)) ^ 2 * ((1003 / 1000) * ((33474029 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341237571 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5085038363 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5895101 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((521557391 / 1000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((341237571 / 1000000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((6245774247 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((5895101 / 1000000000)) * ((1001 / 1000 + 52 / 1000) * ((80076331 / 125000000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 12624) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 12624} (he : 0 < eR c) :
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

theorem hq_displacement_root {c : Ret 12624} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 12624 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
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
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((33474029 / 1000000000000000)) /
        (2 * (1 - eta) * ((5895101 / 1000000000)) ^ 2) +
        12624 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((5895101 / 1000000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 12624} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 12624) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (12624 - 1))).real
      {v | sgA (paperDesignP 12624) c a v < rowSigma} ∂BstLean.Part161.muI 12624 ≤ lowMassBudget) :
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
    √(priceC hqKappa 12624 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 12624 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 12624 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row12624

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 12624) : Prop :=
  ∫ a, (stdGauss (Fin (12624 - 1))).real
    {v | sgA (paperDesignP 12624) c a v < rowSigma} ∂muI 12624 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 12624) : SplitData 12624 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 12624}
    (hw : WINDOW (paperDesignP 12624) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12624)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 12624).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 12624} (t : ℝ)
    (hw : WINDOW (paperDesignP 12624) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 12624)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 12624) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 12624) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 12624} (hw : WINDOW (paperDesignP 12624) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 12624) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12624) c (hqSplit c) ⊆ bulkIx (paperDesignP 12624) c :=
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
noncomputable def hqRootInputs {c : Ret 12624} (t : ℝ)
    (hw : WINDOW (paperDesignP 12624) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 12624))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12624 t c BstLean.Part266.agent12624.root where
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
    norm_num [biasRootCap, BstLean.Part266.agent12624] at h ⊢
    linarith

end BstLean.Part266.Row12624

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 12624) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 12624) c (rowSplit c wl ws),
    ((12624 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12624 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 12624) c (rowSplit c wl ws),
    ((12624 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12624 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (12624 - 1)))
    (rowSplit c wl ws).good a ∂muI 12624 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12624) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12624 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12624) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12624 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12624) c (rowSplit c wl ws),
    hellG2 12624 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12624 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 12624}
    (hw : WINDOW (paperDesignP 12624) c) (he : 0 < eR c)
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
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 12624}
    (hw : WINDOW (paperDesignP 12624) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 12624 t c BstLean.Part266.agent12624.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row12624

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 12624) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 12624)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 12624)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 12624)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 12624)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 12624)

theorem paidBaseCertificate (H : Set (Ret 12624)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row12624

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 12624) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 12624)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 12624)} (h : TablePayment H) :
    (retDist (paperCentres 12624)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 12624))ᶜ := by
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
noncomputable def hqRootInputs_on_base {c : Ret 12624} (t : ℝ)
    (hw : WINDOW (paperDesignP 12624) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 12624 t c BstLean.Part266.agent12624.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row12624

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row12624
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12624) (a : Ix 12624) : Fin (Js 12624) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12624) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12624) : Measure (Fin (Js 12624)) :=
  (muI 12624).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12624) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12624) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12624) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12624)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12624) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12624)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12624)
    (M : Matrix (Fin (mA 12624)) (Fin (mA 12624)) ℝ)
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

theorem table_second_layer_charge (c : Ret 12624) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12624) (mA 12624) (tA 12624) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12624) (mA 12624) (tA 12624)).real
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

theorem table_second_layer_bad_subset (c : Ret 12624) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row12624

/-! A first-layer variance payment from dimension 12624. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row12624
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

theorem row_node_geometry {wr : WRet 12624} (hw : windowW wr)
    (θ : AHid 12624) {g : ℕ} (hg : g < Js 12624) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12624 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12624 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12624 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12624 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12624 * b ^ 2 := by
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
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12624 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12624)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12624} (hw : windowW wr) :
    (gaussMat (mA 12624) 12624 (2 / (12624 : ℝ))).real {X | ∃ g < Js 12624,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12624 : ℝ)) ∨
      42 / (10 * (12624 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row12624
