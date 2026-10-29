import BstLean.Part236Integration

/-! The low-band ledger keeps event charges, restricted moments and root prices separate. -/
namespace BstLean.Part293
open Real Set MeasureTheory

noncomputable def worldCharge : ℝ := 0.001092
noncomputable def sourceCharge : ℝ := 0.000526
noncomputable def latitudeCharge : ℝ := 0.000107
noncomputable def schurCharge : ℝ := 0.00025
noncomputable def angleCharge : ℝ := 0.0000062
noncomputable def tableCharge : ℝ := 0.000706
noncomputable def samplingCharge : ℝ := 1 / 10 ^ 9
noncomputable def retainedCharge : ℝ :=
  worldCharge + sourceCharge + latitudeCharge + schurCharge + angleCharge + tableCharge
noncomputable def radiusMoment : ℝ := 3.164 / 10 ^ 8
noncomputable def coeffK : ℝ := 0.01219
noncomputable def coeffD : ℝ := 0.00000787
noncomputable def endpointIntercept : ℝ := 0.0057
noncomputable def radiusPrice : ℝ := 8950
noncomputable def quadraticPrice : ℝ := 1.081
noncomputable def linearPrice : ℝ := 0.06
noncomputable def restrictedPayment : ℝ :=
  radiusPrice * radiusMoment + 0.372 * quadraticPrice * coeffK ^ 2 +
    0.448 * linearPrice * coeffD
noncomputable def ledger : ℝ := retainedCharge + endpointIntercept + restrictedPayment + samplingCharge

theorem retained_charge_eq : retainedCharge = 0.0026872 := by
  norm_num [retainedCharge, worldCharge, sourceCharge, latitudeCharge, schurCharge,
    angleCharge, tableCharge]

theorem restricted_payment_eq : restrictedPayment = 0.0003431447924852 := by
  norm_num [restrictedPayment, radiusPrice, radiusMoment, quadraticPrice, linearPrice,
    coeffK, coeffD]

theorem ledger_eq : ledger = 0.0087303457924852 := by
  norm_num [ledger, retained_charge_eq, endpointIntercept, restricted_payment_eq,
    samplingCharge]

/-- Only the required one-percent failure budget is exported to the classifier. -/
theorem ledger_le_one_percent : ledger ≤ 1 / 100 := by
  rw [ledger_eq]
  norm_num

theorem root_rounding {h : ℝ} (hh : h ≤ 0.006322616) : h ≤ 0.0064 := by linarith

section Charges
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

structure NetworkCharge (cap : ℝ) where
  event : Set Ω
  measurable : MeasurableSet event
  nonneg : 0 ≤ cap
  complement : μ.real eventᶜ ≤ cap

noncomputable def NetworkCharge.inter {a b : ℝ}
    (A : NetworkCharge μ a) (B : NetworkCharge μ b) : NetworkCharge μ (a + b) where
  event := A.event ∩ B.event
  measurable := A.measurable.inter B.measurable
  nonneg := add_nonneg A.nonneg B.nonneg
  complement := by
    rw [compl_inter]
    exact (measureReal_union_le _ _).trans (add_le_add A.complement B.complement)

/-- A conditional exception has its own charge without paying the conditioning complement again. -/
noncomputable def NetworkCharge.of_restricted {E G : Set Ω} {cap : ℝ}
    (hE : MeasurableSet E) (hG : MeasurableSet G) (hcap : 0 ≤ cap)
    (h : μ.real (E ∩ Gᶜ) ≤ cap) : NetworkCharge μ cap where
  event := Eᶜ ∪ G
  measurable := hE.compl.union hG
  nonneg := hcap
  complement := by simpa only [compl_union, compl_compl] using h

structure EventLedger where
  world : NetworkCharge μ worldCharge
  source : NetworkCharge μ sourceCharge
  latitude : NetworkCharge μ latitudeCharge
  schur : NetworkCharge μ schurCharge
  angle : NetworkCharge μ angleCharge
  table : NetworkCharge μ tableCharge

noncomputable def EventLedger.retained (L : EventLedger μ) :
    NetworkCharge μ retainedCharge :=
  (((((L.world.inter μ L.source).inter μ L.latitude).inter μ L.schur).inter μ L.angle).inter μ L.table)

end Charges

section Restricted
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

structure RestrictedPayment (E : Set Ω) (f : Ω → ℝ) (cap : ℝ) where
  measurable : Measurable f
  nonneg : ∀ ω, 0 ≤ f ω
  integrable : IntegrableOn f E μ
  bound : ∫ ω in E, f ω ∂μ ≤ cap

/-- A root price is not a network-event charge. -/
structure RootPrice (E : Set Ω) (Q q : Ω → ℝ) (cap : ℝ) : Prop where
  nonneg : 0 ≤ cap
  bound : ∀ ω ∈ E, |√(Q ω) - √(q ω)| ≤ cap

end Restricted
end BstLean.Part293

/-- info: 'BstLean.Part293.ledger_le_one_percent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.ledger_le_one_percent
/-- info: 'BstLean.Part293.EventLedger.retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.EventLedger.retained
