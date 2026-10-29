import BstLean.Part236Master
import BstLean.Part293Ledger

/-! A single END certificate at dimension 8000 transfers to the whole band. -/
namespace BstLean.Part293
open Real BstLean.Part232 BstLean.Part236

noncomputable def rootAllowance : ℝ := 0.0064
noncomputable def samplingDeviation : ℝ := 0.000005
noncomputable def worldBase : ℝ := 0.419
noncomputable def agentFrame : ℝ := 1.56
noncomputable def frameMaximum : ℝ := 0.324425

noncomputable def reindexEnd {n c f a h H : ℝ} (m : ℝ)
    (e : EndCertificate n c f a h H) : EndCertificate m c f a h H :=
  { e with plus := e.plus }

theorem reindexEnd_payment_le {n m c f a h H : ℝ} (hnm : n ≤ m)
    (e : EndCertificate n c f a h H) : (reindexEnd m e).payment ≤ e.payment := by
  apply min_le_min_left
  exact add_le_add
    (exp_le_exp.mpr (mul_le_mul_of_nonpos_right hnm e.plus_nonpos))
    (exp_le_exp.mpr (mul_le_mul_of_nonpos_right hnm e.minus_nonpos))

noncomputable def reindexCell {n c f a h H : ℝ} (m : ℝ)
    (e : Option (EndCertificate n c f a h H)) : Option (EndCertificate m c f a h H) :=
  e.map (reindexEnd m)

theorem reindexCell_payment_le {n m c f a h H : ℝ} (hnm : n ≤ m)
    (e : Option (EndCertificate n c f a h H)) :
    cellPayment (reindexCell m e) ≤ cellPayment e := by
  cases e with
  | none => exact le_rfl
  | some e => exact reindexEnd_payment_le hnm e

structure EndpointInputs where
  radius : RadiusCover
  frame : FrameCover
  maximum : frame.maximum = frameMaximum
  certificate : ∀ i j, Option (EndCertificate 8000 (worldBase + frame.h (j + 1))
    agentFrame BstLean.Part156.aL (rootAllowance + samplingDeviation) (radius.h (i + 1)))
  payment : ∀ i < radius.K, ∀ j < frame.K,
    cellPayment (certificate i j) ≤ endpointIntercept + radiusPrice * radius.h i ^ 2 +
      framePrice quadraticPrice linearPrice (frame.h j)
  terminal : 1 ≤ endpointIntercept + radiusPrice * radius.h radius.K ^ 2

noncomputable def EndpointInputs.atDimension (C : EndpointInputs) (n : ℕ) (i j : ℕ) :=
  reindexCell (n : ℝ) (C.certificate i j)

theorem EndpointInputs.payment_atDimension (C : EndpointInputs) {n : ℕ} (hn : 8000 ≤ n)
    (i : ℕ) (hi : i < C.radius.K) (j : ℕ) (hj : j < C.frame.K) :
    cellPayment (C.atDimension n i j) ≤ endpointIntercept + radiusPrice * C.radius.h i ^ 2 +
      framePrice quadraticPrice linearPrice (C.frame.h j) :=
  (reindexCell_payment_le (by exact_mod_cast hn) (C.certificate i j)).trans
    (C.payment i hi j hj)

end BstLean.Part293

/-- info: 'BstLean.Part293.EndpointInputs.payment_atDimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.EndpointInputs.payment_atDimension
