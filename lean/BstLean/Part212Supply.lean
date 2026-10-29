import BstLean.Part212PlaneSupply
import BstLean.Part212Frobenius

/-! A concrete order-160 LJ supply uses the exact radial coefficient. -/
namespace BstLean.Part212

/-- This coefficient uses the proved plane, Frobenius and transverse envelopes. -/
noncomputable def latitudeJacobianSquared160 (n q : ℕ) : ℝ :=
  jacobianConstantSquared160 n (planeEnvelopeSquared160 n q) (frobEnvelopeSquared160 n)

theorem componentMoments160_proved {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q) :
    ComponentMoments160 n (planeEnvelopeSquared160 n q) (frobEnvelopeSquared160 n) := by
  intro c τ hw a v hv
  have hX := planeMoments_bound160 hn hq hw a hv
  exact ⟨hX.1, hX.2, frobMoment_bound160 hn hw a hv⟩

theorem jacobianMoment160_proved {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q) :
    JacobianMoment160 n (latitudeJacobianSquared160 n q) :=
  assemble_jacobian160 (by omega) (planeEnvelopeSquared_pos160 (by omega) hq)
    (frobEnvelope_pos160 (by omega)) (componentMoments160_proved hn hq)

theorem latitudeMoment160_proved {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q) :
    LatitudeMoment160 n (latitudeJacobianSquared160 n q) :=
  latitudeMoment160_of_jacobian (by omega) (jacobianMoment160_proved hn hq)

theorem latitudeJacobianSquared_pos160 {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q) :
    0 < latitudeJacobianSquared160 n q := by
  have hX := planeEnvelopeSquared_pos160 (by omega : 4 ≤ n) hq
  have hY := frobEnvelope_pos160 (by omega : 2 ≤ n)
  have hZ := operatorEnvelope_pos160 (by omega : 1 ≤ n)
  have hC := transverseConstant_pos160
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < BstLean.Part130.mA n := by
    exact_mod_cast (show 0 < BstLean.Part130.mA n by unfold BstLean.Part130.mA; positivity)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  positivity
end BstLean.Part212
