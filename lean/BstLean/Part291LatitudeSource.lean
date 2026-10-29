import BstLean.Part291LatitudeConstant
import BstLean.Part212Fields

namespace BstLean.BlueprintLow
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix muI consV)
open BstLean.Part166 (certI psiK fK sK winC)
open BstLean.Part153 (nuA)
open BstLean.Part150 (thetaC)
open BstLean.Part212 BstLean.Part167 BstLean.Part168

theorem latitudeComponentMomentsBand {n : ℕ} (hn : LowBand n) :
    ComponentMoments160 n 2.254 (frobEnvelopeSquared160 n) := by
  intro c τ hw a v hv
  have hn8 := hn.1
  have hm : (16000 : ℝ) ≤ (mA n : ℝ) := by
    exact_mod_cast (show 16000 ≤ mA n by
      unfold mA
      calc 16000 ≤ 8000 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn.1 2)
  have hR : 0 ≤ latitudeMaxMoment n := by unfold latitudeMaxMoment; positivity
  have hmax := latitudeMaxMoment_bound hn.1
  have hscalar := latitude_plane_scalar hn
  have hc := window_c_ne (by omega) hw
  refine ⟨?_, ?_, frobMoment_bound160 hn.1 hw a hv⟩
  · exact planeMoment_bound160_bound (by omega) hm hR hmax hscalar hc τ a hv _
      (measurable_YF_joint c τ) (fun A p => normSq_bhat_le _)
      (fun A A' h => YF_adm c τ h)
  · exact planeMoment_bound160_bound (by omega) hm hR hmax hscalar hc τ a hv _
      (measurable_YS_joint c τ) (fun A p => normSq_bhat_le _)
      (fun A A' h => YS_adm c τ h)

theorem latitudeMomentBand {n : ℕ} (hn : LowBand n) : LatitudeMoment160 n 5.036 := by
  have hn8 := hn.1
  have hX : (0 : ℝ) < 2.254 := by norm_num
  have hY := frobEnvelope_pos160 (by omega : 2 ≤ n)
  have hZ := operatorEnvelope_pos160 (by omega : 1 ≤ n)
  have ht := transverseConstant_pos160
  have hK0 : 0 ≤ jacobianConstantSquared160 n 2.254 (frobEnvelopeSquared160 n) := by
    unfold jacobianConstantSquared160
    positivity
  exact latitudeMoment160_of_jacobian (by omega) (jacobian160_mono hK0
    (latitude_jacobian_band hn.1) (assemble_jacobian160 (by omega) hX hY
      (latitudeComponentMomentsBand hn)))

theorem latitude_charge_from_moment {n : ℕ} (hn : 8000 ≤ n)
    (hLJ : LatitudeMoment160 n 5.036) (c : Fin n → ℝ) {τ Θ : ℝ}
    (hw : winC c τ) (hΘ : 0 < Θ)
    (hΘmom : (∫⁻ a, ENNReal.ofReal
      ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 12) ∂muI n) ≤
      ENNReal.ofReal (Θ ^ 12)) :
    (nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n
      (ENNReal.ofReal (latitudeConstant (√(5.036 : ℝ)) Θ (1 / 10000) / n))} ≤ 1 / 10000 := by
  have hτ := hw.1
  let w := fun a : Ix n => 1 - latitude (n := n) (√(normSq c)) τ a ^ 2
  have hm : Measurable w := measurable_const.sub
    ((measurable_latitude_comp measurable_const measurable_const measurable_id).pow_const 2)
  have hw0 : ∀ a, 0 ≤ w a := fun a => sub_nonneg.mpr (BstLean.Part162.latitude_sq_le _ _ _)
  have hw1 : ∀ a, w a ≤ 1 := fun a => sub_le_self 1 (sq_nonneg _)
  have hpos := latitude_weight_positive (by omega) c hτ
  have hB : (0 : ℝ) ≤ 5.036 / n := by positivity
  have hf := key_weighted_score80 (by omega) c τ fK BstLean.Part166.measurable_psiK_f
    hm hw0 hpos hw1 (by norm_num : (0 : ℝ) ≤ 1) hB hΘ.le hΘmom
    (fun a v hv => by simpa only [one_mul] using
      (latitude_fields_weighted_moment80 (by omega) hLJ c τ hw a hv).1)
  have hz := key_weighted_score80 (by omega) c τ sK BstLean.Part166.measurable_psiK_s
    hm hw0 hpos hw1 (scale := (n : ℝ) / 2) (by positivity) hB hΘ.le hΘmom
    (fun a v hv => (latitude_fields_weighted_moment80 (by omega) hLJ c τ hw a hv).2)
  apply latitudeEvent_charge_oneTenThousand (by omega) c τ
    (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5.036)) hΘ
  · simpa only [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5.036), ENNReal.ofReal_one,
      one_pow, one_mul, div_mul_eq_mul_div] using hf
  · simpa only [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5.036), latitudeCertZ,
      div_mul_eq_mul_div] using hz

def agentLatitudeEvent {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Set (BstLean.Part215.AgentPair n) :=
  {A | ((c, τ), A) ∈ latitudeEvent n (ENNReal.ofReal (3.042 / n))}

theorem agentLatitudeEvent_measurable {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    MeasurableSet (agentLatitudeEvent c τ) :=
  (measurableSet_latitudeEvent n _).preimage (measurable_const.prodMk measurable_id)

/-- One charge covers both actual latitude fields throughout the low band. -/
theorem agentLatitudeEvent_charge {n : ℕ} (hn : LowBand n) (c : Fin n → ℝ) {τ : ℝ}
    (hw : winC c τ) (hθ : thetaC c τ ≤ 0.528) :
    (nuA n).real (agentLatitudeEvent c τ)ᶜ ≤ (1 / 10000 : ℝ) := by
  have hn8 := hn.1
  have hm := latitudeCoefficient_mono (n := n) (p := 12) (by norm_num) (by omega)
    (by linarith [hw.2.1] : 0 ≤ thetaC c τ) hθ (by norm_num)
  have hp := latitudeCoefficient_pos (p := 12) (by norm_num) (by omega) c hw.1
  have hcharge := latitude_charge_from_moment hn.1 (latitudeMomentBand hn) c hw (hp.trans_le hm)
    ((latitude_moment_exact (p := 12) (by norm_num) (by omega) c hw.1).trans
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hp.le hm 12)))
  apply le_trans (measureReal_mono ?_) hcharge
  intro A hA hsmall
  apply hA
  exact hsmall.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (latitude_constant_band hn.1) (Nat.cast_nonneg _))) 80)

end BstLean.BlueprintLow
