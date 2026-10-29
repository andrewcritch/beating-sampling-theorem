import BstLean.Part221Supply
import BstLean.Part212FreshEvent

/-! One retained latitude event uses the active radial Jacobian constant. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix muI)
open BstLean.Part166 (psiK fK sK winC)
open BstLean.Part153 (nuA)
open BstLean.Part150 (thetaC)
open BstLean.Part212

noncomputable def activeLatitudeConstant160 (n : ℕ) (R2 θ : ℝ) : ℝ :=
  latitudeConstant (√(activeJacobianSquared160 n R2)) (latitudeCoefficient n 12 θ) (1 / 10000)

theorem active_latitude_charge160_of_moment {n : ℕ} (hn : 8000 ≤ n)
    {R2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2)
    (c : Fin n → ℝ) {τ Θ : ℝ} (hw : winC c τ) (hΘ : 0 < Θ)
    (hΘmom : ∫⁻ a, ENNReal.ofReal
      ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 12) ∂muI n ≤
      ENNReal.ofReal (Θ ^ 12)) :
    (nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n
      (ENNReal.ofReal (latitudeConstant (√(activeJacobianSquared160 n R2)) Θ
        (1 / 10000) / n))} ≤ 1 / 10000 := by
  have hτ : 0 < τ := hw.1
  let w := fun a : Ix n => 1 - latitude (n := n) (√(normSq c)) τ a ^ 2
  have hm : Measurable w := measurable_const.sub
    ((measurable_latitude_comp measurable_const measurable_const measurable_id).pow_const 2)
  have hw0 : ∀ a, 0 ≤ w a := fun a => sub_nonneg.mpr (BstLean.Part162.latitude_sq_le _ _ _)
  have hw1 : ∀ a, w a ≤ 1 := fun a =>
    sub_le_self 1 (sq_nonneg (latitude (n := n) (√(normSq c)) τ a))
  have hpos := latitude_weight_positive (by omega) c hτ
  have hK := activeJacobianSquared_pos160 hn hR0
  have hB : 0 ≤ activeJacobianSquared160 n R2 / n := div_nonneg hK.le (Nat.cast_nonneg _)
  have hj := activeLatitudeMoment160 hn hR0 hR
  have hf := key_weighted_score80 (by omega) c τ fK BstLean.Part166.measurable_psiK_f
    hm hw0 hpos hw1 (by norm_num : (0 : ℝ) ≤ 1) hB hΘ.le hΘmom
    (fun a v hv => by simpa only [one_mul] using
      (latitude_fields_weighted_moment80 (by omega) hj c τ hw a hv).1)
  have hz := key_weighted_score80 (by omega) c τ sK BstLean.Part166.measurable_psiK_s
    hm hw0 hpos hw1 (scale := (n : ℝ) / 2) (by positivity) hB hΘ.le hΘmom
    (fun a v hv => (latitude_fields_weighted_moment80 (by omega) hj c τ hw a hv).2)
  have hs : √(activeJacobianSquared160 n R2) ^ 2 = activeJacobianSquared160 n R2 :=
    Real.sq_sqrt hK.le
  apply latitudeEvent_charge_oneTenThousand (by omega) c τ (Real.sqrt_pos.mpr hK) hΘ
  · simpa only [hs, ENNReal.ofReal_one, one_pow, one_mul, div_mul_eq_mul_div] using hf
  · simpa only [hs, latitudeCertZ, div_mul_eq_mul_div] using hz


theorem active_latitude_charge160_window {n : ℕ} (hn : 8000 ≤ n)
    {R2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2)
    (c : Fin n → ℝ) {τ θplus : ℝ} (hw : winC c τ)
    (hθ : thetaC c τ ≤ θplus) (hθ1 : θplus ≤ 1) :
    (nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n
      (ENNReal.ofReal (activeLatitudeConstant160 n R2 θplus / n))} ≤ 1 / 10000 := by
  have hm := latitudeCoefficient_mono (n := n) (p := 12) (by norm_num) (by omega)
    (by linarith [hw.2.1] : 0 ≤ thetaC c τ) hθ hθ1
  have hp := latitudeCoefficient_pos (p := 12) (by norm_num) (by omega) c hw.1
  apply active_latitude_charge160_of_moment hn hR0 hR c hw (hp.trans_le hm)
  exact (latitude_moment_exact (p := 12) (by norm_num) (by omega) c hw.1).trans
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hp.le hm 12))

def activeRetainedEvent160 (n : ℕ) (R2 : ℝ) : Set (AgFam n) :=
  guardedLatitudeEvent n (latitudeWorldWindow n)
    (ENNReal.ofReal (activeLatitudeConstant160 n R2 (55 / 100) / n))

theorem measurableSet_activeRetainedEvent160 (n : ℕ) (R2 : ℝ) :
    MeasurableSet (activeRetainedEvent160 n R2) :=
  measurableSet_guardedLatitudeEvent (measurableSet_latitudeWorldWindow n) _

/-- The retained-data complement is charged once, at one ten-thousandth. -/
theorem active_retained_charge160 {n : ℕ} (hn : 8000 ≤ n)
    {R2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2)
    (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (activeRetainedEvent160 n R2))ᶜ ≤ 1 / 10000 := by
  apply guardedLatitudeEvent_retained_charge D hτ
    (measurableSet_latitudeWorldWindow n) (by norm_num)
  intro c τ ht hw
  exact active_latitude_charge160_window hn hR0 hR c hw hw.2.2 (by norm_num)

theorem activeRetainedEvent160_fields {n : ℕ} {R2 : ℝ} {k : AgFam n}
    (hk : k ∈ activeRetainedEvent160 n R2) (hw : winC k.1.1 k.1.2) :
    k ∈ latitudeEvent n (ENNReal.ofReal (activeLatitudeConstant160 n R2 (55 / 100) / n)) :=
  hk hw

end BstLean.Part221
