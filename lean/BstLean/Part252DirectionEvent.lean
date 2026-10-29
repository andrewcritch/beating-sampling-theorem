import BstLean.Part215SharpRadius
import BstLean.Part160Event

/-! The sharp direction-error event is measurable in all retained parameters. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part215
open BstLean.Part29 (stdGauss)

theorem measurable_standPoint_fam {X : Type*} [MeasurableSpace X] {n : ℕ}
    {c : X → Fin n → ℝ} {τ : X → ℝ} {ξ : X → Fin n → ℝ}
    (hc : Measurable c) (hτ : Measurable τ) (hξ : Measurable ξ) :
    Measurable (fun p => standPoint (c p) (τ p) (ξ p)) :=
  measurable_sphPt.comp (hc.add (hτ.smul hξ))

theorem measurable_inputErrorAverage_fam (n : ℕ) :
    Measurable (fun p : AgFam n × (Fin n → ℝ) =>
      inputErrorAverage p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let Y := (AgFam n × (Fin n → ℝ)) × (Fin n → ℝ)
  have hc : Measurable (fun p : Y => p.1.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hτ : Measurable (fun p : Y => p.1.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have ha : Measurable (fun p : Y => p.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hx := measurable_standPoint_fam hc hτ (measurable_snd.comp measurable_fst)
  have hy := measurable_standPoint_fam hc hτ measurable_snd
  have hm' : Measurable (fun p : Y =>
      pairInputError p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2) := by
    have hh := ((measurable_pairVector_inputs.comp (ha.prodMk (hx.prodMk hy))).const_smul
      ((n : ℝ)⁻¹)).sub (continuous_pairIdeal.measurable.comp (hx.prodMk hy))
    convert hh using 1
    funext p j
    rfl
  exact hm'.stronglyMeasurable.integral_prod_right'.measurable

def DirectionError (n : ℕ) : Set (AgFam n) :=
  {k | k.2 ∈ sharpErrorEvent k.1.1 k.1.2}

theorem measurableSet_DirectionError (n : ℕ) : MeasurableSet (DirectionError n) := by
  have hy : Measurable (fun p : AgFam n × (Fin n → ℝ) => p.1.1.1 + p.1.1.2 • p.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hr : Measurable (fun p : AgFam n × (Fin n → ℝ) =>
      radiusWeight p.1.1.1 p.1.1.2 p.2) :=
    ((measurable_snd.comp (measurable_fst.comp measurable_fst)).div
      (BstLean.Part130.measurable_normSq.comp hy).sqrt).ennreal_ofReal.pow_const _
  have hm : Measurable (fun k : AgFam n => errorInputMoment k.1.1 k.1.2 k.2) :=
    Measurable.lintegral_prod_right' (hr.mul
      ((BstLean.Part130.measurable_normSq.comp (measurable_inputErrorAverage_fam n)).sqrt.ennreal_ofReal.pow_const 24))
  have hθ : Measurable (fun k : AgFam n => BstLean.Part150.thetaC k.1.1 k.1.2) := by
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    have hc : Measurable (fun k : AgFam n => normSq k.1.1) :=
      BstLean.Part130.measurable_normSq.comp (measurable_fst.comp measurable_fst)
    have ht : Measurable (fun k : AgFam n => (n : ℝ) * k.1.2 ^ 2) :=
      ((measurable_snd.comp measurable_fst).pow_const 2).const_mul _
    exact ht.div ((hc.add ht).sqrt.pow_const 2)
  have hR : Measurable (fun k : AgFam n =>
      radiusCoefficient n 12 (BstLean.Part150.thetaC k.1.1 k.1.2)) :=
    hθ.div (measurable_const.sub ((hθ.const_mul _).div_const _))
  have hb : Measurable (fun k : AgFam n => sharpErrorBudget k.1.1 k.1.2) :=
    measurable_const.mul ((((hR.div_const _).pow_const 12).ennreal_ofReal).pow_const _)
  exact measurableSet_le (hm.pow_const _) (hb.div_const _)

theorem directionError_ret_charge {n : ℕ} (hn : 27 ≤ n)
    (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (DirectionError n))ᶜ ≤ (7 / 25000 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_DirectionError n) (by norm_num)
  intro c τ hτ
  simpa only [DirectionError, sharpErrorEvent, compl_setOf, mem_setOf_eq] using
    sharp_error_event_one_payment hn c hτ

end BstLean.Part252
