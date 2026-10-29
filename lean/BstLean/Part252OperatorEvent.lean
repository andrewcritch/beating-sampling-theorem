import BstLean.Part252OperatorCap
import BstLean.Part249Covariance

/-! A measurable common event shares the order-160 payment with the fourth moment. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part215
open BstLean.Part29 (stdGauss)

def Operator160 (n : ℕ) : Set (AgFam n) :=
  {k | k.2 ∈ operatorEvent k.1.1 k.1.2 (6 / 1000) (ENNReal.ofReal (1 / 20000))}

theorem measurableSet_Operator160 (n : ℕ) : MeasurableSet (Operator160 n) := by
  have hy : Measurable (fun p : AgFam n × (Fin n → ℝ) => p.1.1.1 + p.1.1.2 • p.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hJ : Measurable (fun p : AgFam n × (Fin n → ℝ) =>
      BstLean.Part152.opN (jacT p.1.2.1 p.1.2.2 (sphPt (p.1.1.1 + p.1.1.2 • p.2)))) := by
    have h := (measurable_opN_jacT_joint (n := n) (m := mA n) (m₂ := mA n)).comp
      ((((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_snd).comp measurable_fst)).prodMk
        (measurable_sphPt.comp hy))
    simpa only [Function.comp_def] using h
  have hX : Measurable (fun p : AgFam n × (Fin n → ℝ) => Xq p.1.2 p.1.1.1 p.1.1.2 p.2) :=
    (hJ.pow_const 2).mul (BstLean.Part130.measurable_normSq.comp hy).inv
  have hH : Measurable (fun k : AgFam n => operatorHighMoment k.1.1 k.1.2 k.2) :=
    Measurable.lintegral_prod_right' ((hX.pow_const 160).ennreal_ofReal)
  have hI : Measurable (fun k : AgFam n =>
      ∫ ξ, (normSq (k.1.1 + k.1.2 • ξ))⁻¹ ^ 160 ∂stdGauss (Fin n)) :=
    (((BstLean.Part130.measurable_normSq.comp hy).inv.pow_const 160).stronglyMeasurable.integral_prod_right').measurable
  have hB : Measurable (fun k : AgFam n => operatorBudget k.1.1 k.1.2 (6 / 1000)) :=
    measurable_const.mul hI.ennreal_ofReal
  exact measurableSet_le hH (hB.div_const _)

theorem operator160_ret_charge {n : ℕ} (hn : 322 ≤ n)
    (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (Operator160 n))ᶜ ≤ (1 / 20000 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_Operator160 n) (by norm_num)
  intro c τ hτ
  have hh := operator_event_charge160 hn c hτ (by norm_num : (0 : ℝ) ≤ 6 / 1000)
    (δ := ENNReal.ofReal (1 / 20000)) (by norm_num) ENNReal.ofReal_ne_top
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real, Operator160, operatorEvent, compl_setOf, mem_setOf_eq, mem_compl_iff,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 20000)] using hh'

theorem operator160_ret_moment {n : ℕ} (hn : 8192 ≤ n) (D : Design n) :
    agentEv D (Operator160 n) ⊆ agentEv D (BstLean.Part245.MomentM12 n) := by
  intro c hc hτ
  exact fourth_on_operator_event_8192 hn c.1.2 hτ (hc hτ)

def sharedGood {n : ℕ} (D : Design n) : Set (Ret n) :=
  agentEv D (BstLean.Part249.optionBSharp n) ∩ agentEv D (Operator160 n)

theorem sharedGood_measurable {n : ℕ} (D : Design n) : MeasurableSet (sharedGood D) :=
  (measurableSet_agentEv D (BstLean.Part249.optionBSharp_measurable n)).inter
    (measurableSet_agentEv D (measurableSet_Operator160 n))

theorem sharedGood_charge {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (sharedGood D)ᶜ ≤ (3 / 10000 : ℝ) := by
  unfold sharedGood
  rw [compl_inter]
  exact (measureReal_union_le _ _).trans
    ((add_le_add (BstLean.Part249.optionB_ret_charge hn D hτW)
      (operator160_ret_charge (by omega) D hτW)).trans (by norm_num))

theorem sharedGood_subset {n : ℕ} (hn : 8192 ≤ n) (D : Design n) :
    sharedGood D ⊆ BstLean.Part249.optionBGood D := by
  intro c hc
  exact ⟨hc.1, operator160_ret_moment hn D hc.2⟩

structure SharedEventCertificate (n : ℕ) (D : Design n) : Prop where
  measurable : MeasurableSet (sharedGood D)
  charge : (retDist D.toCentres).real (sharedGood D)ᶜ ≤ (3 / 10000 : ℝ)
  moment_and_covariance : sharedGood D ⊆ BstLean.Part249.optionBGood D

theorem sharedEventCertificate {n : ℕ} (hn : 11883 ≤ n) (D : Design n)
    (hτW : TauWorld D) : SharedEventCertificate n D :=
  ⟨sharedGood_measurable D, sharedGood_charge hn D hτW, sharedGood_subset (by omega) D⟩

end BstLean.Part252
