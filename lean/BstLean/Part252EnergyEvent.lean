import BstLean.Part252EnergyCap
import BstLean.Part160Event

namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160
open BstLean.Part177 BstLean.Part222
open BstLean.Part29 (stdGauss)

def Energy32 (n : ℕ) : Set (AgFam n) :=
  {k | k.2 ∈ energyEvent k.1.1 k.1.2}

theorem measurableSet_Energy32 (n : ℕ) : MeasurableSet (Energy32 n) := by
  have hy : Measurable (fun p : AgFam n × (Fin n → ℝ) => p.1.1.1 + p.1.1.2 • p.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hm : Measurable (fun p : AgFam n × (Fin n → ℝ) =>
      |standEnergyDeviation p.1.1.1 p.1.1.2 p.1.2 p.2| ^ 32) :=
    (((measurable_omK_comp (measurable_snd.comp measurable_fst)
      (measurable_sphPt.comp hy)).sqrt.sub_const 1).abs).pow_const 32
  have ha : Measurable (fun k : AgFam n => energyAverage k.1.1 k.1.2 k.2) :=
    hm.stronglyMeasurable.integral_prod_right' |>.measurable
  exact measurableSet_le ha measurable_const

theorem energy32_ret_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (Energy32 n))ᶜ ≤ (1 / 20000 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_Energy32 n) (by norm_num)
  intro c τ _
  exact energy_event_charge hn c τ

end BstLean.Part252
