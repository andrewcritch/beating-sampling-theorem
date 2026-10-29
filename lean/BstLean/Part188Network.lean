import BstLean.Part188Interfaces
import BstLean.Part188WF

/-! The actual network quantities in the weighted domination premise. -/

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nrm nrm_sq)

variable {n : ℕ}

lemma measurable_inputEnergy (D : Design n) (c : Ret n) : Measurable (inputEnergy D c) :=
  (measurable_normSq.comp (BstLean.Part160.measurable_hStand D c)).div_const _

lemma measurable_centreCoordinate (D : Design n) (c : Ret n) :
    Measurable (centreCoordinate D c) :=
  (Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp (BstLean.Part160.measurable_hStand D c)).mul_const _).div_const _

lemma measurable_weight (a d : ℝ) {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) : Measurable (fun x => weight a d (f x)) :=
  ((measurable_const.sub (hf.pow_const 2)).max measurable_const).inv.sqrt

lemma measurableSet_goodInput {X : Type*} [MeasurableSpace X] {omega f : X → ℝ}
    (homega : Measurable omega) (hf : Measurable f) (a d : ℝ) :
    MeasurableSet {x | goodInput a d (omega x) (f x)} :=
  (measurableSet_le measurable_const homega).inter
    (measurableSet_le (hf.pow_const 2) measurable_const)

/-- The identity in the corrected WF domination step, in Lean's network normalization. -/
theorem network_residual_energy (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hb : normSq (D.bA c.1 c.2.1.1) ≠ 0) (ξ : Fin n → ℝ) :
    normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) =
      (n : ℝ) * (inputEnergy D c ξ - centreCoordinate D c ξ ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [BstLean.Part136.normSq_res hb]
  unfold inputEnergy centreCoordinate
  rw [div_pow, mul_pow, Real.sq_sqrt hnR.le, nrm_sq]
  field_simp
  <;> ring

/-- The corrected good set lies inside the network residual-mass set. -/
theorem network_good_subset_residual (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hb : normSq (D.bA c.1 c.2.1.1) ≠ 0) (a d : ℝ) :
    {ξ | goodInput a d (inputEnergy D c ξ) (centreCoordinate D c ξ)} ⊆
      {ξ | (n : ℝ) * d ≤ normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ))} := by
  intro ξ hξ
  change (n : ℝ) * d ≤ normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ))
  rw [network_residual_energy hn D c hb ξ]
  exact mul_le_mul_of_nonneg_left (goodInput_residual hξ) (Nat.cast_nonneg _)

end BstLean.Part188
