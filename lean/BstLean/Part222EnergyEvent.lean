import BstLean.Part222EnergyMoment
import BstLean.Part222Mass
import BstLean.Part215Actual

/-! One order-32 Markov payment controls the energy norm for a fixed input distribution. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part177
open BstLean.Part157 (Design Ret)
open BstLean.Part215 (standPoint measurable_standPoint)

noncomputable def standEnergyDeviation {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : TH n) (ξ : Fin n → ℝ) : ℝ := √(omK a (standPoint c τ ξ))-1

lemma standEnergyDeviation_eq {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : TH n) (ξ : Fin n → ℝ) :
    standEnergyDeviation c τ a ξ = energyDeviation (standPoint c τ ξ) a := by
  unfold standEnergyDeviation energyDeviation omK nrm
  rw [sqrt_div (normSq_nonneg _)]

lemma measurable_standEnergyDeviation {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (Function.uncurry (standEnergyDeviation c τ)) := by
  exact ((measurable_omK_comp measurable_fst
    ((measurable_standPoint c τ).comp measurable_snd)).sqrt).sub_const 1

lemma measurable_standEnergyDeviation_fixed {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : TH n) :
    Measurable (standEnergyDeviation c τ a) := by
  unfold standEnergyDeviation
  exact ((measurable_omK_comp (n := n) (θ := fun _ : Fin n → ℝ => a)
    measurable_const (measurable_standPoint c τ)).sqrt).sub_const 1

lemma standEnergyDeviation_bound {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    (a : TH n) (ξ : Fin n → ℝ) :
    |standEnergyDeviation c τ a ξ| ≤
      √(BstLean.Part131.frob a.2 * BstLean.Part131.frob a.1 / n)+1 := by
  have hω := omK_le (n := n) hn a
    (x := standPoint c τ ξ) (by rw [standPoint, normSq_sphPt hn])
  have hs := sqrt_le_sqrt hω
  change |√(omK a (standPoint c τ ξ))-1| ≤ _
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sqrt_nonneg _), abs_one]; linarith)

lemma standEnergyDeviation_integrable {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) (a : TH n) :
    Integrable (fun ξ => |standEnergyDeviation c τ a ξ|^32) (stdGauss (Fin n)) := by
  let B := BstLean.Part131.frob a.2 * BstLean.Part131.frob a.1 / n
  have hm := measurable_standEnergyDeviation_fixed c τ a
  refine Integrable.of_bound (hm.abs.pow_const 32).aestronglyMeasurable
    ((√B+1)^32) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (abs_nonneg _) (standEnergyDeviation_bound hn c τ a ξ) 32

noncomputable def energyAverage {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : TH n) : ℝ :=
  ∫ ξ, |standEnergyDeviation c τ a ξ|^32 ∂stdGauss (Fin n)

lemma measurable_energyAverage {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (energyAverage c τ) :=
  ((measurable_standEnergyDeviation c τ).abs.pow_const 32).stronglyMeasurable.integral_prod_right'
    |>.measurable

theorem energyAverage_moment {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (energyAverage c τ) (nuA n) ∧
    (∫ a, energyAverage c τ a ∂nuA n) ≤ energyWeightAllowance n^32 := by
  apply averaged_moment_bound (nuA n) (stdGauss (Fin n))
    (fun a ξ => |standEnergyDeviation c τ a ξ|^32)
    ((measurable_standEnergyDeviation c τ).abs.pow_const 32)
    (fun a ξ => pow_nonneg (abs_nonneg _) _)
    (standEnergyDeviation_integrable hn c τ) (pow_nonneg (energyWeightAllowance_nonneg n) _)
  intro ξ
  simp_rw [standEnergyDeviation_eq]
  exact energy_weight_moment hn _ (by rw [standPoint, normSq_sphPt hn])

noncomputable def energyAllowance (n : ℕ) : ℝ :=
  (20000 : ℝ)^((32 : ℝ)⁻¹) * energyWeightAllowance n

lemma energyAllowance_nonneg (n : ℕ) : 0 ≤ energyAllowance n :=
  mul_nonneg (rpow_nonneg (by norm_num) _) (energyWeightAllowance_nonneg n)

lemma energyAllowance_pow (n : ℕ) : energyAllowance n^32 = 20000*energyWeightAllowance n^32 := by
  unfold energyAllowance
  have h : ((20000 : ℝ)^((32 : ℝ)⁻¹))^32 = 20000 := by
    simpa only [Nat.cast_ofNat] using rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
  rw [mul_pow, h]

noncomputable def energyEvent {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Set (TH n) :=
  {a | energyAverage c τ a ≤ energyAllowance n^32}

lemma measurableSet_energyEvent {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    MeasurableSet (energyEvent c τ) := measurableSet_le (measurable_energyAverage c τ) measurable_const

/-- The energy event costs 0.00005 after all inputs are integrated. -/
theorem energy_event_charge {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real (energyEvent c τ)ᶜ ≤ 1/20000 := by
  have hnR : (0 : ℝ) < mA n := by exact_mod_cast (Nat.one_le_pow 2 n hn)
  have ha : 0 < agentLayerAllowance n := by
    unfold agentLayerAllowance layerAllowance
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (BstLean.Part195.rotationConstant_nonneg 16) (sqrt_nonneg _)) (by positivity)
  have hB : 0 < energyWeightAllowance n^32 := by
    unfold energyWeightAllowance
    positivity
  have hW : energyWeightAllowance n ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : (32 : ℕ) ≠ 0)] at hB
    exact (lt_irrefl _ hB)
  have hT : 0 < energyAllowance n^32 := by rw [energyAllowance_pow]; positivity
  have hi := energyAverage_moment hn c τ
  have h0 : ∀ a, 0 ≤ energyAverage c τ a := fun a =>
    integral_nonneg fun ξ => pow_nonneg (abs_nonneg _) _
  have hsub : (energyEvent c τ)ᶜ ⊆ {a | energyAllowance n^32 ≤ |energyAverage c τ a|} := by
    intro a ha
    have h : ¬ energyAverage c τ a ≤ energyAllowance n^32 := ha
    change energyAllowance n^32 ≤ |energyAverage c τ a|
    rw [abs_of_nonneg (h0 a)]
    exact (not_le.mp h).le
  have ht := BstLean.Part188.moment_tail (nuA n) (energyAverage c τ) 1 hT
    (by simpa only [pow_one, abs_of_nonneg (h0 _)] using hi.1)
    (by simpa only [pow_one, abs_of_nonneg (h0 _)] using hi.2)
  refine ((measureReal_mono hsub).trans ht).trans_eq ?_
  rw [pow_one, energyAllowance_pow]
  field_simp [hW]

/-- The event supplies Part188's energy interface for any design at this retained value. -/
theorem energyMoment_on_event {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hc : c.2.1.1 ∈ energyEvent c.1.2 (D.tau0 c)) :
    BstLean.Part188.EnergyMoment D c (energyAllowance n) := by
  have he : (fun ξ => |standEnergyDeviation c.1.2 (D.tau0 c) c.2.1.1 ξ|^32) =
      (fun ξ => (√(BstLean.Part188.inputEnergy D c ξ)-1)^32) := by
    funext ξ
    rw [← abs_pow, abs_of_nonneg (by positivity)]
    rfl
  refine ⟨energyAllowance_nonneg n, ?_, ?_⟩
  · rw [← he]
    exact standEnergyDeviation_integrable hn _ _ _
  · rw [← he]
    exact hc

#print axioms energyAverage_moment
#print axioms energy_event_charge
#print axioms energyMoment_on_event
end BstLean.Part222
