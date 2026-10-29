import BstLean.Part215Average
import BstLean.Part215Event

/-! Actual Gaussian input averages of the sharp fixed-pair error. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200
open BstLean.Part29 (stdGauss)

abbrev AgentPair (n : ℕ) :=
  Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ

noncomputable def standPoint {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :=
  sphPt (c + τ • ξ)

lemma measurable_standPoint {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (standPoint c τ) :=
  measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ))

lemma continuous_pairIdeal {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => pairIdeal p.1 p.2) := by
  unfold pairIdeal BstLean.Part145.kg projT
  have hk := BstLean.Part130.continuous_kappa
  fun_prop

lemma measurable_pairVector_inputs {n : ℕ} :
    Measurable (fun p : AgentPair n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      pairVector p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hJ : Measurable (fun p : AgentPair n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      jacT p.1.1 p.1.2 p.2.1) := by
    have hp : Measurable (fun p : AgentPair n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (p.1, p.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have h := (measurable_jacT_joint (n := n) (m := mA n) (m₂ := mA n)).comp hp
    simpa only [Function.comp_def] using h
  have hT : Measurable (fun J : Matrix (Fin (mA n)) (Fin n) ℝ => Jᵀ) :=
    continuous_id.matrix_transpose.measurable
  have hH : Continuous (fun p : AgentPair n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      hid2 p.1.1 p.1.2 p.2.2) := by
    have h1 : Continuous (fun p : AgentPair n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        p.1.1 *ᵥ p.2.2) :=
      Continuous.matrix_mulVec (continuous_fst.comp continuous_fst)
        (continuous_snd.comp continuous_snd)
    have h2 := Continuous.matrix_mulVec (continuous_snd.comp continuous_fst)
      (continuous_reluV.comp h1)
    exact continuous_reluV.comp h2
  have h := BstLean.Part134.measurable_mulVec_joint.comp ((hT.comp hJ).prodMk hH.measurable)
  simpa only [Function.comp_def, pairVector] using h

noncomputable def pairInputError {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) (ξ ξ' : Fin n → ℝ) : Fin n → ℝ :=
  (n : ℝ)⁻¹ • pairVector a.1 a.2 (standPoint c τ ξ) (standPoint c τ ξ') -
    pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')

lemma measurable_pairInputError {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun p : (AgentPair n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      pairInputError c τ p.1.1 p.1.2 p.2) := by
  let Y := (AgentPair n × (Fin n → ℝ)) × (Fin n → ℝ)
  have hξ : Measurable (fun p : Y => p.1.2) := measurable_snd.comp measurable_fst
  have hξ' : Measurable (fun p : Y => p.2) := measurable_snd
  have ha : Measurable (fun p : Y => p.1.1) := measurable_fst.comp measurable_fst
  have hp := ha.prodMk (((measurable_standPoint c τ).comp hξ).prodMk
    ((measurable_standPoint c τ).comp hξ'))
  have h := ((measurable_pairVector_inputs.comp hp).const_smul ((n : ℝ)⁻¹)).sub
    (continuous_pairIdeal.measurable.comp
      (((measurable_standPoint c τ).comp hξ).prodMk ((measurable_standPoint c τ).comp hξ')))
  convert h using 1
  funext p
  rfl

lemma pairInputError_le {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) (ξ ξ' : Fin n → ℝ) :
    nrm (pairInputError c τ a ξ ξ') ≤
      |(n : ℝ)⁻¹| * (opN a.1 ^ 2 * opN a.2 ^ 2) + 1 := by
  have hx := normSq_sphPt hn (c + τ • ξ)
  have hx' := normSq_sphPt hn (c + τ • ξ')
  have hV := pairVector_le a.1 a.2 hx (standPoint c τ ξ')
  have hN : nrm (standPoint c τ ξ') = 1 := by simp [standPoint, nrm, hx']
  rw [hN, mul_one] at hV
  exact (nrm_sub_le _ _).trans (add_le_add
    (by rw [nrm_smul]; exact mul_le_mul_of_nonneg_left hV (abs_nonneg _))
    (pairIdeal_le hx hx'))

noncomputable def inputErrorAverage {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) (ξ : Fin n → ℝ) : Fin n → ℝ :=
  ∫ ξ', pairInputError c τ a ξ ξ' ∂stdGauss (Fin n)

noncomputable def idealInputAverage {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (ξ : Fin n → ℝ) : Fin n → ℝ :=
  ∫ ξ', pairIdeal (standPoint c τ ξ) (standPoint c τ ξ') ∂stdGauss (Fin n)

/-- The deterministic ideal average has a uniform bound. This is a coarse bound. -/
theorem idealInputAverage_le_one {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    nrm (idealInputAverage c τ ξ) ≤ 1 := by
  have hm : Measurable (fun ξ' => pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')) := by
    have hp : Measurable (fun ξ' : Fin n → ℝ =>
        (standPoint c τ ξ, standPoint c τ ξ')) :=
      measurable_const.prodMk (measurable_standPoint c τ)
    have h := (continuous_pairIdeal (n := n)).measurable.comp hp
    simpa only [Function.comp_def] using h
  have hbound : ∀ ξ', nrm (pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')) ≤ 1 :=
    fun ξ' => pairIdeal_le (normSq_sphPt hn _) (normSq_sphPt hn _)
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hiN : Integrable (fun ξ' => nrm (pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')))
      (stdGauss (Fin n)) :=
    Integrable.of_bound (BstLean.Part130.measurable_normSq.comp hm).sqrt.aestronglyMeasurable
      1 (ae_of_all _ fun ξ' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
        exact hbound ξ')
  have hi := integrable_vector_of_nrm hm hiN
  have hmean : nrm (idealInputAverage c τ ξ) ≤
      ∫ ξ', nrm (pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')) ∂stdGauss (Fin n) :=
    nrm_integral_le hi hiN
  exact hmean.trans
    ((integral_mono hiN (integrable_const 1) hbound).trans_eq (by simp))

lemma measurable_inputErrorAverage {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun p : AgentPair n × (Fin n → ℝ) => inputErrorAverage c τ p.1 p.2) :=
  (measurable_pairInputError c τ).stronglyMeasurable.integral_prod_right'.measurable

theorem inputErrorAverage_fixed_moment64 {n : ℕ} (hn : 15 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    (∫⁻ a, ENNReal.ofReal (nrm (inputErrorAverage c τ a ξ)) ^ 64 ∂nuA n) ≤
      ENNReal.ofReal (BstLean.Part209.pairEpsilon n 16 (1 / 100)) ^ 64 := by
  have hn0 : 1 ≤ n := by omega
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hF : Measurable (fun p : AgentPair n × (Fin n → ℝ) =>
      pairInputError c τ p.1 ξ p.2) := by
    have hp : Measurable (fun p : AgentPair n × (Fin n → ℝ) => ((p.1, ξ), p.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    have h := (measurable_pairInputError c τ).comp hp
    simpa only [Function.comp_def] using h
  have hbound : ∀ a, ENNReal.ofReal (nrm (inputErrorAverage c τ a ξ)) ^ 64 ≤
      ∫⁻ ξ', ENNReal.ofReal (nrm (pairInputError c τ a ξ ξ')) ^ 64 ∂stdGauss (Fin n) := by
    intro a
    have hm : Measurable (fun ξ' => pairInputError c τ a ξ ξ') := by
      have hp : Measurable (fun ξ' : Fin n → ℝ => ((a, ξ), ξ')) :=
        measurable_const.prodMk measurable_id
      have h := (measurable_pairInputError c τ).comp hp
      simpa only [Function.comp_def] using h
    have hiN : Integrable (fun ξ' => nrm (pairInputError c τ a ξ ξ')) (stdGauss (Fin n)) :=
      Integrable.of_bound (BstLean.Part130.measurable_normSq.comp hm).sqrt.aestronglyMeasurable
        _ (ae_of_all _ fun ξ' => by
          rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
          exact pairInputError_le hn0 c τ a ξ ξ')
    exact average_nrm_pow_le (by norm_num) hm (integrable_vector_of_nrm hm hiN) hiN
  refine (lintegral_mono hbound).trans ?_
  rw [lintegral_lintegral_swap
    (((BstLean.Part130.measurable_normSq.comp hF).sqrt.ennreal_ofReal.pow_const 64).aemeasurable)]
  calc
    _ ≤ ∫⁻ _ξ' : Fin n → ℝ,
        ENNReal.ofReal (BstLean.Part209.pairEpsilon n 16 (1 / 100)) ^ 64
          ∂stdGauss (Fin n) := by
      apply lintegral_mono
      intro ξ'
      have h := BstLean.Part209.paperPairError_sharp_moment hn (by norm_num : 1 ≤ 16)
        (normSq_sphPt hn0 (c + τ • ξ)) (normSq_sphPt hn0 (c + τ • ξ'))
      have hb := BstLean.Part209.lintegral_of_moment
        (paperPairError_nonneg _ _) h.1 h.2
      have hε : 0 ≤ BstLean.Part209.pairEpsilon n 16 (1 / 100) :=
        add_nonneg (BstLean.Part209.meanEpsilon_nonneg n 16 (by norm_num) (by norm_num))
          (BstLean.Part209.fluctuationRoot_nonneg n 16)
      simpa only [pairInputError, standPoint, paperPairError, AgentPair, mA,
        show 4 * 16 = 64 by norm_num, ENNReal.ofReal_pow hε] using hb
    _ = _ := by simp

#print axioms inputErrorAverage_fixed_moment64

/-- The radius factor is fixed before integration of the Agent matrices. -/
noncomputable def radiusWeight {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (τ / nrm (c + τ • ξ)) ^ 24

lemma measurable_radiusWeight {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (radiusWeight c τ) := by
  unfold radiusWeight nrm
  have hN : Measurable (fun ξ : Fin n → ℝ => √(normSq (c + τ • ξ))) :=
    (BstLean.Part130.measurable_normSq.comp
    (measurable_const.add (measurable_id.const_smul τ))).sqrt
  exact (measurable_const.div hN).ennreal_ofReal.pow_const _

/-- This is the order-24 input error moment before its root is taken. -/
noncomputable def errorInputMoment {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) : ℝ≥0∞ :=
  ∫⁻ ξ, radiusWeight c τ ξ * ENNReal.ofReal (nrm (inputErrorAverage c τ a ξ)) ^ 24
    ∂stdGauss (Fin n)

theorem actual_weighted_error_moment64 {n : ℕ} (hn : 15 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) :
    (∫⁻ a, errorInputMoment c τ a ^ (8 / 3 : ℝ) ∂nuA n) ≤
      ENNReal.ofReal (BstLean.Part209.pairEpsilon n 16 (1 / 100)) ^ 64 *
        (∫⁻ ξ, radiusWeight c τ ξ ∂stdGauss (Fin n)) ^ (8 / 3 : ℝ) := by
  apply weighted_mixed_moment (nuA n) (stdGauss (Fin n)) (radiusWeight c τ)
    (fun a ξ => nrm (inputErrorAverage c τ a ξ)) (measurable_radiusWeight c τ)
    ((BstLean.Part130.measurable_normSq.comp (measurable_inputErrorAverage c τ)).sqrt)
    (fun _ _ => nrm_nonneg _)
  exact inputErrorAverage_fixed_moment64 hn c τ

/-- The actual shared-weight error event has one payment, with a scalar radius certificate. -/
theorem actual_error_event_charge {n : ℕ} (hn : 15 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) {B δ : ℝ≥0∞} (hB : B ≠ 0) (hBt : B ≠ ∞)
    (hbudget : ENNReal.ofReal (BstLean.Part209.pairEpsilon n 16 (1 / 100)) ^ 64 *
      (∫⁻ ξ, radiusWeight c τ ξ ∂stdGauss (Fin n)) ^ (8 / 3 : ℝ) ≤ B * δ) :
    (nuA n) {a | errorInputMoment c τ a ^ (8 / 3 : ℝ) ≤ B}ᶜ ≤ δ := by
  exact weighted_error_event_charge (nuA n) (stdGauss (Fin n)) (radiusWeight c τ)
    (fun a ξ => nrm (inputErrorAverage c τ a ξ)) (measurable_radiusWeight c τ)
    ((BstLean.Part130.measurable_normSq.comp (measurable_inputErrorAverage c τ)).sqrt)
    (fun _ _ => nrm_nonneg _) (inputErrorAverage_fixed_moment64 hn c τ) hB hBt hbudget

#print axioms actual_weighted_error_moment64
#print axioms actual_error_event_charge

/-- The deterministic ideal average requires no Markov payment. -/
theorem ideal_weighted_moment24_coarse {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) :
    (∫⁻ ξ, radiusWeight c τ ξ * ENNReal.ofReal (nrm (idealInputAverage c τ ξ)) ^ 24
      ∂stdGauss (Fin n)) ≤ ∫⁻ ξ, radiusWeight c τ ξ ∂stdGauss (Fin n) := by
  apply lintegral_mono
  intro ξ
  have h : ENNReal.ofReal (nrm (idealInputAverage c τ ξ)) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (idealInputAverage_le_one hn c τ ξ)
  simpa using mul_le_mul_right (pow_le_pow_left' h 24) (radiusWeight c τ ξ)

#print axioms idealInputAverage_le_one
#print axioms ideal_weighted_moment24_coarse
end BstLean.Part215
