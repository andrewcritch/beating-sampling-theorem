import BstLean.Part222Junction
import BstLean.Part211Junction

/-! The high-order operator event replaces the centre source's earlier operator payment. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part215

/-- Removing only the operator threshold preserves every other centre source condition. -/
def centreBase (n J : ℕ) (c : Fin n → ℝ) (τ : ℝ) : Set (BstLean.Part177.TH n) :=
  {a | ∃ MP : ℝ, 0 < MP ∧ a ∈ BstLean.Part211.CentreSource n J c τ MP}

theorem centreBase_charge {n J : ℕ} (hn : 4096 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ)
    (hr : BstLean.Part154.rhoBar n BstLean.Part154.csC < 1/4) :
    (nuA n).real (centreBase n J c τ)ᶜ ≤
      exp (-(n : ℝ)/2)+3445/(n : ℝ)^2+13*exp (-12) := by
  have hnR : (3 : ℝ) < n := by exact_mod_cast (show 3 < n by omega)
  let K := jS n 1 0^2*(n : ℝ)/((n : ℝ)-3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  let MP := (K+ε)/ε
  have hMP : 0 < MP := by dsimp [MP]; positivity
  have hsub : (centreBase n J c τ)ᶜ ⊆ (BstLean.Part211.CentreSource n J c τ MP)ᶜ := by
    intro a ha hb
    exact ha ⟨MP,hMP,hb⟩
  have h := BstLean.Part211.centre_source_charge (J := J) (P := 1) hn
    (by norm_num) (by omega) c hτ hMP (by norm_num : (0 : ℝ) ≤ 0) hr
  have he : (jS n 1 0^2*(n : ℝ)/(((n : ℝ)-1-2*(1 : ℕ))*MP))^1 = K/MP := by
    dsimp [K]
    simp only [pow_one, Nat.cast_one]
    rw [div_div]
    congr 1
    ring
  rw [he] at h
  have hb : K/MP ≤ ε := by
    apply (div_le_iff₀ hMP).2
    dsimp [MP]
    rw [mul_div_cancel₀ _ hε.ne']
    linarith
  exact ((measureReal_mono hsub).trans h).trans (by linarith)

noncomputable def operatorXiAllowance {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    (δ : ℝ≥0∞) : ℝ :=
  2/(mA n : ℝ)*τ^2*((operatorBudget c τ η/δ)^(1/160 : ℝ)).toReal

lemma operatorXiAllowance_identity {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ) (δ : ℝ≥0∞) :
    operatorXiAllowance c τ η δ =
      2/(mA n : ℝ)*BstLean.Part219.operatorAllowance c τ η δ^2 := by
  let B := operatorBudget c τ η/δ
  have he : ((B^(1/320 : ℝ)).toReal)^2 = (B^(1/160 : ℝ)).toReal := by
    rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← Real.rpow_two,
      ← Real.rpow_mul ENNReal.toReal_nonneg]
    congr 1
    norm_num
  unfold operatorXiAllowance BstLean.Part219.operatorAllowance
  rw [mul_pow, he]
  ring

theorem operatorXiAllowance_le {n : ℕ} (c : Fin n → ℝ) (τ η MP : ℝ) (δ : ℝ≥0∞)
    (hMP : BstLean.Part219.operatorAllowance c τ η δ^2 ≤ MP) :
    operatorXiAllowance c τ η δ ≤ MP*(2/(n : ℝ))/n := by
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; rfl
  have he : MP*(2/(n : ℝ))/n = (2/(n : ℝ)^2)*MP := by
    rw [mul_div_assoc, div_div, pow_two]
    ring
  rw [operatorXiAllowance_identity, hm, he]
  exact mul_le_mul_of_nonneg_left hMP (by positivity)

/-- The same order-160 event supplies the first input moment for the centre transfer. -/
theorem XiS_on_operator_event {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) {a : AgentPair n}
    (ha : a ∈ operatorEvent c τ η δ) :
    XiS a.1 a.2 c τ ≤ operatorXiAllowance c τ η δ := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hm : Measurable (fun ξ => Xq a c τ ξ) := by
    have h := (measurable_Xq_joint c τ).comp
      ((measurable_const : Measurable (fun _ : Fin n → ℝ => a)).prodMk
        (measurable_id : Measurable (fun ξ : Fin n → ℝ => ξ)))
    simpa only [Function.comp_def, id_eq] using h
  have h1 := ofReal_integral_le_lintegral (μ := stdGauss (Fin n)) (Xq_nonneg a c τ)
  have h2 := lp_mono_nat (μ := stdGauss (Fin n)) hm (Xq_nonneg a c τ)
    (q := 1) (P := 160) (by norm_num) (by norm_num)
  simp only [Nat.cast_one, pow_one, div_one, ENNReal.rpow_one] at h2
  have h3 := h1.trans (h2.trans (ENNReal.rpow_le_rpow ha (by norm_num)))
  have ht : (operatorBudget c τ η/δ)^(1/160 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hδ)
  have h4 := ENNReal.toReal_mono ht h3
  rw [ENNReal.toReal_ofReal (integral_nonneg (Xq_nonneg a c τ))] at h4
  exact mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2/(mA n : ℝ)*τ^2)

theorem centreSource_on_operator_event {n J : ℕ} (c : Fin n → ℝ) (τ η MP : ℝ)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) {a : AgentPair n}
    (hbase : a ∈ centreBase n J c τ) (hop : a ∈ operatorEvent c τ η δ)
    (hMP : operatorXiAllowance c τ η δ ≤ MP*(2/(n : ℝ))/n) :
    a ∈ BstLean.Part211.CentreSource n J c τ MP := by
  obtain ⟨MP0,hMP0,h0⟩ := hbase
  exact ⟨⟨h0.1.1,h0.1.2.1,h0.1.2.2.1,h0.1.2.2.2.1,h0.1.2.2.2.2.1,
    (XiS_on_operator_event c τ η hδ hop).trans hMP⟩,h0.2⟩

/-- This common source pays the centre tails, the error event, the operator event and energy once. -/
theorem centre_direction_energy_charge {n J : ℕ} (hn : 4096 ≤ n) (c : Fin n → ℝ)
    {τ η : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η)
    (hr : BstLean.Part154.rhoBar n BstLean.Part154.csC < 1/4) :
    (nuA n).real (centreBase n J c τ ∩
      (sharpErrorEvent c τ ∩ operatorEvent c τ η (ENNReal.ofReal (1/20000))) ∩
      energyEvent c τ)ᶜ ≤
      exp (-(n : ℝ)/2)+3445/(n : ℝ)^2+15*exp (-12)+19/50000 := by
  have h := common_event_charge_paper (by omega) c hτ hη (centreBase n J c τ)
    (centreBase_charge hn c hτ hr)
  exact h.trans (by linarith [exp_pos (-12 : ℝ)])

#print axioms centreBase_charge
#print axioms operatorXiAllowance_identity
#print axioms operatorXiAllowance_le
#print axioms XiS_on_operator_event
#print axioms centreSource_on_operator_event
#print axioms centre_direction_energy_charge
end BstLean.Part222
