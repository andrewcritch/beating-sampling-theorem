import BstLean.Part144Joint

/-!
# Part 144, tools for the joint step

Role: `delegations/statements/p144-spec.md`, item 2. Tools for `Part144JointT`.

* `QD_F3`: `QD` does not read the last matrix of `F`; `measurable_QDT`.
* `lintegral_QD_le`: `E[K·QD] ≤ K·e²` under `(W, A, F)` if `‖kD − c‖₂ ≤ e`.
* `ofReal_integral_le_lintegral`: `ofReal (∫ g) ≤ ∫⁻ ofReal g`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
  BstLean.Part142

variable {N mW n mA mF : ℕ}

/-- `QD` does not read the last matrix of `F`. -/
lemma QD_F3 (c : ℝ) (W : MlpParam N mW n) (A A' : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (F₃ F₃' : Matrix (Fin 1) (Fin mF) ℝ) :
    QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) =
      QD c ((W, A, A', F₁, F₂, F₃') : Rest N mW n mA mF) := by
  unfold QD
  refine integral_congr_ae (Filter.Eventually.of_forall fun uu => ?_)
  simp only
  rw [kD_zU, kD_zU]

lemma measurable_QDT (hN : 1 ≤ N) (c : ℝ) :
    Measurable (fun t : Trip N mW n mA mF =>
      QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF)) := by
  have := lawU2_prob hN
  have mQ : Measurable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c) :=
    ((measurable_kD.sub measurable_const).pow_const
      2).stronglyMeasurable.integral_prod_left'.measurable
  have memb : Measurable (fun t : Trip N mW n mA mF =>
      ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  have h3 := mQ.comp memb
  simp only [Function.comp_def] at h3
  exact h3

/-- `E[K·QD] ≤ K·e²` under `(W, A, F)`, if `‖kD − c‖₂ ≤ e` and `K ≥ 0`. -/
theorem lintegral_QD_le (hN : 1 ≤ N) {c e : ℝ}
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e) {K : ℝ}
    (hK0 : 0 ≤ K) :
    ∫⁻ t : Trip N mW n mA mF,
        ENNReal.ofReal (K * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF))
        ∂lawT N mW n mA mF ≤ ENNReal.ofReal (K * e ^ 2) := by
  have := lawU2_prob hN
  have e1 : ∫⁻ t : Trip N mW n mA mF,
      ENNReal.ofReal (K * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF))
        ∂lawT N mW n mA mF =
      ∫⁻ r, ENNReal.ofReal (K * QD c r) ∂lawR N mW n mA mF := by
    have mπ : Measurable (fun r : Rest N mW n mA mF => (r.1, r.2.1, r.2.2.2)) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have mH : Measurable (fun t : Trip N mW n mA mF =>
        ENNReal.ofReal (K * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF))) :=
      ENNReal.measurable_ofReal.comp ((measurable_QDT hN c).const_mul K)
    unfold lawT
    rw [← lawR_drop, lintegral_map mH mπ]
    refine lintegral_congr fun r => ?_
    simp only
    rw [QD_indep]
  rw [e1]
  have iQ : Integrable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c)
      (lawR N mW n mA mF) := hD.int_sq.integral_prod_right
  have eQ : ∫ r, QD c r ∂lawR N mW n mA mF ≤ e ^ 2 := by
    have := integral_prod_symm (μ := lawU2 N) (ν := lawR N mW n mA mF) _ hD.int_sq
    unfold QD
    rw [← this]
    exact hD.le
  rw [← ofReal_integral_eq_lintegral_ofReal (iQ.const_mul K)
    (Filter.Eventually.of_forall fun r => mul_nonneg hK0 (QD_nonneg c r))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left eQ hK0

/-- `ofReal (∫ g) ≤ ∫⁻ ofReal g` for an integrable `g`. -/
lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : Integrable g μ) :
    ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  have hp : Integrable (fun x => max (g x) 0) μ := hg.pos_part
  have h1 : ∫ x, g x ∂μ ≤ ∫ x, max (g x) 0 ∂μ :=
    integral_mono hg hp fun x => le_max_left _ _
  have h2 : ENNReal.ofReal (∫ x, max (g x) 0 ∂μ) = ∫⁻ x, ENNReal.ofReal (max (g x) 0) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hp (Filter.Eventually.of_forall fun x => le_max_right _ _)
  have h3 : ∀ x, ENNReal.ofReal (max (g x) 0) = ENNReal.ofReal (g x) := by
    intro x
    rcases le_total (g x) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  simp_rw [h3] at h2
  exact (ENNReal.ofReal_le_ofReal h1).trans h2.le

end BstLean.Part144

open BstLean.Part144 in
#print axioms lintegral_QD_le
