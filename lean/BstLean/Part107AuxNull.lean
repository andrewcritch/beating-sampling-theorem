import BstLean.Part107Defs

/-!
# Part 107, auxiliary null sets: `NonZero107`, `NullPar107`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

instance nullSing_gauss01 : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num)

/-- The coordinate `i` of a standard Gaussian vector is not zero, almost surely. -/
lemma coord_ne_zero_ae {n : ℕ} (i : Fin n) : ∀ᵐ g ∂stdGauss (Fin n), g i ≠ 0 := by
  rw [ae_iff]
  have hmp := measurePreserving_eval (μ := fun _ : Fin n => gaussianReal 0 1) i
  have h : {g : Fin n → ℝ | ¬ g i ≠ 0} = (Function.eval i) ⁻¹' {0} := by
    ext g; simp
  rw [h]
  unfold stdGauss
  rw [hmp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
  exact measure_singleton 0

theorem nonZero107 : NonZero107 := by
  intro n hn
  filter_upwards [coord_ne_zero_ae (⟨0, hn⟩ : Fin n)] with g hg h0
  exact hg (by rw [h0]; rfl)

/-- For `a₀ ≠ 0`, the line `a₀ y = a₁ x` is null for the standard Gaussian measure of `ℝ²`. -/
lemma line_null (a0 a1 : ℝ) (h0 : a0 ≠ 0) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {q : ℝ × ℝ | a0 * q.2 = a1 * q.1} = 0 := by
  have hm : MeasurableSet {q : ℝ × ℝ | a0 * q.2 = a1 * q.1} :=
    measurableSet_eq_fun (measurable_snd.const_mul a0) (measurable_fst.const_mul a1)
  rw [Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall fun x => ?_
  have : (Prod.mk x ⁻¹' {q : ℝ × ℝ | a0 * q.2 = a1 * q.1}) = {a1 * x / a0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [eq_div_iff h0, mul_comm]
  simp only [this, Pi.zero_apply]
  exact measure_singleton _

lemma line_null' {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a0 a1 : ℝ) (h0 : a0 ≠ 0) :
    stdGauss (Fin n) {b : Fin n → ℝ | a0 * b j = a1 * b i} = 0 := by
  have he : Function.Injective (![i, j] : Fin 2 → Fin n) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have h1 := BstLean.Part29.stdGauss_map_restrict (ι := Fin n) (![i, j] : Fin 2 → Fin n) he
  have h2 := (measurePreserving_finTwoArrow (gaussianReal 0 1))
  have hmeas : Measurable (fun z : Fin n → ℝ => z ∘ (![i, j] : Fin 2 → Fin n)) :=
    Measurable.of_eval fun k => measurable_pi_apply _
  have hm : MeasurableSet {q : ℝ × ℝ | a0 * q.2 = a1 * q.1} :=
    measurableSet_eq_fun (measurable_snd.const_mul a0) (measurable_fst.const_mul a1)
  have h3 := line_null a0 a1 h0
  rw [← h2.map_eq, Measure.map_apply h2.measurable hm] at h3
  change (stdGauss (Fin 2)) _ = 0 at h3
  rw [← h1, Measure.map_apply hmeas (h2.measurable hm)] at h3
  convert h3 using 2
  ext b
  simp [MeasurableEquiv.finTwoArrow]

theorem nullPar107 : NullPar107 := by
  intro n hn
  set i : Fin n := ⟨0, by omega⟩
  set j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hS : MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) | p.1 i * p.2 j = p.1 j * p.2 i} :=
    measurableSet_eq_fun
      (((measurable_pi_apply i).comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_snd))
      (((measurable_pi_apply j).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd))
  have hnull : gg n {p : (Fin n → ℝ) × (Fin n → ℝ) | p.1 i * p.2 j = p.1 j * p.2 i} = 0 := by
    rw [Measure.measure_prod_null hS]
    filter_upwards [coord_ne_zero_ae i] with a ha
    exact line_null' i j hij (a i) (a j) ha
  have hae : ∀ᵐ p ∂gg n, ¬ (p.1 i * p.2 j = p.1 j * p.2 i) := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with p hp θ h0
  apply hp
  have e1 : Real.cos θ * p.1 i + Real.sin θ * p.2 i = 0 := by
    simpa using congrFun h0 i
  have e2 : Real.cos θ * p.1 j + Real.sin θ * p.2 j = 0 := by
    simpa using congrFun h0 j
  have hcs := Real.cos_sq_add_sin_sq θ
  have hc : Real.cos θ * (p.1 i * p.2 j - p.1 j * p.2 i) = 0 := by linear_combination p.2 j * e1 - p.2 i * e2
  have hs : Real.sin θ * (p.1 i * p.2 j - p.1 j * p.2 i) = 0 := by linear_combination p.1 i * e2 - p.1 j * e1
  have : p.1 i * p.2 j - p.1 j * p.2 i = 0 := by
    linear_combination Real.cos θ * hc + Real.sin θ * hs - (p.1 i * p.2 j - p.1 j * p.2 i) * hcs
  linarith

end BstLean.Part107
