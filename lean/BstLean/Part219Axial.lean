import BstLean.Part219Ideal
import BstLean.Part161Lat

/-! Axial symmetry of the actual normalized shifted Gaussian mean. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part215
open BstLean.Part29 (stdGauss)

noncomputable def reflection {n : ℕ} (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  hhMat (e0 n - w)

lemma reflection_apply {n : ℕ} (w x : Fin n → ℝ) :
    reflection w *ᵥ x = x - (2 * (normSq w)⁻¹ * (w ⬝ᵥ x)) • w := by
  unfold reflection
  rw [hh_mulVec]
  have he : e0 n - (e0 n - w) = w := by abel
  rw [he]
  rfl

lemma reflection_normSq {n : ℕ} (w x : Fin n → ℝ) :
    normSq (reflection w *ᵥ x) = normSq x := hh_normSq _ _

lemma reflection_distribution {n : ℕ} (w : Fin n → ℝ) :
    (stdGauss (Fin n)).map (fun x => reflection w *ᵥ x) = stdGauss (Fin n) :=
  stdGauss_map_hh _

lemma reflection_sphPt {n : ℕ} (w x : Fin n → ℝ) (hx : normSq x ≠ 0) :
    sphPt (reflection w *ᵥ x) = reflection w *ᵥ sphPt x := by
  rw [sphPt_eq' (by simpa only [reflection_normSq] using hx), sphPt_eq' hx,
    reflection_normSq, Matrix.mulVec_smul]

/-- Reflection across a plane that contains the shift fixes the input mean. -/
theorem inputMean_reflection {n : ℕ} (hn : 1 ≤ n) (c w : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (hw : w ⬝ᵥ c = 0) :
    reflection w *ᵥ inputMean c τ = inputMean c τ := by
  have hQ : Measurable (fun x => reflection w *ᵥ x) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hc : reflection w *ᵥ c = c := by simp only [reflection_apply, hw, mul_zero,
    zero_smul, sub_zero]
  have he : ∀ᵐ x ∂stdGauss (Fin n),
      standPoint c τ (reflection w *ᵥ x) = reflection w *ᵥ standPoint c τ x := by
    filter_upwards [ae_normSq_ne hn c hτ.ne'] with x hx
    have he' : c + τ • (reflection w *ᵥ x) = reflection w *ᵥ (c + τ • x) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hc]
    unfold standPoint
    rw [he', reflection_sphPt w _ hx]
  have hmap := integral_map (μ := stdGauss (Fin n)) hQ.aemeasurable
    (measurable_standPoint c τ).aestronglyMeasurable
  rw [reflection_distribution] at hmap
  change inputMean c τ = ∫ x, standPoint c τ (reflection w *ᵥ x) ∂stdGauss (Fin n) at hmap
  rw [integral_congr_ae he, integral_matrix _ (integrable_standPoint hn c τ)] at hmap
  exact hmap.symm

/-- The input mean is parallel to the shift axis; no sign or moment estimate is assumed. -/
theorem inputMean_axial {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1)
    (a : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    inputMean (a • u) τ = (u ⬝ᵥ inputMean (a • u) τ) • u := by
  set m := inputMean (a • u) τ
  set α := u ⬝ᵥ m
  set w := m - α • u
  have huu : u ⬝ᵥ u = 1 := by simpa only [normSq, dotProduct, ← sq] using hu
  have hwu : w ⬝ᵥ u = 0 := by
    dsimp only [w]
    rw [sub_dotProduct, smul_dotProduct, huu, smul_eq_mul, mul_one, dotProduct_comm m u]
    exact sub_self _
  have hwc : w ⬝ᵥ (a • u) = 0 := by rw [dotProduct_smul, hwu, smul_zero]
  have hm := inputMean_reflection hn (a • u) w hτ hwc
  change reflection w *ᵥ m = m at hm
  have hwm : w ⬝ᵥ m = normSq w := by
    have he : m = w + α • u := by dsimp only [w]; abel
    rw [he, dotProduct_add, dotProduct_smul, hwu, smul_zero, add_zero]
    simp only [dotProduct, normSq, sq]
  rw [reflection_apply, hwm] at hm
  by_cases hw0 : normSq w = 0
  · have hz := normSq_eq_zero hw0
    exact sub_eq_zero.mp hz
  · have hc : 2 * (normSq w)⁻¹ * normSq w = 2 := by field_simp
    rw [hc] at hm
    have hz : w = 0 := by
      have hs : (2 : ℝ) • w = 0 := sub_eq_self.mp hm
      exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
    exact sub_eq_zero.mp hz

lemma integrable_dot {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (u : Fin n → ℝ) {f : X → Fin n → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => u ⬝ᵥ f x) μ := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, u i • ContinuousLinearMap.proj i
  have he : ∀ z, L z = u ⬝ᵥ z := by
    intro z
    simp only [L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct]
  simpa only [he] using L.integrable_comp hf

lemma dot_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (u : Fin n → ℝ) {f : X → Fin n → ℝ} (hf : Integrable f μ) :
    (∫ x, u ⬝ᵥ f x ∂μ) = u ⬝ᵥ (∫ x, f x ∂μ) := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, u i • ContinuousLinearMap.proj i
  have he : ∀ z, L z = u ⬝ᵥ z := by
    intro z
    simp only [L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct]
  simpa only [he] using L.integral_comp_comm hf

theorem inputMean_zero {n : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ) :
    inputMean (0 : Fin n → ℝ) τ = 0 := by
  set m := inputMean (0 : Fin n → ℝ) τ
  have h := inputMean_reflection hn 0 m hτ (by simp)
  change reflection m *ᵥ m = m at h
  have hmm : m ⬝ᵥ m = normSq m := by simp only [dotProduct, normSq, sq]
  rw [reflection_apply, hmm] at h
  by_cases hm0 : normSq m = 0
  · exact normSq_eq_zero hm0
  · have hc : 2 * (normSq m)⁻¹ * normSq m = 2 := by field_simp
    rw [hc] at h
    exact (smul_eq_zero.mp (sub_eq_self.mp h)).resolve_left (by norm_num)

/-- Normalization is monotone along a positive displacement in any direction. -/
lemma normalized_dot_monotone {n : ℕ} (u y : Fin n → ℝ) {a : ℝ} (ha : 0 < a)
    (hy : normSq y ≠ 0) (hx : normSq (y + a • u) ≠ 0) :
    u ⬝ᵥ sphPt y ≤ u ⬝ᵥ sphPt (y + a • u) := by
  set x := y + a • u
  have hy0 : 0 < nrm y := sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg y) hy.symm)
  have hx0 : 0 < nrm x := sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg x) hx.symm)
  have hxx : sphPt x ⬝ᵥ x = nrm x := by
    rw [sphPt_eq' hx, smul_dotProduct, smul_eq_mul]
    have hdot : x ⬝ᵥ x = nrm x ^ 2 := by rw [nrm_sq]; simp [normSq, dotProduct, sq]
    rw [hdot]
    change 1 / nrm x * nrm x ^ 2 = nrm x
    field_simp
  have hyy : sphPt y ⬝ᵥ y = nrm y := by
    rw [sphPt_eq' hy, smul_dotProduct, smul_eq_mul]
    have hdot : y ⬝ᵥ y = nrm y ^ 2 := by rw [nrm_sq]; simp [normSq, dotProduct, sq]
    rw [hdot]
    change 1 / nrm y * nrm y ^ 2 = nrm y
    field_simp
  have hxN : nrm (sphPt x) = 1 := by
    rw [sphPt_eq' hx, nrm_smul, abs_of_pos (by positivity)]
    change 1 / nrm x * nrm x = 1
    field_simp
  have hyN : nrm (sphPt y) = 1 := by
    rw [sphPt_eq' hy, nrm_smul, abs_of_pos (by positivity)]
    change 1 / nrm y * nrm y = 1
    field_simp
  have hxy : sphPt x ⬝ᵥ y ≤ nrm y := by
    have hh := (le_abs_self (sphPt x ⬝ᵥ y)).trans (abs_dot_le_nrm (sphPt x) y)
    simpa only [hxN, one_mul] using hh
  have hyx : sphPt y ⬝ᵥ x ≤ nrm x := by
    have hh := (le_abs_self (sphPt y ⬝ᵥ x)).trans (abs_dot_le_nrm (sphPt y) x)
    simpa only [hyN, one_mul] using hh
  have hp : 0 ≤ (sphPt x - sphPt y) ⬝ᵥ (x - y) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hxx, hyy]
    linarith
  have he : x - y = a • u := by dsimp only [x]; abel
  rw [he, dotProduct_smul, sub_dotProduct, smul_eq_mul,
    dotProduct_comm (sphPt x) u, dotProduct_comm (sphPt y) u] at hp
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp hp)

/-- The actual axial mean has a nonnegative coefficient for a nonnegative shift. -/
theorem inputMean_axial_nonneg {n : ℕ} (hn : 1 ≤ n) (u : Fin n → ℝ)
    {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    0 ≤ u ⬝ᵥ inputMean (a • u) τ := by
  rcases eq_or_lt_of_le ha with ha | ha
  · simp only [← ha, zero_smul, inputMean_zero hn hτ, dotProduct_zero, le_refl]
  have hpt : ∀ᵐ x ∂stdGauss (Fin n),
      u ⬝ᵥ standPoint 0 τ x ≤ u ⬝ᵥ standPoint (a • u) τ x := by
    filter_upwards [ae_normSq_ne hn (0 : Fin n → ℝ) hτ.ne',
      ae_normSq_ne hn (a • u) hτ.ne'] with x hy hx
    simp only [zero_add] at hy
    have h := normalized_dot_monotone u (τ • x) ha hy (by simpa only [add_comm] using hx)
    simpa only [standPoint, zero_add, add_comm, add_zero] using h
  have h := integral_mono_ae (integrable_dot u (integrable_standPoint hn 0 τ))
    (integrable_dot u (integrable_standPoint hn (a • u) τ)) hpt
  rw [dot_integral u (integrable_standPoint hn 0 τ),
    dot_integral u (integrable_standPoint hn (a • u) τ)] at h
  change u ⬝ᵥ inputMean 0 τ ≤ u ⬝ᵥ inputMean (a • u) τ at h
  simpa only [inputMean_zero hn hτ, dotProduct_zero] using h

#print axioms inputMean_reflection
#print axioms inputMean_axial
#print axioms inputMean_zero
#print axioms inputMean_axial_nonneg
end BstLean.Part219
