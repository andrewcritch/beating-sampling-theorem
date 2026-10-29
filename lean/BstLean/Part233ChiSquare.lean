import BstLean.Part152LM

/-! Exact exponential payment for the conditional output norm. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)

theorem chiSquare_mgf {ι : Type*} [Fintype ι] {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun ξ : ι → ℝ => exp (t * ∑ i, ξ i ^ 2)) (stdGauss ι) ∧
    (∫ ξ : ι → ℝ, exp (t * ∑ i, ξ i ^ 2) ∂stdGauss ι) =
      ((√(1 - 2 * t))⁻¹) ^ Fintype.card ι := by
  have hind : iIndepFun (fun (i : ι) (ξ : ι → ℝ) => ξ i ^ 2) (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun _ => fun z : ℝ => z ^ 2) (fun _ => by fun_prop)
  have hm : ∀ i : ι, Measurable (fun ξ : ι → ℝ => ξ i ^ 2) := fun i => by fun_prop
  have hv : ∀ i : ι,
      Integrable (fun ξ : ι → ℝ => exp (t * ξ i ^ 2)) (stdGauss ι) ∧
      (∫ ξ : ι → ℝ, exp (t * ξ i ^ 2) ∂stdGauss ι) = (√(1 - 2 * t))⁻¹ := by
    intro i
    obtain ⟨hi, he⟩ := BstLean.Part152.gauss_mgf_sq ht
    unfold stdGauss
    refine ⟨integrable_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i) hi, ?_⟩
    rw [integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      hi.aestronglyMeasurable, he]
  constructor
  · simpa using hind.integrable_exp_mul_sum hm (s := Finset.univ) (fun i _ => (hv i).1)
  · have he := hind.mgf_sum hm Finset.univ (t := t)
    simp only [mgf, Finset.sum_apply] at he
    rw [he]
    simp_rw [(hv _).2]
    simp

/-- The exact Chernoff parameter gives the paper's logarithmic exponent. -/
theorem chiSquare_chernoff {ι : Type*} [Fintype ι] {e : ℝ} (he : 0 < e) :
    (stdGauss ι).real {ξ | (Fintype.card ι : ℝ) * (1 + e) ≤ ∑ i, ξ i ^ 2} ≤
      exp (-(Fintype.card ι : ℝ) * (e - log (1 + e)) / 2) := by
  let t : ℝ := e / (2 * (1 + e))
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht : t < 1 / 2 := by
    dsimp [t]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  obtain ⟨hi, hm⟩ := chiSquare_mgf (ι := ι) ht
  have h := measure_ge_le_exp_mul_mgf (μ := stdGauss ι)
    (X := fun ξ => ∑ i, ξ i ^ 2) (t := t)
    ((Fintype.card ι : ℝ) * (1 + e)) ht0 hi
  rw [mgf, hm] at h
  have hw : 1 - 2 * t = (1 + e)⁻¹ := by dsimp [t]; field_simp; ring
  have hroot : (√(1 - 2 * t))⁻¹ = exp (log (1 + e) / 2) := by
    rw [hw, Real.sqrt_inv, inv_inv, Real.exp_half, Real.exp_log (by positivity)]
  rw [hroot, ← Real.exp_nat_mul, ← Real.exp_add] at h
  convert h using 1
  congr 1
  dsimp [t]
  field_simp
  ring

end BstLean.Part233
#print axioms BstLean.Part233.chiSquare_mgf
#print axioms BstLean.Part233.chiSquare_chernoff
