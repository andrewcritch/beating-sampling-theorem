import BstLean.Part209Contraction
import BstLean.Part200Network

/-! An actual conditional-mean error bound on the low-length complement. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

variable {n m p : ℕ}

theorem pairMean_he_moment (hp : 1 ≤ p) {s : ℕ} (hs : 1 ≤ s) {v : ℝ} (hv : 0 ≤ v)
    {x : Fin n → ℝ} (hx : normSq x = 1) (x' : Fin n → ℝ) :
    Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      nrm (pairMean (p := p) (2 / (p : ℝ)) A₁ x x') ^ s) (gaussMat m n v) ∧
    (∫ A₁, nrm (pairMean (p := p) (2 / (p : ℝ)) A₁ x x') ^ s ∂gaussMat m n v) ≤
      matrixMoment m n s v * nrm x' ^ s := by
  obtain ⟨hi, hb⟩ := opN_moment (p := m) (q := n) hv hs
  have hm : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      nrm (pairMean (p := p) (2 / (p : ℝ)) A₁ x x') ^ s) :=
    (BstLean.Part130.measurable_normSq.comp
    (measurable_pairMean (m := m) (p := p) (2 / (p : ℝ)) x x')).sqrt.pow_const s
  have hdom : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ,
      nrm (pairMean (p := p) (2 / (p : ℝ)) A₁ x x') ^ s ≤ opN A₁ ^ (2 * s) * nrm x' ^ s := by
    intro A₁
    have h := pow_le_pow_left₀ (nrm_nonneg _) (pairMean_he_coarse_le hp A₁ hx x') s
    simpa only [mul_pow, ← pow_mul] using h
  have hIi := hi.mul_const (nrm x' ^ s)
  have hI := hIi.mono' hm.aestronglyMeasurable (ae_of_all _ fun A₁ => by
    rw [Real.norm_of_nonneg (pow_nonneg (nrm_nonneg _) _)]; exact hdom A₁)
  refine ⟨hI, (integral_mono hI hIi hdom).trans ?_⟩
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right hb (pow_nonneg (nrm_nonneg _) _)

noncomputable def meanError (x x' : Fin n → ℝ)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) : ℝ :=
  nrm ((n : ℝ)⁻¹ • pairMean (p := n ^ 2) (2 / (n ^ 2 : ℕ)) A x x' - pairIdeal x x')

lemma measurable_meanError (x x' : Fin n → ℝ) : Measurable (meanError x x') := by
  apply BstLean.Part130.measurable_normSq.sqrt.comp
  exact ((measurable_pairMean (m := n ^ 2) (p := n ^ 2) (2 / (n ^ 2 : ℕ)) x x').const_smul
    (n : ℝ)⁻¹).sub (measurable_const (a := pairIdeal x x'))

/-- This proved constant is coarse in the first layer; it has no second-layer operator factor. -/
noncomputable def meanErrorMoment (n s : ℕ) : ℝ :=
  2 ^ (s - 1) * ((n : ℝ)⁻¹ ^ s * matrixMoment (n ^ 2) n s (2 / n) + 1)

theorem meanError_moment (hn : 1 ≤ n) {s : ℕ} (hs : 1 ≤ s)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun A => meanError x x' A ^ s) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, meanError x x' A ^ s ∂gaussMat (n ^ 2) n (2 / n)) ≤ meanErrorMoment n s := by
  obtain ⟨hi, hb⟩ := pairMean_he_moment (m := n ^ 2) (p := n ^ 2)
    (by nlinarith) hs (by positivity : 0 ≤ 2 / (n : ℝ)) hx x'
  have hx'n : nrm x' = 1 := by simp [nrm, hx']
  rw [hx'n, one_pow, mul_one] at hb
  obtain ⟨hI, hB⟩ := error_moment_of_moment (measurable_pairMean _ x x') hi
    ((n : ℝ)⁻¹) (pairIdeal x x') hb
  refine ⟨hI, hB.trans ?_⟩
  have hid := pow_le_pow_left₀ (nrm_nonneg _) (pairIdeal_le hx hx') s
  simp only [one_pow] at hid
  rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hid) (by positivity)

/-- The bad set is integrated once under the first-layer distribution. -/
theorem meanError_lowLength (hn : 2 ≤ n) {s : ℕ} (hs : 1 ≤ s)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {η : ℝ} (hη : 2 / (n : ℝ) ^ 2 ≤ η) :
    (∫ A in {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|},
      meanError x x' A ^ s ∂gaussMat (n ^ 2) n (2 / n)) ≤
      sqrt (meanErrorMoment n (2 * s)) *
        sqrt (4 * exp (-(n : ℝ) ^ 2 * (η - 2 / (n : ℝ) ^ 2) ^ 2 / 4)) := by
  have hB : MeasurableSet {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|} :=
    (measurableSet_lt measurable_const ((measurable_layerLength x).sub measurable_const).abs).union
      (measurableSet_lt measurable_const ((measurable_layerLength x').sub measurable_const).abs)
  obtain ⟨hi, hb⟩ := meanError_moment (by omega : 1 ≤ n) (by omega : 1 ≤ 2 * s) hx hx'
  exact restricted_moment_bound (measurable_meanError x x') (fun _ => nrm_nonneg _) hi hB hb
    (pair_lowLength_probability hn hx hx' hη)

end BstLean.Part209
