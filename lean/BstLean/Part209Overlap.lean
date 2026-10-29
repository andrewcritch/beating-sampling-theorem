import BstLean.Part209Bernstein

/-! The exact overlap mean and its centered scalar Bernstein tail. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)

variable {n m : ℕ}

noncomputable def reluPairRow (x x' w : Fin n → ℝ) : ℝ := relu (dotp w x) * relu (dotp w x')

lemma measurable_reluPairRow (x x' : Fin n → ℝ) : Measurable (reluPairRow x x') :=
  (measurable_relu.comp (measurable_dot_left x)).mul (measurable_relu.comp (measurable_dot_left x'))

lemma reluPairRow_le (x x' w : Fin n → ℝ) :
    |reluPairRow x x' w| ≤ (dotp w x ^ 2 + dotp w x' ^ 2) / 2 := by
  unfold reluPairRow
  rw [abs_mul]
  have h := mul_le_mul (abs_relu_le (dotp w x)) (abs_relu_le (dotp w x'))
    (abs_nonneg _) (abs_nonneg _)
  nlinarith [sq_nonneg (|dotp w x| - |dotp w x'|), sq_abs (dotp w x), sq_abs (dotp w x')]

lemma reluPairRow_scale {v : ℝ} (hv : 0 ≤ v) (x x' w : Fin n → ℝ) :
    reluPairRow x x' (sqrt v • w) = v * reluPairRow x x' w := by
  have hd : ∀ z : Fin n → ℝ, dotp (sqrt v • w) z = sqrt v * dotp w z := by
    intro z
    simp only [dotp, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
  simp only [reluPairRow, hd, relu_mul_of_nonneg (sqrt_nonneg v)]
  have hs := Real.sq_sqrt hv
  calc sqrt v * relu (dotp w x) * (sqrt v * relu (dotp w x')) =
      sqrt v ^ 2 * (relu (dotp w x) * relu (dotp w x')) := by ring
    _ = _ := by rw [hs]

lemma reluPairRow_mean {v : ℝ} (hv : 0 ≤ v) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    (∫ w, reluPairRow x x' (sqrt v • w) ∂stdGauss (Fin n)) = v / 2 * kappa (dotp x x') := by
  have h := row_formula_std x x'
  change 2 * (∫ w, reluPairRow x x' w ∂stdGauss (Fin n)) =
    sqrt (normSq x) * sqrt (normSq x') * kappa (dotp x x' /
      (sqrt (normSq x) * sqrt (normSq x'))) at h
  simp only [hx, hx', sqrt_one, one_mul, div_one] at h
  simp_rw [reluPairRow_scale hv]
  rw [integral_const_mul]
  nlinarith

/-- The overlap uses the same first-layer matrix at both fixed unit inputs. -/
theorem relu_overlap_tail {v : ℝ} (hv : 0 < v) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) (hm : 0 < m)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n v).real {A | 2 * v * (sqrt (2 * (m : ℝ) * τ) + τ) <
      |dotp (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) - (m : ℝ) * v / 2 * kappa (dotp x x')|} ≤
      2 * exp (-τ) := by
  have hdom : ∀ w : Fin n → ℝ, |reluPairRow x x' w| ≤
      v * (((w ⬝ᵥ x) / sqrt v) ^ 2 + ((w ⬝ᵥ x') / sqrt v) ^ 2) / 2 := by
    intro w
    have he : v * (((w ⬝ᵥ x) / sqrt v) ^ 2 + ((w ⬝ᵥ x') / sqrt v) ^ 2) / 2 =
        (dotp w x ^ 2 + dotp w x' ^ 2) / 2 := by
      change v * ((dotp w x / sqrt v) ^ 2 + (dotp w x' / sqrt v) ^ 2) / 2 = _
      rw [div_pow, div_pow, sq_sqrt hv.le]
      field_simp
    rw [he]
    exact reluPairRow_le x x' w
  have h := BstLean.Part182.s2_dev hv (measurable_reluPairRow x x') hx hx' hv hdom hm hτ
  rw [reluPairRow_mean hv.le hx hx'] at h
  have he : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      (∑ j, reluPairRow x x' (rowOf j A)) = dotp (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) := by
    intro A
    rfl
  simp_rw [he] at h
  convert h using 2
  ext A
  congr 2
  ring

noncomputable def firstOverlap (x x' : Fin n → ℝ)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) : ℝ :=
  dotp (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) / (n : ℝ)

/-- The normalized overlap has exactly the single-layer ReLU kernel mean. -/
theorem firstOverlap_mean (hn : 1 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (firstOverlap x x') (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, firstOverlap x x' A ∂gaussMat (n ^ 2) n (2 / n)) = kappa (dotp x x') := by
  obtain ⟨hi, he⟩ := layer_dot_relu (m := n ^ 2) (by positivity : 0 ≤ 2 / (n : ℝ)) x x'
  refine ⟨hi.div_const _, ?_⟩
  unfold firstOverlap
  rw [integral_div, he]
  simp only [kernelPhi, hx, hx', sqrt_one, one_mul, div_one, Nat.cast_pow]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

end BstLean.Part209
