import BstLean.Part199TI
import BstLean.Part182Schur

/-! Part 208: integrated mode bounds. All four integrals use one measure. -/
namespace BstLean.Part208
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part182
open BstLean.Part153 (nrm nrm_sq abs_dot_le_nrm)

/-- A tangent vector has a smaller component in the retained centre direction. -/
theorem tangent_centre_sq {n : ℕ} {u x f : Fin n → ℝ}
    (hu : normSq u = 1) (hx : normSq x = 1) (hf : x ⬝ᵥ f = 0) :
    (u ⬝ᵥ f) ^ 2 ≤ (1 - (u ⬝ᵥ x) ^ 2) * normSq f := by
  let v := u - (u ⬝ᵥ x) • x
  have hdot : v ⬝ᵥ f = u ⬝ᵥ f := by
    simp [v, sub_dotProduct, smul_dotProduct, hf]
  have hnorm : normSq v = 1 - (u ⬝ᵥ x) ^ 2 := by
    rw [← ms_dot_self]
    dsimp [v]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, ms_dot_self, hu, hx, dotProduct_comm x u]
    ring
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_dot_le_nrm v f) 2
  rw [sq_abs, mul_pow, nrm_sq, nrm_sq, hdot, hnorm] at h
  exact h

/-- Apply the overlap denominator only on the restricted pair set. -/
theorem tangent_pair_sq {n : ℕ} {x x' f : Fin n → ℝ} {cp : ℝ}
    (hf : x ⬝ᵥ f = 0) (hcp : cp ^ 2 < 1)
    (hc : (x ⬝ᵥ x') ^ 2 ≤ cp ^ 2) :
    (eTan x x' ⬝ᵥ f) ^ 2 ≤ (x' ⬝ᵥ f) ^ 2 / (1 - cp ^ 2) := by
  have hd : 0 < 1 - (x ⬝ᵥ x') ^ 2 := by linarith
  unfold eTan
  rw [smul_dotProduct, sub_dotProduct, smul_dotProduct, hf]
  simp only [mul_zero, sub_zero, smul_eq_mul, mul_pow, inv_pow, sq_sqrt hd.le]
  rw [← div_eq_inv_mul]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)

section Integral
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Cauchy--Schwarz in a form that accepts explicit square-integrability evidence. -/
theorem integral_product_le (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun x => f x ^ 2) μ) (hgi : Integrable (fun x => g x ^ 2) μ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ∫ x, f x ^ 2 ∂μ ≤ A) (hgb : ∫ x, g x ^ 2 ∂μ ≤ B) :
    ∫ x, f x * g x ∂μ ≤ √(A * B) := by
  have hfg : Integrable (fun x => f x * g x) μ := by
    refine Integrable.mono' ((hfi.add hgi).div_const 2) (hf.mul hg).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  apply le_sqrt_of_forall_pos hA hB
  intro s hs
  have hpt : ∀ x, f x * g x ≤ (s * f x ^ 2 + g x ^ 2 / s) / 2 := by
    intro x
    have h := sq_nonneg (s * f x - g x)
    have hs0 : s ≠ 0 := hs.ne'
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (mul_le_mul_iff_of_pos_right hs).mp
    field_simp
    nlinarith
  have h := integral_mono hfg (((hfi.const_mul s).add (hgi.div_const s)).div_const 2) hpt
  simp only [Pi.add_apply] at h
  rw [integral_div, integral_add (hfi.const_mul s) (hgi.div_const s),
    integral_const_mul, integral_div] at h
  exact h.trans (div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hfa hs.le)
      (div_le_div_of_nonneg_right hgb hs.le)) (by norm_num))

/-- The tangential gain follows after integration of the four pair modes.
`a,b` are full-vector factors; `c,d` are tangent-component factors.
The measure can already contain the restriction to good core pairs. -/
theorem integrated_four_modes (a b c d : X → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    (hai : Integrable (fun x => a x ^ 2) μ) (hbi : Integrable (fun x => b x ^ 2) μ)
    (hci : Integrable (fun x => c x ^ 2) μ) (hdi : Integrable (fun x => d x ^ 2) μ)
    {E χ kE ko ks : ℝ} (hE : 0 ≤ E) (hχ : 0 ≤ χ)
    (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (haE : ∫ x, a x ^ 2 ∂μ ≤ E) (hbE : ∫ x, b x ^ 2 ∂μ ≤ E)
    (hcE : ∫ x, c x ^ 2 ∂μ ≤ E * χ) (hdE : ∫ x, d x ^ 2 ∂μ ≤ E * χ) :
    kE * (∫ x, a x * b x ∂μ) +
      ko * ((∫ x, c x * b x ∂μ) + ∫ x, a x * d x ∂μ) +
      ks * (∫ x, c x * d x ∂μ) ≤ E * (kE + 2 * ko * √χ + ks * χ) := by
  have hab := integral_product_le μ a b ha hb hai hbi hE hE haE hbE
  have hcb := integral_product_le μ c b hc hb hci hbi (mul_nonneg hE hχ) hE hcE hbE
  have had := integral_product_le μ a d ha hd hai hdi hE (mul_nonneg hE hχ) haE hdE
  have hcd := integral_product_le μ c d hc hd hci hdi
    (mul_nonneg hE hχ) (mul_nonneg hE hχ) hcE hdE
  have h1 : √(E * E) = E := by rw [← sq, sqrt_sq hE]
  have h2 : √(E * χ * E) = E * √χ := by
    rw [show E * χ * E = E ^ 2 * χ by ring, sqrt_mul (sq_nonneg E), sqrt_sq hE]
  have h3 : √(E * (E * χ)) = E * √χ := by
    rw [show E * (E * χ) = E * χ * E by ring, h2]
  have h4 : √(E * χ * (E * χ)) = E * χ := by
    rw [← sq, sqrt_sq (mul_nonneg hE hχ)]
  rw [h1] at hab
  rw [h2] at hcb
  rw [h3] at had
  rw [h4] at hcd
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hab hkE)
    (mul_le_mul_of_nonneg_left (add_le_add hcb had) hko))
      (mul_le_mul_of_nonneg_left hcd hks)
  convert h using 1 <;> ring

end Integral
end BstLean.Part208
