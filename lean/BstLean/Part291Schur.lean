import BstLean.Part208SchurIntegrated
import BstLean.Part208PairRows
import BstLean.Part188Rows
import BstLean.Part291RW

/-! The integrated WS estimate keeps the dependent weight in both pair factors.
The row coefficients W and T are separate; neither assumes a rotation-invariant
weighted law. The network pair-event and row estimates must still be supplied. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part182 BstLean.Part208
open BstLean.Part153 (nrm nrm_nonneg nrm_sq)

theorem ws_four_modes {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b c d : X → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    (hai : Integrable (fun x => a x ^ 2) μ) (hbi : Integrable (fun x => b x ^ 2) μ)
    (hci : Integrable (fun x => c x ^ 2) μ) (hdi : Integrable (fun x => d x ^ 2) μ)
    {W T Q kE ko ks : ℝ} (hW : 0 ≤ W) (hT : 0 ≤ T) (hQ : 0 ≤ Q)
    (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (haW : ∫ x, a x ^ 2 ∂μ ≤ W * Q) (hbW : ∫ x, b x ^ 2 ∂μ ≤ W * Q)
    (hcT : ∫ x, c x ^ 2 ∂μ ≤ T * Q) (hdT : ∫ x, d x ^ 2 ∂μ ≤ T * Q) :
    kE * (∫ x, a x * b x ∂μ) +
      ko * ((∫ x, c x * b x ∂μ) + ∫ x, a x * d x ∂μ) +
      ks * (∫ x, c x * d x ∂μ) ≤ (kE * W + 2 * ko * √(W * T) + ks * T) * Q := by
  have hab := integral_product_le μ a b ha hb hai hbi
    (mul_nonneg hW hQ) (mul_nonneg hW hQ) haW hbW
  have hcb := integral_product_le μ c b hc hb hci hbi
    (mul_nonneg hT hQ) (mul_nonneg hW hQ) hcT hbW
  have had := integral_product_le μ a d ha hd hai hdi
    (mul_nonneg hW hQ) (mul_nonneg hT hQ) haW hdT
  have hcd := integral_product_le μ c d hc hd hci hdi
    (mul_nonneg hT hQ) (mul_nonneg hT hQ) hcT hdT
  have e1 : √(W * Q * (W * Q)) = W * Q := sqrt_mul_self (mul_nonneg hW hQ)
  have e2 : √(T * Q * (T * Q)) = T * Q := sqrt_mul_self (mul_nonneg hT hQ)
  have e3 : √(W * Q * (T * Q)) = √(W * T) * Q := by
    rw [show W * Q * (T * Q) = (W * T) * Q ^ 2 by ring,
      sqrt_mul (mul_nonneg hW hT), sqrt_sq hQ]
  have e4 : √(T * Q * (W * Q)) = √(W * T) * Q := by
    rw [mul_comm (T * Q) (W * Q), e3]
  rw [e1] at hab
  rw [e2] at hcd
  rw [e3] at had
  rw [e4] at hcb
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hab hkE)
    (mul_le_mul_of_nonneg_left (add_le_add hcb had) hko))
    (mul_le_mul_of_nonneg_left hcd hks)
  convert h using 1 <;> ring

theorem ws_modes_of_rows {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (a c : X × X → ℝ) (F : X → ℝ)
    (ha : Measurable a) (hc : Measurable c)
    (hai : Integrable (fun p => a p ^ 2) (μ.prod μ))
    (hci : Integrable (fun p => c p ^ 2) (μ.prod μ))
    (hFi : Integrable F μ) (hF : ∀ x, 0 ≤ F x)
    {W T kE ko ks : ℝ} (hW : 0 ≤ W) (hT : 0 ≤ T)
    (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hrowA : ∀ x, ∫ y, a (x, y) ^ 2 ∂μ ≤ W * F x)
    (hrowC : ∀ x, ∫ y, c (x, y) ^ 2 ∂μ ≤ T * F x) :
    kE * (∫ p, a p * a p.swap ∂μ.prod μ) +
      ko * ((∫ p, c p * a p.swap ∂μ.prod μ) + ∫ p, a p * c p.swap ∂μ.prod μ) +
      ks * (∫ p, c p * c p.swap ∂μ.prod μ) ≤
      (kE * W + 2 * ko * √(W * T) + ks * T) * ∫ x, F x ∂μ := by
  have hA : (∫ p, a p ^ 2 ∂μ.prod μ) ≤ W * ∫ x, F x ∂μ := by
    rw [integral_prod _ hai, ← integral_const_mul]
    exact integral_mono hai.integral_prod_left (hFi.const_mul W) hrowA
  have hC : (∫ p, c p ^ 2 ∂μ.prod μ) ≤ T * ∫ x, F x ∂μ := by
    rw [integral_prod _ hci, ← integral_const_mul]
    exact integral_mono hci.integral_prod_left (hFi.const_mul T) hrowC
  apply ws_four_modes (μ.prod μ) a (fun p => a p.swap) c (fun p => c p.swap)
    ha (ha.comp measurable_swap) hc (hc.comp measurable_swap)
    hai hai.swap hci hci.swap hW hT (integral_nonneg hF) hkE hko hks hA
  · rw [integral_prod_swap (fun p => a p ^ 2)]; exact hA
  · exact hC
  · rw [integral_prod_swap (fun p => c p ^ 2)]; exact hC

/-- Schur with an integrated core coefficient and a bounded dependent density.
The exceptional contribution pays exactly the inverse cutoff, after the square
root. The same good-pair set is used for all choices of the density. -/
theorem ws_dependent_integrated {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {m k : ℕ}
    (B : X → Matrix (Fin m) (Fin k) ℝ) (hB : ∀ i j, Measurable (fun x => B x i j))
    (β : X → ℝ) (hβm : Measurable β) (hβ : ∀ x, opN (B x) ≤ β x) {CB : ℝ}
    (hCB : ∀ x, β x ≤ CB)
    (w q : X → ℝ) (hwm : Measurable w) (hqm : Measurable q)
    (hw0 : ∀ x, 0 ≤ w x) (hq0 : ∀ x, 0 ≤ q x)
    (hwi : Integrable w μ) (hw2 : Integrable (fun x => w x ^ 2) μ)
    {d : ℝ} (hd : 0 < d) (hqd : ∀ x, q x ≤ 1 / d)
    (S : Set X) (hS : MeasurableSet S) (hwS : ∀ x, x ∉ S → w x = 0)
    (G : Set (X × X)) (hG : MeasurableSet G) {R : ℝ} (hR : 0 ≤ R)
    (hgood : ∀ v : Fin m → ℝ,
      (∫ p in G, (w p.1 * q p.1) * (w p.2 * q p.2) *
        ((B p.1 *ᵥ vecMul v (B p.1)) ⬝ᵥ (B p.2 *ᵥ vecMul v (B p.2))) ∂μ.prod μ) ≤
        R * ∫ x, (w x * q x) * normSq (vecMul v (B x)) ∂μ)
    (hi4 : Integrable (fun x => w x ^ 2 * β x ^ 4) μ) (v : Fin m → ℝ) :
    ∫ x, w x * q x * normSq (vecMul v (B x)) ∂μ ≤
      (R + √(√((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) *
        ∫ x, w x ^ 2 * β x ^ 4 ∂μ) / d) * normSq v := by
  have hi : Integrable (fun x => w x * q x) μ := by
    refine Integrable.mono' (hwi.mul_const (1 / d)) (hwm.mul hqm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (hq0 x))]
    exact mul_le_mul_of_nonneg_left (hqd x) (hw0 x)
  have hi2 : Integrable (fun x => (w x * q x) ^ 2) μ := by
    refine Integrable.mono' (hw2.mul_const ((1 / d) ^ 2))
      ((hwm.mul hqm).pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hq0 x) (hqd x) 2) (sq_nonneg _)
  have h := schur_integrated μ B hB β hβm hβ hCB (fun x => w x * q x)
    (hwm.mul hqm) (fun x => mul_nonneg (hw0 x) (hq0 x)) hi hi2 S hS
    (fun x hx => by rw [hwS x hx, zero_mul]) G hG hR hgood v
  have he := BstLean.Part188.weighted_exceptional_moment μ w q β hwm hqm hβm hd hq0 hqd hi4
  have hroot := sqrt_le_sqrt (mul_le_mul_of_nonneg_left he
    (sqrt_nonneg ((μ.prod μ).real (Gᶜ ∩ S ×ˢ S))))
  have eqroot : √(√((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) *
      ((1 / d) ^ 2 * ∫ x, w x ^ 2 * β x ^ 4 ∂μ)) =
      √(√((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) * ∫ x, w x ^ 2 * β x ^ 4 ∂μ) / d := by
    rw [show √((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) *
        ((1 / d) ^ 2 * ∫ x, w x ^ 2 * β x ^ 4 ∂μ) =
        (1 / d) ^ 2 * (√((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) *
          ∫ x, w x ^ 2 * β x ^ 4 ∂μ) by ring,
      sqrt_mul (sq_nonneg _), sqrt_sq (by positivity)]
    ring
  rw [eqroot] at hroot
  exact h.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hroot) (normSq_nonneg v))

end BstLean.BlueprintLow
