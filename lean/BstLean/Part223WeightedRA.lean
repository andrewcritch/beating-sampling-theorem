import BstLean.Part223WeightedStatistics
import BstLean.Part223ScalarRA

/-! Integrated row coefficients give deterministic RA prices. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part213
open BstLean.Part186.RA (ρ2 RR)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem collectedSecond_moment {a b c : X → ℝ} {A B C : ℝ}
    (ha : MomentBound μ 16 a A) (hb : MomentBound μ 16 b B)
    (hc : MomentBound μ 16 c C) :
    MomentBound μ 8 (fun x => collectedSecond (a x) (b x) (c x))
      (collectedSecond A B C) := by
  have h0 := ha.power (k := 8) (r := 2)
  have h1 := (ha.mul8 hb).scale (by positivity : 0 ≤ 2 * sqrt (π / 2))
  have h2 := ((hb.power (k := 8) (r := 2)).add (by norm_num)
    ((ha.mul8 hc).scale (by norm_num : (0 : ℝ) ≤ 2))).scale (by norm_num : (0 : ℝ) ≤ 2)
  have h3 := (hb.mul8 hc).scale (by positivity : 0 ≤ 6 * sqrt (π / 2))
  have h4 := (hc.power (k := 8) (r := 2)).scale (by norm_num : (0 : ℝ) ≤ 8)
  have h := (((h0.add (by norm_num) h1).add (by norm_num) h2).add
    (by norm_num) h3).add (by norm_num) h4
  convert h using 1 <;> unfold collectedSecond <;> first | (funext x; ring) | ring

lemma radiusPolynomialRoot16_lintegral (a b c : ℝ) :
    ENNReal.ofReal (radiusPolynomialRoot16 a b c ^ 16) =
      ∫⁻ p, ENNReal.ofReal (|radiusPolynomial a b c p| ^ 16) ∂ρ2 := by
  rw [radiusPolynomialRoot16_pow,
    ofReal_integral_eq_lintegral_ofReal (radius_polynomial_power a b c 16).1
      (Filter.Eventually.of_forall fun _ => by positivity)]
  simp only [Even.pow_abs (by decide : Even 16)]

theorem radiusPolynomialRoot16_moment [SFinite μ]
    {a b c : X → ℝ} {A B C : ℝ}
    (ha : MomentBound μ 16 a A) (hb : MomentBound μ 16 b B)
    (hc : MomentBound μ 16 c C) :
    MomentBound μ 16 (fun x => radiusPolynomialRoot16 (a x) (b x) (c x))
      (radiusPolynomialRoot16 A B C) := by
  have ma := ha.measurable
  have mb := hb.measurable
  have mc := hc.measurable
  have hm : Measurable (fun p : X × (ℝ × ℝ) =>
      radiusPolynomial (a p.1) (b p.1) (c p.1) p.2) := by
    unfold radiusPolynomial planeRadius RR
    fun_prop
  have hroot : Measurable (fun x => radiusPolynomialRoot16 (a x) (b x) (c x)) := by
    have he : (fun x => radiusPolynomialRoot16 (a x) (b x) (c x)) =
        fun x => (∫ p, radiusPolynomial (a x) (b x) (c x) p ^ 16 ∂ρ2) ^ ((16 : ℝ)⁻¹) := by
      funext x
      rw [radiusPolynomialRoot16, radiusPolynomialMoment16_eq]
    rw [he]
    have hi : Measurable (fun x =>
        ∫ p, radiusPolynomial (a x) (b x) (c x) p ^ 16 ∂ρ2) :=
      (hm.pow_const 16).stronglyMeasurable.integral_prod_right'.measurable
    exact hi.pow_const ((16 : ℝ)⁻¹)
  refine ⟨hroot, radiusPolynomialRoot16_nonneg _ _ _, ?_⟩
  have hnode (p : ℝ × ℝ) : MomentBound μ 16
      (fun x => radiusPolynomial (a x) (b x) (c x) p) (radiusPolynomial A B C p) := by
    have h := (ha.add (by norm_num) (hb.scale (sqrt_nonneg (RR p)))).add
      (by norm_num) (hc.scale (sq_nonneg (planeRadius p)))
    convert h using 1 <;> unfold radiusPolynomial planeRadius <;>
      first | (funext x; ring) | ring
  simp only [abs_of_nonneg (radiusPolynomialRoot16_nonneg _ _ _),
    radiusPolynomialRoot16_lintegral]
  rw [lintegral_lintegral_swap (hm.abs.pow_const 16 |>.ennreal_ofReal).aemeasurable]
  exact lintegral_mono fun p => by
    simpa only [Even.pow_abs (by decide : Even 16)] using (hnode p).moment

theorem integrated_location_price [SFinite μ]
    {a b c : X → ℝ} {A B C r N : ℝ}
    (ha : MomentBound μ 16 a A) (hb : MomentBound μ 16 b B)
    (hc : MomentBound μ 16 c C) (hr : 0 ≤ r) (hN : 0 ≤ N) :
    ∫⁻ x, ENNReal.ofReal (N *
      (collectedSecond (a x) (b x) (c x) +
        r * radiusPolynomialRoot16 (a x) (b x) (c x) ^ 2) ^ 8) ∂μ ≤
      ENNReal.ofReal (N *
        (collectedSecond A B C + r * radiusPolynomialRoot16 A B C ^ 2) ^ 8) := by
  have hs := (collectedSecond_moment ha hb hc).add (by norm_num)
    (((radiusPolynomialRoot16_moment ha hb hc).power (k := 8) (r := 2)).scale hr)
  simp_rw [ENNReal.ofReal_mul hN]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl
    (by simpa only [Even.pow_abs (by decide : Even 8)] using hs.moment)

theorem integrated_energy_price [SFinite μ]
    {a b c : X → ℝ} {A B C r N : ℝ}
    (ha : MomentBound μ 16 a A) (hb : MomentBound μ 16 b B)
    (hc : MomentBound μ 16 c C) (hr : 0 ≤ r) (hN : 0 ≤ N) :
    ∫⁻ x, ENNReal.ofReal (N *
      (a x + b x * sqrt (π / 2) + 2 * c x +
        r * radiusPolynomialRoot16 (a x) (b x) (c x)) ^ 16) ∂μ ≤
      ENNReal.ofReal (N *
        (A + B * sqrt (π / 2) + 2 * C + r * radiusPolynomialRoot16 A B C) ^ 16) := by
  have hbase := (ha.add (by norm_num) (hb.scale (sqrt_nonneg (π / 2)))).add
    (by norm_num) (hc.scale (by norm_num : (0 : ℝ) ≤ 2))
  have hs := hbase.add (by norm_num) ((radiusPolynomialRoot16_moment ha hb hc).scale hr)
  have hm : ∫⁻ x, ENNReal.ofReal
      ((a x + b x * sqrt (π / 2) + 2 * c x +
        r * radiusPolynomialRoot16 (a x) (b x) (c x)) ^ 16) ∂μ ≤
      ENNReal.ofReal
        ((A + B * sqrt (π / 2) + 2 * C + r * radiusPolynomialRoot16 A B C) ^ 16) := by
    simpa only [Even.pow_abs (by decide : Even 16), mul_comm (sqrt (π / 2))] using hs.moment
  simp_rw [ENNReal.ofReal_mul hN]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl hm

#print axioms collectedSecond_moment
#print axioms radiusPolynomialRoot16_moment
#print axioms integrated_location_price
#print axioms integrated_energy_price
end BstLean.Part223
