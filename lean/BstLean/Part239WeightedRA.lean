import BstLean.Part239NodeSupply
import BstLean.Part239NetworkRA

/-! Weighted node moments supply the integrated order104 RA prices. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part213
open BstLean.Part223 (MomentBound)
open BstLean.Part186.RA (ρ2 RR)
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma moment_mul52 {f g : X → ℝ} {A B : ℝ}
    (hf : MomentBound μ 104 f A) (hg : MomentBound μ 104 g B) :
    MomentBound μ 52 (fun x => f x * g x) (A * B) := by
  haveI : ENNReal.HolderTriple (104 : ℝ≥0∞) 104 52 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := (104 : ℝ≥0∞))
    (q := (104 : ℝ≥0∞)) (r := (52 : ℝ≥0∞))
      hf.measurable.aestronglyMeasurable hg.measurable.aestronglyMeasurable
  have hn : eLpNorm (fun x => f x * g x) 52 μ ≤ ENNReal.ofReal (A * B) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hf.nonneg]
    exact mul_le_mul' (BstLean.Part213.moment_norm_bound hf.measurable
      (by norm_num) hf.nonneg hf.moment)
      (BstLean.Part213.moment_norm_bound hg.measurable (by norm_num) hg.nonneg hg.moment)
  have hp := pow_le_pow_left' hn 52
  have he : eLpNorm (fun x => f x * g x) (52 : ℝ≥0∞) μ ^ (52 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 52) ∂μ := by
    exact BstLean.Part153.eLpNorm_nat_pow (μ := μ) (f := fun x => f x * g x)
      (by norm_num : (52 : ℕ) ≠ 0) (hf.measurable.mul hg.measurable).aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow (mul_nonneg hf.nonneg hg.nonneg)] at hp
  exact ⟨hf.measurable.mul hg.measurable, mul_nonneg hf.nonneg hg.nonneg, hp⟩


noncomputable def radiusPolynomialRoot104 (a b c : ℝ) : ℝ :=
  (∫ p, radiusPolynomial a b c p ^ 104 ∂ρ2) ^ (104 : ℝ)⁻¹

lemma radiusPolynomialRoot104_nonneg (a b c : ℝ) :
    0 ≤ radiusPolynomialRoot104 a b c := by
  unfold radiusPolynomialRoot104
  positivity

lemma radiusPolynomialRoot104_pow (a b c : ℝ) :
    radiusPolynomialRoot104 a b c ^ 104 = ∫ p, radiusPolynomial a b c p ^ 104 ∂ρ2 := by
  unfold radiusPolynomialRoot104
  exact Real.rpow_inv_natCast_pow (integral_nonneg fun _ => by positivity) (by norm_num)

theorem collectedSecond_moment {a b c : X → ℝ} {A B C : ℝ}
    (ha : MomentBound μ 104 a A) (hb : MomentBound μ 104 b B)
    (hc : MomentBound μ 104 c C) :
    MomentBound μ 52 (fun x => collectedSecond (a x) (b x) (c x))
      (collectedSecond A B C) := by
  have h0 := ha.power (k := 52) (r := 2)
  have h1 := (moment_mul52 ha hb).scale (by positivity : 0 ≤ 2 * sqrt (π / 2))
  have h2 := ((hb.power (k := 52) (r := 2)).add (by norm_num)
    ((moment_mul52 ha hc).scale (by norm_num : (0 : ℝ) ≤ 2))).scale (by norm_num : (0 : ℝ) ≤ 2)
  have h3 := (moment_mul52 hb hc).scale (by positivity : 0 ≤ 6 * sqrt (π / 2))
  have h4 := (hc.power (k := 52) (r := 2)).scale (by norm_num : (0 : ℝ) ≤ 8)
  have h := (((h0.add (by norm_num) h1).add (by norm_num) h2).add
    (by norm_num) h3).add (by norm_num) h4
  convert h using 1 <;> unfold collectedSecond <;> first | (funext x; ring) | ring

lemma radiusPolynomialRoot104_lintegral (a b c : ℝ) :
    ENNReal.ofReal (radiusPolynomialRoot104 a b c ^ 104) =
      ∫⁻ p, ENNReal.ofReal (|radiusPolynomial a b c p| ^ 104) ∂ρ2 := by
  rw [radiusPolynomialRoot104_pow,
    ofReal_integral_eq_lintegral_ofReal (radius_polynomial_power a b c 104).1
      (Filter.Eventually.of_forall fun _ => by positivity)]
  simp only [Even.pow_abs (by decide : Even 104)]

/-- The exact Gaussian plane norm discharges the source moment premise. -/
theorem radiusPolynomial_source_moment104 (a b c : ℝ) :
    MomentBound ρ2 104 (radiusPolynomial a b c) (radiusPolynomialRoot104 a b c) := by
  refine ⟨?_, radiusPolynomialRoot104_nonneg a b c, ?_⟩
  · unfold radiusPolynomial planeRadius RR
    fun_prop
  · exact le_of_eq (radiusPolynomialRoot104_lintegral a b c).symm

theorem radiusPolynomialRoot104_moment [SFinite μ]
    {a b c : X → ℝ} {A B C : ℝ}
    (ha : MomentBound μ 104 a A) (hb : MomentBound μ 104 b B)
    (hc : MomentBound μ 104 c C) :
    MomentBound μ 104 (fun x => radiusPolynomialRoot104 (a x) (b x) (c x))
      (radiusPolynomialRoot104 A B C) := by
  have ma := ha.measurable
  have mb := hb.measurable
  have mc := hc.measurable
  have hm : Measurable (fun p : X × (ℝ × ℝ) =>
      radiusPolynomial (a p.1) (b p.1) (c p.1) p.2) := by
    unfold radiusPolynomial planeRadius RR
    fun_prop
  have hroot : Measurable (fun x => radiusPolynomialRoot104 (a x) (b x) (c x)) := by
    unfold radiusPolynomialRoot104
    have hi : Measurable (fun x =>
        ∫ p, radiusPolynomial (a x) (b x) (c x) p ^ 104 ∂ρ2) :=
      (hm.pow_const 104).stronglyMeasurable.integral_prod_right'.measurable
    exact hi.pow_const ((104 : ℝ)⁻¹)
  refine ⟨hroot, radiusPolynomialRoot104_nonneg _ _ _, ?_⟩
  have hnode (p : ℝ × ℝ) : MomentBound μ 104
      (fun x => radiusPolynomial (a x) (b x) (c x) p) (radiusPolynomial A B C p) := by
    have h := (ha.add (by norm_num) (hb.scale (sqrt_nonneg (RR p)))).add
      (by norm_num) (hc.scale (sq_nonneg (planeRadius p)))
    convert h using 1 <;> unfold radiusPolynomial planeRadius <;>
      first | (funext x; ring) | ring
  simp only [abs_of_nonneg (radiusPolynomialRoot104_nonneg _ _ _),
    radiusPolynomialRoot104_lintegral]
  rw [lintegral_lintegral_swap (hm.abs.pow_const 104 |>.ennreal_ofReal).aemeasurable]
  exact lintegral_mono fun p => by
    simpa only [Even.pow_abs (by decide : Even 104)] using (hnode p).moment

theorem integrated_location_price [SFinite μ]
    {a b c : X → ℝ} {A B C r N : ℝ}
    (ha : MomentBound μ 104 a A) (hb : MomentBound μ 104 b B)
    (hc : MomentBound μ 104 c C) (hr : 0 ≤ r) (hN : 0 ≤ N) :
    ∫⁻ x, ENNReal.ofReal (N *
      (collectedSecond (a x) (b x) (c x) +
        r * radiusPolynomialRoot104 (a x) (b x) (c x) ^ 2) ^ 52) ∂μ ≤
      ENNReal.ofReal (N *
        (collectedSecond A B C + r * radiusPolynomialRoot104 A B C ^ 2) ^ 52) := by
  have hs := (collectedSecond_moment ha hb hc).add (by norm_num)
    (((radiusPolynomialRoot104_moment ha hb hc).power (k := 52) (r := 2)).scale hr)
  simp_rw [ENNReal.ofReal_mul hN]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl
    (by simpa only [Even.pow_abs (by decide : Even 52)] using hs.moment)

theorem integrated_energy_price [SFinite μ]
    {a b c : X → ℝ} {A B C r N : ℝ}
    (ha : MomentBound μ 104 a A) (hb : MomentBound μ 104 b B)
    (hc : MomentBound μ 104 c C) (hr : 0 ≤ r) (hN : 0 ≤ N) :
    ∫⁻ x, ENNReal.ofReal (N *
      (a x + b x * sqrt (π / 2) + 2 * c x +
        r * radiusPolynomialRoot104 (a x) (b x) (c x)) ^ 104) ∂μ ≤
      ENNReal.ofReal (N *
        (A + B * sqrt (π / 2) + 2 * C + r * radiusPolynomialRoot104 A B C) ^ 104) := by
  have hbase := (ha.add (by norm_num) (hb.scale (sqrt_nonneg (π / 2)))).add
    (by norm_num) (hc.scale (by norm_num : (0 : ℝ) ≤ 2))
  have hs := hbase.add (by norm_num) ((radiusPolynomialRoot104_moment ha hb hc).scale hr)
  have hm : ∫⁻ x, ENNReal.ofReal
      ((a x + b x * sqrt (π / 2) + 2 * c x +
        r * radiusPolynomialRoot104 (a x) (b x) (c x)) ^ 104) ∂μ ≤
      ENNReal.ofReal
        ((A + B * sqrt (π / 2) + 2 * C + r * radiusPolynomialRoot104 A B C) ^ 104) := by
    simpa only [Even.pow_abs (by decide : Even 104), mul_comm (sqrt (π / 2))] using hs.moment
  simp_rw [ENNReal.ofReal_mul hN]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl hm


#print axioms radiusPolynomialRoot104_moment
#print axioms radiusPolynomial_source_moment104
#print axioms integrated_location_price
#print axioms integrated_energy_price
end BstLean.Part239
