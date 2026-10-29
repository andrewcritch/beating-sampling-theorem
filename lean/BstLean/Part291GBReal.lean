import BstLean.Part291GB
import BstLean.Part291Cap

namespace BstLean.BlueprintLow
open MeasureTheory Real
open scoped ENNReal

theorem gb_moment_bound_real {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (V Z ω g : X → ℝ)
    (hV : Measurable V) (hZ : Measurable Z) (hω : Measurable ω) (hg : Measurable g)
    (hV0 : ∀ x, 0 ≤ V x) (hZ0 : ∀ x, 0 ≤ Z x)
    (hω0 : ∀ x, 0 ≤ ω x) (hg0 : ∀ x, 0 ≤ g x)
    {K F L E G : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F) (hL0 : 0 ≤ L)
    (hE0 : 0 ≤ E) (hG0 : 0 ≤ G)
    (hVω : ∀ x, V x ≤ K * ω x) (hZg : ∀ x, Z x ≤ F * g x)
    (hiV : Integrable V μ) (hiω : Integrable (fun x => ω x ^ 16) μ)
    (hig : Integrable (fun x => g x ^ 12) μ)
    (hL : (∫ x, V x ∂μ) ≤ L) (hE : (∫ x, ω x ^ 16 ∂μ) ≤ E)
    (hG : (∫ x, g x ^ 12 ∂μ) ≤ G) :
    (∫ x, V x * Z x ∂μ) ≤
      L ^ (41 / 45 : ℝ) *
        (K * F ^ (45 / 4 : ℝ) *
          (E ^ (1 / 16 : ℝ) * G ^ (15 / 16 : ℝ))) ^ (4 / 45 : ℝ) := by
  have hLv : (∫⁻ x, ENNReal.ofReal (V x) ∂μ) ≤ ENNReal.ofReal L := by
    rw [← ofReal_integral_eq_lintegral_ofReal hiV (ae_of_all _ hV0)]
    exact ENNReal.ofReal_le_ofReal hL
  have hEv : (∫⁻ x, ENNReal.ofReal (ω x) ^ 16 ∂μ) ≤ ENNReal.ofReal E := by
    simp_rw [← ENNReal.ofReal_pow (hω0 _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hiω (ae_of_all _ fun x => pow_nonneg (hω0 x) 16)]
    exact ENNReal.ofReal_le_ofReal hE
  have hGv : (∫⁻ x, ENNReal.ofReal (g x) ^ 12 ∂μ) ≤ ENNReal.ofReal G := by
    simp_rw [← ENNReal.ofReal_pow (hg0 _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hig (ae_of_all _ fun x => pow_nonneg (hg0 x) 12)]
    exact ENNReal.ofReal_le_ofReal hG
  have h := gb_moment_bound μ (fun x => ENNReal.ofReal (V x))
    (fun x => ENNReal.ofReal (Z x)) (fun x => ENNReal.ofReal (ω x))
    (fun x => ENNReal.ofReal (g x)) hV.ennreal_ofReal hZ.ennreal_ofReal
    hω.ennreal_ofReal hg.ennreal_ofReal
    (K := ENNReal.ofReal K) (F := ENNReal.ofReal F)
    (fun x => by rw [← ENNReal.ofReal_mul hK]; exact ENNReal.ofReal_le_ofReal (hVω x))
    (fun x => by rw [← ENNReal.ofReal_mul hF]; exact ENNReal.ofReal_le_ofReal (hZg x))
    hLv hEv hGv
  have hfin : ENNReal.ofReal L ^ (41 / 45 : ℝ) *
      (ENNReal.ofReal K * ENNReal.ofReal F ^ (45 / 4 : ℝ) *
        (ENNReal.ofReal E ^ (1 / 16 : ℝ) * ENNReal.ofReal G ^ (15 / 16 : ℝ))) ^ (4 / 45 : ℝ) ≠ ∞ := by
    finiteness
  have ht := ENNReal.toReal_mono hfin h
  simp_rw [← ENNReal.ofReal_mul (hV0 _)] at ht
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => mul_nonneg (hV0 x) (hZ0 x)) (hV.mul hZ).aestronglyMeasurable] at ht
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hK, ENNReal.toReal_ofReal hF, ENNReal.toReal_ofReal hL0,
    ENNReal.toReal_ofReal hE0, ENNReal.toReal_ofReal hG0] using ht

end BstLean.BlueprintLow
