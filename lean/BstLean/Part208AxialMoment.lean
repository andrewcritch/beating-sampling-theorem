import BstLean.Part208AxialGeometry

/-! Part 208: weighted second moments of the actual shifted Gaussian direction. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (radF53 unitF53 measurable_radF)

/-- At a fixed longitudinal coordinate, integrate the actual transverse Gaussian. -/
theorem axial_second {d : ℕ} (hd : 1 ≤ d) (a τ p : ℝ) (v : Fin d → ℝ)
    (q : ℝ → ℝ) (hq : Measurable q)
    (hqi : Integrable (fun z : Fin d → ℝ => q (radF53 z)) (stdGauss (Fin d))) :
    (∫ G, q (radF53 G) * (unitF53 (Fin.cons a (τ • G)) ⬝ᵥ Fin.cons p v) ^ 2
      ∂stdGauss (Fin d)) =
      p ^ 2 * (∫ G, q (radF53 G) * axialLong a τ (radF53 G) ^ 2 ∂stdGauss (Fin d)) +
      normSq v / d * ∫ G, q (radF53 G) * axialTrans a τ (radF53 G) ^ 2
        ∂stdGauss (Fin d) := by
  have ha : Measurable (fun r => axialLong a τ r * p) := by
    unfold axialLong axialDen; fun_prop
  have hb : Measurable (axialTrans a τ) := by
    unfold axialTrans axialDen; fun_prop
  have ha1 : ∀ r, |axialLong a τ r * p| ≤ |p| := by
    intro r
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right (axialLong_abs_le a τ r) (abs_nonneg p)
  simp_rw [unit_cons_dot]
  rw [radial_second_bounded hd v q (fun r => axialLong a τ r * p)
    (axialTrans a τ) hq ha hb hqi ha1 (axialTrans_abs_le a τ)]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext G
  ring

/-- A radial input weight preserves the latitude gain. No Agent event is averaged here. -/
theorem axial_second_le {d : ℕ} (hd : 1 ≤ d) (a τ p : ℝ) (v : Fin d → ℝ)
    (q : ℝ → ℝ) (hq : Measurable q)
    (hqi : Integrable (fun z : Fin d → ℝ => q (radF53 z)) (stdGauss (Fin d)))
    (hq0 : ∀ r, 0 ≤ q r) {sp : ℝ}
    (hsp : ∀ r, q r * axialLong a τ r ^ 2 ≤ sp * q r) :
    (∫ G, q (radF53 G) * (unitF53 (Fin.cons a (τ • G)) ⬝ᵥ Fin.cons p v) ^ 2
      ∂stdGauss (Fin d)) ≤
      (sp * p ^ 2 + normSq v / d) * ∫ G, q (radF53 G) ∂stdGauss (Fin d) := by
  have ha : Measurable (fun r => axialLong a τ r ^ 2) := by
    unfold axialLong axialDen; fun_prop
  have hb : Measurable (fun r => axialTrans a τ r ^ 2) := by
    unfold axialTrans axialDen; fun_prop
  have ha1 : ∀ r, ‖axialLong a τ r ^ 2‖ ≤ (1 : ℝ) := by
    intro r
    rw [Real.norm_eq_abs, abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) (axialLong_abs_le a τ r) 2
    simpa using h
  have hb1 : ∀ r, ‖axialTrans a τ r ^ 2‖ ≤ (1 : ℝ) := by
    intro r
    rw [Real.norm_eq_abs, abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) (axialTrans_abs_le a τ r) 2
    simpa using h
  have hai := hqi.mul_bdd (ha.comp measurable_radF).aestronglyMeasurable
    (ae_of_all _ fun G => ha1 (radF53 G))
  have hbi := hqi.mul_bdd (hb.comp measurable_radF).aestronglyMeasurable
    (ae_of_all _ fun G => hb1 (radF53 G))
  have h1 := integral_mono hai (hqi.const_mul sp) (fun G => hsp (radF53 G))
  dsimp only [Function.comp_apply] at h1
  rw [integral_const_mul] at h1
  have h2 : (∫ G, q (radF53 G) * axialTrans a τ (radF53 G) ^ 2 ∂stdGauss (Fin d)) ≤
      ∫ G, q (radF53 G) ∂stdGauss (Fin d) := by
    apply integral_mono hbi hqi
    intro G
    have h := hb1 (radF53 G)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    simpa using mul_le_mul_of_nonneg_left h (hq0 _)
  rw [axial_second hd a τ p v q hq hqi]
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 (sq_nonneg p))
    (mul_le_mul_of_nonneg_left h2 (div_nonneg (normSq_nonneg v) (Nat.cast_nonneg d)))
  convert h using 1 <;> ring

end BstLean.Part208
