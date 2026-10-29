import BstLean.Part71Defs
import BstLean.Part56PropD_Polar
import BstLean.Part29Gauss

/-! Part 71, Theorem QT1, sphere-to-Gaussian comparison:
`E_σ exp(2 xᵀBx) ≤ E_γ exp(2 gᵀBg / n)`. -/

namespace BstLean.Part71

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part53 (unitF53 radF53)

theorem continuous_qf {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Continuous (qf B) := by
  unfold qf; fun_prop

theorem qf_smul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    qf B (c • x) = c ^ 2 * qf B x := by
  unfold qf
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem qf_unit_rad {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) :
    qf B (unitF53 g) * radF53 g ^ 2 = qf B g := by
  unfold unitF53 radF53
  set S := ∑ i, g i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (g i))
  rw [qf_smul, Real.sq_sqrt hS0, div_pow, Real.sq_sqrt hS0]
  rcases eq_or_lt_of_le hS0 with h | h
  · have hg : g = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i))).mp h.symm i
        (Finset.mem_univ i)
      simpa using this
    subst hg
    simp [qf]
  · field_simp

/-- The tangent-line bound: `e^c ≤ E_γ exp(c ‖g‖²/n)`. -/
theorem tangent_bound (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    ENNReal.ofReal (Real.exp c) ≤
      ∫⁻ g, ENNReal.ofReal (Real.exp (c * radF53 g ^ 2 / n)) ∂stdGauss (Fin n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : BstLean.Part29.GaussMoments n (stdGauss (Fin n)) := BstLean.Part29.gaussMoments_std
  let L : (Fin n → ℝ) → ℝ := fun g =>
    Real.exp c * (1 - c) + Real.exp c * c / n * ∑ i, g i * g i
  have hLint : Integrable L (stdGauss (Fin n)) := by
    refine (integrable_const _).add ((integrable_finsetSum _ (fun i _ => hG.int2 i i)).const_mul _)
  have hLval : ∫ g, L g ∂stdGauss (Fin n) = Real.exp c := by
    simp only [L]
    rw [integral_add (integrable_const _)
      ((integrable_finsetSum _ (fun i _ => hG.int2 i i)).const_mul _),
      integral_const, integral_const_mul, integral_finsetSum _ (fun i _ => hG.int2 i i)]
    have hm : ∀ i, ∫ g, g i * g i ∂stdGauss (Fin n) = 1 := by
      intro i; have := hG.m2 i i; simpa using this
    simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  calc ENNReal.ofReal (Real.exp c) = ENNReal.ofReal (∫ g, L g ∂stdGauss (Fin n)) := by rw [hLval]
    _ ≤ ENNReal.ofReal (∫ g, max (L g) 0 ∂stdGauss (Fin n)) :=
        ENNReal.ofReal_le_ofReal (integral_mono hLint hLint.pos_part (fun g => le_max_left _ _))
    _ = ∫⁻ g, ENNReal.ofReal (max (L g) 0) ∂stdGauss (Fin n) :=
        ofReal_integral_eq_lintegral_ofReal hLint.pos_part (ae_of_all _ (fun g => le_max_right _ _))
    _ = ∫⁻ g, ENNReal.ofReal (L g) ∂stdGauss (Fin n) := by
        refine lintegral_congr (fun g => ?_)
        rcases le_total (L g) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]
    _ ≤ _ := by
        refine lintegral_mono (fun g => ENNReal.ofReal_le_ofReal ?_)
        have hr : radF53 g ^ 2 = ∑ i, g i * g i := by
          unfold radF53
          rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (g i)))]
          simp only [pow_two]
        rw [hr]
        set s := ∑ i, g i * g i
        have he := Real.add_one_le_exp (c * (s / n - 1))
        have hsplit : Real.exp (c * s / n) = Real.exp c * Real.exp (c * (s / n - 1)) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
        rw [hsplit]
        have hec := Real.exp_pos c
        have : L g = Real.exp c * (c * (s / n - 1) + 1) := by
          simp only [L, s]; field_simp; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left he hec.le

/-- Sphere-to-Gaussian comparison. -/
theorem sphere_le_gauss (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (2 * qf B x)) ∂uniformSphere n ≤
      ∫⁻ g, ENNReal.ofReal (Real.exp (2 * qf B g / n)) ∂stdGauss (Fin n) := by
  have hq := continuous_qf B
  rw [BstLean.Part56.uniformSphere_lintegral_gauss n hn
    (fun x => ENNReal.ofReal (Real.exp (2 * qf B x))) (by fun_prop)]
  let F : (Fin n → ℝ) → ℝ → ENNReal := fun u r =>
    ENNReal.ofReal (Real.exp (2 * qf B u * r ^ 2 / n))
  have hF : Measurable (Function.uncurry F) := by
    change Measurable (fun p : (Fin n → ℝ) × ℝ =>
      ENNReal.ofReal (Real.exp (2 * qf B p.1 * p.2 ^ 2 / n)))
    fun_prop
  have hpolar := BstLean.Part53.gauss_polar_gen F hF
  calc ∫⁻ g, ENNReal.ofReal (Real.exp (2 * qf B (unitF53 g))) ∂stdGauss (Fin n)
      ≤ ∫⁻ g, ∫⁻ g', F (unitF53 g) (radF53 g') ∂stdGauss (Fin n) ∂stdGauss (Fin n) := by
        refine lintegral_mono (fun g => ?_)
        have := tangent_bound n hn (2 * qf B (unitF53 g))
        simpa [F, mul_assoc] using this
    _ = ∫⁻ g, F (unitF53 g) (radF53 g) ∂stdGauss (Fin n) := hpolar.symm
    _ = _ := by
        refine lintegral_congr (fun g => ?_)
        simp only [F]
        rw [mul_assoc 2, qf_unit_rad]

end BstLean.Part71
