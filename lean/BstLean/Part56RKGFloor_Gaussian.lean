import BstLean.Part56Orth_Mean

namespace BstLean.Part56.FloorAux

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens fval contr)
open BstLean.Part53 (linZ nsq sg)

variable {n d : ℕ}

private lemma gaussian_char {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∫ z, Complex.exp (((∑ i, z i * t i : ℝ) : ℂ) * Complex.I) ∂stdGauss ι) =
      Complex.exp ((-(∑ i, t i ^ 2 : ℝ) / 2 : ℝ) : ℂ) := by
  have h := ProbabilityTheory.charFun_stdGaussian (WithLp.toLp 2 t)
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)] at h
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq] at h
  simpa [BstLean.Part29.stdGauss, PiLp.inner_apply,
    EuclideanSpace.real_norm_sq_eq, mul_comm] using h

/-- A linear Gaussian field has independent coordinates with its feature variance. -/
theorem linear_gaussian_law (ψ : Mono n d → ℝ) :
    (stdGauss (CoefIdxD n d)).map (fun Z => linZ Z ψ) =
      (stdGauss (Fin n)).map (fun g => Real.sqrt (nsq ψ) • g) := by
  classical
  have hm : Measurable (fun Z : CoefIdxD n d → ℝ => linZ Z ψ) := by
    unfold linZ BstLean.Part41.colM
    fun_prop
  have hn : 0 ≤ nsq ψ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : ((stdGauss (CoefIdxD n d)).map (fun Z => linZ Z ψ)).map
        (WithLp.toLp 2) =
      ((stdGauss (Fin n)).map (fun g => Real.sqrt (nsq ψ) • g)).map
        (WithLp.toLp 2) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, Measure.map_map (by fun_prop) hm,
      integral_map (by fun_prop) (by fun_prop)]
    rw [charFun_apply, Measure.map_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    have hinner (x : Fin n → ℝ) :
        inner ℝ (WithLp.toLp 2 x) t = ∑ i, x i * t i := by
      simp only [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp [RCLike.inner_apply, mul_comm]
    simp only [Function.comp_apply, hinner]
    let w : CoefIdxD n d → ℝ := fun α => ψ ⟨α.1, α.2.1⟩ * t α.2.2
    have hlin (Z : CoefIdxD n d → ℝ) :
        (∑ a, linZ Z ψ a * t a) = ∑ α, Z α * w α := by
      simp only [linZ, BstLean.Part41.colM, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type, w]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro a ha
      ring
    have hnorm : (∑ α, w α ^ 2) = nsq ψ * ∑ a, t a ^ 2 := by
      simp only [w, mul_pow, Fintype.sum_sigma, Fintype.sum_prod_type]
      simp only [← Finset.mul_sum]
      simp only [← Finset.sum_mul]
      simp only [nsq, Fintype.sum_sigma]
    have hscale (g : Fin n → ℝ) :
        (∑ a, (Real.sqrt (nsq ψ) • g) a * t a) =
          ∑ a, g a * (Real.sqrt (nsq ψ) * t a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [hlin, hscale]
    rw [gaussian_char, gaussian_char, hnorm]
    have hs : (∑ a, (Real.sqrt (nsq ψ) * t a) ^ 2) = nsq ψ * ∑ a, t a ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt hn, ← Finset.mul_sum]
    rw [hs]
  exact MeasurableEquiv.map_measurableEquiv_injective
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) he

/-- Equal Gaussian laws give equal integrals for every continuous test function. -/
theorem linear_gaussian_integral (ψ : Mono n d → ℝ)
    (H : (Fin n → ℝ) → ℝ) (hH : Continuous H) :
    (∫ Z, H (linZ Z ψ) ∂stdGauss (CoefIdxD n d)) =
      ∫ g, H (Real.sqrt (nsq ψ) • g) ∂stdGauss (Fin n) := by
  have hm : Measurable (fun Z : CoefIdxD n d → ℝ => linZ Z ψ) := by
    unfold linZ BstLean.Part41.colM
    fun_prop
  rw [← integral_map hm.aemeasurable hH.aestronglyMeasurable,
    linear_gaussian_law, integral_map (by fun_prop) hH.aestronglyMeasurable]

end BstLean.Part56.FloorAux
