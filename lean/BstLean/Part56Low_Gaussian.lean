import BstLean.Part56Defs
import BstLean.Part56Orth_Residual
import Mathlib.Probability.Distributions.Gaussian.CharFun

namespace BstLean.Part56.LowGaussian

open MeasureTheory BstLean.Part29 BstLean.Part36 BstLean.Part41 BstLean.Part53

private lemma gaussian_char {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∫ z, Complex.exp (((∑ i, z i * t i : ℝ) : ℂ) * Complex.I) ∂stdGauss ι) =
      Complex.exp ((-(∑ i, t i ^ 2 : ℝ) / 2 : ℝ) : ℂ) := by
  have h := ProbabilityTheory.charFun_stdGaussian (WithLp.toLp 2 t)
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)] at h
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq] at h
  simpa [BstLean.Part29.stdGauss, PiLp.inner_apply,
    EuclideanSpace.real_norm_sq_eq, mul_comm] using h

variable {n d : ℕ}

private def coefEquiv : CoefIdxD n d ≃ Mono n d × Fin n where
  toFun a := (⟨a.1, a.2.1⟩, a.2.2)
  invFun a := ⟨a.1.1, (a.1.2, a.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma linear_gaussian_law (ψ : Mono n d → ℝ) :
    (stdGauss (CoefIdxD n d)).map (fun Z => linZ Z ψ) =
      (stdGauss (Fin n)).map (fun g => Real.sqrt (nsq ψ) • g) := by
  classical
  have hL : Measurable (fun Z : CoefIdxD n d → ℝ => linZ Z ψ) := by
    unfold linZ colM
    fun_prop
  have hR : Measurable (fun g : Fin n → ℝ => Real.sqrt (nsq ψ) • g) := by fun_prop
  have he : ((stdGauss (CoefIdxD n d)).map (fun Z => linZ Z ψ)).map (WithLp.toLp 2) =
      ((stdGauss (Fin n)).map (fun g => Real.sqrt (nsq ψ) • g)).map (WithLp.toLp 2) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, Measure.map_map (by fun_prop) hL,
      integral_map (by fun_prop) (by fun_prop)]
    rw [charFun_apply, Measure.map_map (by fun_prop) hR,
      integral_map (by fun_prop) (by fun_prop)]
    have hinner (x : Fin n → ℝ) :
        inner ℝ (WithLp.toLp 2 x) t = ∑ i, x i * t i := by
      simp only [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp [RCLike.inner_apply, mul_comm]
    simp only [Function.comp_apply, hinner]
    have hd (Z : CoefIdxD n d → ℝ) :
        (∑ a, linZ Z ψ a * t a) =
          ∑ α, Z α * (ψ ⟨α.1, α.2.1⟩ * t α.2.2) := by
      rw [← coefEquiv.symm.sum_comp, Fintype.sum_prod_type]
      unfold linZ colM
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [coefEquiv]
      ring
    have hr (g : Fin n → ℝ) :
        (∑ a, (Real.sqrt (nsq ψ) • g) a * t a) =
          ∑ a, g a * (Real.sqrt (nsq ψ) * t a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [hd, hr]
    rw [gaussian_char, gaussian_char]
    congr 2
    have hs : ∑ α : CoefIdxD n d, (ψ ⟨α.1, α.2.1⟩ * t α.2.2) ^ 2 =
        nsq ψ * ∑ a, t a ^ 2 := by
      rw [← coefEquiv.symm.sum_comp, Fintype.sum_prod_type]
      simp only [coefEquiv, Equiv.coe_fn_symm_mk, mul_pow]
      change (∑ p : Mono n d, ∑ a : Fin n, ψ p ^ 2 * t a ^ 2) =
        (∑ p : Mono n d, ψ p ^ 2) * ∑ a : Fin n, t a ^ 2
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    have hn : 0 ≤ nsq ψ := Finset.sum_nonneg fun p _ => sq_nonneg _
    rw [hs]
    simp_rw [mul_pow, Real.sq_sqrt hn]
    rw [← Finset.mul_sum]
  exact MeasurableEquiv.map_measurableEquiv_injective
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) he

lemma integral_linear_gaussian (ψ : Mono n d → ℝ) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) (y : Fin n → ℝ) :
    (∫ Z, F (y + linZ Z ψ) ∂stdGauss (CoefIdxD n d)) =
      ∫ g, F (y + Real.sqrt (nsq ψ) • g) ∂stdGauss (Fin n) := by
  have hL : Measurable (fun Z : CoefIdxD n d → ℝ => linZ Z ψ) := by
    unfold linZ colM
    fun_prop
  have hR : Measurable (fun g : Fin n → ℝ => Real.sqrt (nsq ψ) • g) := by fun_prop
  have hFy : Continuous (fun z : Fin n → ℝ => F (y + z)) :=
    hF.comp (continuous_const.add continuous_id)
  rw [← integral_map hL.aemeasurable hFy.aestronglyMeasurable,
    linear_gaussian_law ψ, integral_map hR.aemeasurable hFy.aestronglyMeasurable]


end BstLean.Part56.LowGaussian
