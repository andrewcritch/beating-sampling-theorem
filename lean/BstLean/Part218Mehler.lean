import BstLean.Part134Mehler
import BstLean.Part105GebeleinL2

/-! The sharp second-order Gaussian inequality extends to square-integrable functions. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory
open BstLean.Part29 BstLean.Part105

section
variable {ι : Type} [Fintype ι]

noncomputable def coordinateL2 (i : ι) : Lp ℝ 2 (stdGauss ι) :=
  (BstLean.Part112.memLp_coord i).toLp (fun x => x i)

lemma inner_coordinateL2 (F : Lp ℝ 2 (stdGauss ι)) (i : ι) :
    inner ℝ (coordinateL2 i) F = ∫ x, F x * x i ∂stdGauss ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(BstLean.Part112.memLp_coord i).coeFn_toLp] with x hx
  change inner ℝ ((BstLean.Part112.memLp_coord i).toLp (fun x => x i) x) (F x) = _
  rw [hx]
  simp [mul_comm]

lemma coordinate_integral_congr {f g : (ι → ℝ) → ℝ} (h : f =ᵐ[stdGauss ι] g) (i : ι) :
    (∫ x, f x * x i ∂stdGauss ι) = ∫ x, g x * x i ∂stdGauss ι := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- The bounded-function hypothesis is removed by density in `L²`. -/
theorem mehler2_L2 {ρ : ℝ} (hρ : |ρ| ≤ 1) {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (stdGauss ι)) (hg : MemLp g 2 (stdGauss ι)) :
    |(∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂(stdGauss ι).prod (stdGauss ι)) -
      (∫ x, f x ∂stdGauss ι) * (∫ x, g x ∂stdGauss ι) -
      ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι)| ≤
      ρ ^ 2 * Real.sqrt ((∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι) -
        ∑ i, (∫ x, f x * x i ∂stdGauss ι) ^ 2) *
      Real.sqrt ((∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι) -
        ∑ i, (∫ x, g x * x i ∂stdGauss ι) ^ 2) := by
  classical
  have h₁ := ou_mp_fst (ι := ι)
  have h₂ := ou_mp_snd (ι := ι) hρ
  have key : ∀ F G : Lp ℝ 2 (stdGauss ι),
      |inner ℝ (Lp.compMeasurePreserving _ h₁ F) (Lp.compMeasurePreserving _ h₂ G) -
          inner ℝ (oneL2 (stdGauss ι)) F * inner ℝ (oneL2 (stdGauss ι)) G -
          ρ * ∑ i, inner ℝ (coordinateL2 i) F * inner ℝ (coordinateL2 i) G| ≤
        ρ ^ 2 * Real.sqrt (‖F - (inner ℝ (oneL2 (stdGauss ι)) F) • oneL2 (stdGauss ι)‖ ^ 2 -
          ∑ i, (inner ℝ (coordinateL2 i) F) ^ 2) *
        Real.sqrt (‖G - (inner ℝ (oneL2 (stdGauss ι)) G) • oneL2 (stdGauss ι)‖ ^ 2 -
          ∑ i, (inner ℝ (coordinateL2 i) G) ^ 2) := by
    have hc1 : Continuous (Lp.compMeasurePreserving (E := ℝ) (p := 2) _ h₁) :=
      (Lp.isometry_compMeasurePreserving h₁).continuous
    have hc2 : Continuous (Lp.compMeasurePreserving (E := ℝ) (p := 2) _ h₂) :=
      (Lp.isometry_compMeasurePreserving h₂).continuous
    refine (Lp.simpleFunc.denseRange (E := ℝ) (μ := stdGauss ι) (p := 2)
      ENNReal.ofNat_ne_top).induction_on₂ ?_ ?_
    · apply isClosed_le
      · apply Continuous.abs
        apply Continuous.sub
        · exact ((hc1.comp continuous_fst).inner (hc2.comp continuous_snd)).sub
            ((continuous_const.inner continuous_fst).mul (continuous_const.inner continuous_snd))
        · fun_prop
      · fun_prop
    · intro s t
      have hs := Lp.simpleFunc.toSimpleFunc_eq_toFun s
      have ht := Lp.simpleFunc.toSimpleFunc_eq_toFun t
      have h := BstLean.Part134.mehler2_sharp hρ
        (bm_simpleFunc (Lp.simpleFunc.toSimpleFunc s)) (bm_simpleFunc (Lp.simpleFunc.toSimpleFunc t))
      rw [cross_congr h₁ h₂ hs ht, var_congr hs, var_congr ht,
        integral_congr_ae hs, integral_congr_ae ht] at h
      simp_rw [coordinate_integral_congr hs, coordinate_integral_congr ht] at h
      simp_rw [inner_coordinateL2]
      rw [inner_comp, inner_oneL2, inner_oneL2, norm_sq_centre, norm_sq_centre]
      exact h
  have hF := hf.coeFn_toLp
  have hG := hg.coeFn_toLp
  have h := key (hf.toLp f) (hg.toLp g)
  simp_rw [inner_coordinateL2] at h
  rw [inner_comp, inner_oneL2, inner_oneL2, norm_sq_centre, norm_sq_centre,
    cross_congr h₁ h₂ hF hG, var_congr hF, var_congr hG,
    integral_congr_ae hF, integral_congr_ae hG] at h
  simp_rw [coordinate_integral_congr hF, coordinate_integral_congr hG] at h
  exact h

end
end BstLean.Part218
#print axioms BstLean.Part218.mehler2_L2
