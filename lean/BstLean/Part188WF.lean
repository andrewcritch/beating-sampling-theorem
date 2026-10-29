import BstLean.Part188Weight
import BstLean.Part170FlQ

/-! Weighted domination and the scalar mean step of the corrected WF argument. -/

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134 BstLean.Part160

lemma eDir_sq_le_weighted {m : ℕ} (b h v : Fin m → ℝ) {N a d omega f : ℝ}
    (hN : 0 < N) (hd : 0 < d)
    (hres : normSq (res b h) = N * (omega - f ^ 2)) :
    (∑ j, eDir b h j * v j) ^ 2 ≤
      weightSq a d f / N * (∑ j, res b h j * v j) ^ 2 +
        (if goodInput a d omega f then 0 else normSq v) := by
  classical
  by_cases hg : goodInput a d omega f
  · rw [if_pos hg, add_zero]
    have hR : 0 < omega - f ^ 2 := hd.trans_le (goodInput_residual hg)
    have hns : 0 < normSq (res b h) := by rw [hres]; positivity
    have he : (∑ j, eDir b h j * v j) =
        (√(normSq (res b h)))⁻¹ * (∑ j, res b h j * v j) := by
      unfold eDir
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]
    rw [he, mul_pow, inv_pow, Real.sq_sqrt hns.le, hres, mul_inv_rev]
    have hcoef : (omega - f ^ 2)⁻¹ * N⁻¹ ≤ weightSq a d f / N := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (weightSq_on_good hd hg) (inv_nonneg.mpr hN.le)
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  · rw [if_neg hg]
    have hunit : normSq (eDir b h) ≤ 1 := by
      rcases eDir_unit_or_zero b h with he | he
      · exact he.le
      · rw [he]; simp [normSq]
    have hCS := sum_mul_sq_le (eDir b h) v
    have hbound : (∑ j, eDir b h j * v j) ^ 2 ≤ normSq v :=
      hCS.trans ((mul_le_mul_of_nonneg_right hunit (normSq_nonneg v)).trans_eq (one_mul _))
    have hpos : 0 ≤ weightSq a d f / N * (∑ j, res b h j * v j) ^ 2 :=
      mul_nonneg (div_nonneg (weightSq_nonneg hd) hN.le) (sq_nonneg _)
    linarith

/-- Domination uses the complement of the good intersection, with its full mass. -/
theorem weighted_frame_domination {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ] (h : X → Fin m → ℝ) (hh : Measurable h)
    (b v : Fin m → ℝ) (omega f : X → ℝ) {N a d : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hG : MeasurableSet {x | goodInput a d (omega x) (f x)})
    (hres : ∀ x, normSq (res b (h x)) = N * (omega x - f x ^ 2))
    (hi : Integrable (fun x => weightSq a d (f x) * (∑ j, res b (h x) j * v j) ^ 2) μ) :
    ∫ x, (∑ j, eDir b (h x) j * v j) ^ 2 ∂μ ≤
      (∫ x, weightSq a d (f x) * (∑ j, res b (h x) j * v j) ^ 2 ∂μ) / N +
        μ.real {x | ¬ goodInput a d (omega x) (f x)} * normSq v := by
  classical
  have hm : Measurable (fun x => (∑ j, eDir b (h x) j * v j) ^ 2) :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_eDir b).comp hh)).mul_const _).pow_const 2
  have hL : Integrable (fun x => (∑ j, eDir b (h x) j * v j) ^ 2) μ := by
    refine Integrable.of_bound hm.aestronglyMeasurable (normSq v) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hu : normSq (eDir b (h x)) ≤ 1 := by
      rcases eDir_unit_or_zero b (h x) with he | he
      · exact he.le
      · rw [he]; simp [normSq]
    exact (sum_mul_sq_le (eDir b (h x)) v).trans
      ((mul_le_mul_of_nonneg_right hu (normSq_nonneg v)).trans_eq (one_mul _))
  set G := {x | goodInput a d (omega x) (f x)}
  have hI : Integrable (Gᶜ.indicator (fun _ => normSq v)) μ :=
    (integrable_const _).indicator hG.compl
  have hp : ∀ x, (∑ j, eDir b (h x) j * v j) ^ 2 ≤
      (weightSq a d (f x) * (∑ j, res b (h x) j * v j) ^ 2) / N +
        Gᶜ.indicator (fun _ => normSq v) x := by
    intro x
    have he : Gᶜ.indicator (fun _ => normSq v) x =
        (if goodInput a d (omega x) (f x) then 0 else normSq v) := by
      by_cases hx : goodInput a d (omega x) (f x) <;> simp [G, hx]
    rw [he, mul_div_right_comm]
    exact eDir_sq_le_weighted b (h x) v hN hd (hres x)
  have hbound := integral_mono hL ((hi.div_const N).add hI) hp
  change (∫ x, (∑ j, eDir b (h x) j * v j) ^ 2 ∂μ) ≤
    ∫ x, ((weightSq a d (f x) * (∑ j, res b (h x) j * v j) ^ 2) / N +
      Gᶜ.indicator (fun _ => normSq v) x) ∂μ at hbound
  rw [integral_add (f := fun x => (weightSq a d (f x) *
      (∑ j, res b (h x) j * v j) ^ 2) / N) (g := Gᶜ.indicator (fun _ => normSq v))
      (hi.div_const N) hI, integral_div,
    integral_indicator_const _ hG.compl, smul_eq_mul] at hbound
  exact hbound

/-- The exact decomposition of a scalar weighted mean. -/
lemma weighted_mean_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p z : X → ℝ)
    (hp : Integrable p μ) (hz : Integrable z μ)
    (hpz : Integrable (fun x => p x * z x) μ) :
    ∫ x, p x * z x ∂μ = (∫ x, p x ∂μ) * (∫ x, z x ∂μ) +
      ∫ x, (p x - ∫ y, p y ∂μ) * (z x - ∫ y, z y ∂μ) ∂μ := by
  have he : (fun x => (p x - ∫ y, p y ∂μ) * (z x - ∫ y, z y ∂μ)) =
      fun x => ((p x * z x - p x * (∫ y, z y ∂μ)) -
        (∫ y, p y ∂μ) * z x) + (∫ y, p y ∂μ) * (∫ y, z y ∂μ) := by
    funext x; ring
  rw [he, integral_add (f := fun x => (p x * z x - p x * (∫ y, z y ∂μ)) -
      (∫ y, p y ∂μ) * z x) (g := fun _ => (∫ y, p y ∂μ) * (∫ y, z y ∂μ))
      ((hpz.sub (hp.mul_const _)).sub (hz.const_mul _)) (integrable_const _),
    integral_sub (f := fun x => p x * z x - p x * (∫ y, z y ∂μ))
      (g := fun x => (∫ y, p y ∂μ) * z x) (hpz.sub (hp.mul_const _)) (hz.const_mul _),
    integral_sub (f := fun x => p x * z x) (g := fun x => p x * (∫ y, z y ∂μ))
      hpz (hp.mul_const _), integral_mul_const, integral_const_mul,
    integral_const, probReal_univ, one_smul]
  ring

/-- Cauchy-Schwarz preserves the dependence of the scalar weight and the residual. -/
theorem weighted_mean_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p z : X → ℝ)
    (hp : Integrable p μ) (hz : Integrable z μ)
    (hpz : Integrable (fun x => p x * z x) μ)
    (hp2 : Integrable (fun x => (p x - ∫ y, p y ∂μ) ^ 2) μ)
    (hz2 : Integrable (fun x => (z x - ∫ y, z y ∂μ) ^ 2) μ) :
    |∫ x, p x * z x ∂μ| ≤ |∫ x, p x ∂μ| * |∫ x, z x ∂μ| +
      √(∫ x, (p x - ∫ y, p y ∂μ) ^ 2 ∂μ) *
        √(∫ x, (z x - ∫ y, z y ∂μ) ^ 2 ∂μ) := by
  set P := ∫ y, p y ∂μ
  set Z := ∫ y, z y ∂μ
  have hi : Integrable (fun x => (p x - P) * (z x - Z)) μ := by
    have he : (fun x => (p x - P) * (z x - Z)) =
        fun x => ((p x * z x - p x * Z) - P * z x) + P * Z := by funext x; ring
    rw [he]
    exact ((hpz.sub (hp.mul_const _)).sub (hz.const_mul _)).add (integrable_const _)
  have hAbs : |∫ x, (p x - P) * (z x - Z) ∂μ| ≤
      ∫ x, |p x - P| * |z x - Z| ∂μ := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (norm_integral_le_integral_norm (f := fun x => (p x - P) * (z x - Z)))
  have hpAbs2 : Integrable (fun x => |p x - P| ^ 2) μ := by simpa only [sq_abs] using hp2
  have hzAbs2 : Integrable (fun x => |z x - Z| ^ 2) μ := by simpa only [sq_abs] using hz2
  have hAbsI : Integrable (fun x => |p x - P| * |z x - Z|) μ := by
    simpa only [abs_mul] using hi.abs
  have hCS := BstLean.Part170.int_cs hpAbs2 hzAbs2 hAbsI
  simp only [sq_abs] at hCS
  rw [weighted_mean_identity μ p z hp hz hpz]
  calc _ ≤ |P * Z| + |∫ x, (p x - P) * (z x - Z) ∂μ| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; exact add_le_add_right (hAbs.trans hCS) _

/-- The scalar second-moment identity under a probability distribution. -/
lemma second_moment_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (z : X → ℝ)
    (hz : Integrable z μ) (hz2 : Integrable (fun x => z x ^ 2) μ) :
    ∫ x, z x ^ 2 ∂μ = ∫ x, (z x - ∫ y, z y ∂μ) ^ 2 ∂μ + (∫ y, z y ∂μ) ^ 2 := by
  set Z := ∫ y, z y ∂μ
  have he : (fun x => (z x - Z) ^ 2) = fun x => z x ^ 2 - 2 * Z * z x + Z ^ 2 := by
    funext x; ring
  rw [he, integral_add (f := fun x => z x ^ 2 - 2 * Z * z x) (g := fun _ => Z ^ 2)
      (hz2.sub (hz.const_mul _)) (integrable_const _),
    integral_sub (f := fun x => z x ^ 2) (g := fun x => 2 * Z * z x)
      hz2 (hz.const_mul _), integral_const_mul, integral_const,
    probReal_univ, one_smul]
  dsimp [Z]
  ring

/-- WF after the analytic covariance step. All means use the same probability distribution.
The covariance bound for the weighted residual remains an explicit premise. -/
theorem WF_of_weighted_covariance {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ] (h : X → Fin m → ℝ) (hh : Measurable h)
    (b v : Fin m → ℝ) (omega f : X → ℝ) {N a d Npsi B xi Ncov Vpsi Beta : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hv : normSq v = 1)
    (hG : MeasurableSet {x | goodInput a d (omega x) (f x)})
    (hres : ∀ x, normSq (res b (h x)) = N * (omega x - f x ^ 2))
    (hNcov : 0 ≤ Ncov) (hVpsi : 0 ≤ Vpsi)
    (hp : Integrable (fun x => weight a d (f x)) μ)
    (hz : Integrable (fun x => ∑ j, res b (h x) j * v j) μ)
    (hpz : Integrable (fun x => weight a d (f x) * (∑ j, res b (h x) j * v j)) μ)
    (hpz2 : Integrable (fun x => (weight a d (f x) * (∑ j, res b (h x) j * v j)) ^ 2) μ)
    (hp2 : Integrable (fun x => (weight a d (f x) - ∫ y, weight a d (f y) ∂μ) ^ 2) μ)
    (hz2 : Integrable (fun x => ((∑ j, res b (h x) j * v j) -
      ∫ y, (∑ j, res b (h y) j * v j) ∂μ) ^ 2) μ)
    (hvarp : ∫ x, (weight a d (f x) - ∫ y, weight a d (f y) ∂μ) ^ 2 ∂μ ≤ Vpsi)
    (hvarz : ∫ x, ((∑ j, res b (h x) j * v j) -
      ∫ y, (∑ j, res b (h y) j * v j) ∂μ) ^ 2 ∂μ ≤ Ncov)
    (hmean : |∫ x, (∑ j, res b (h x) j * v j) ∂μ| ≤ √xi)
    (hcov : ∫ x, (weight a d (f x) * (∑ j, res b (h x) j * v j) -
      ∫ y, weight a d (f y) * (∑ j, res b (h y) j * v j) ∂μ) ^ 2 ∂μ ≤
        (√Npsi + √B) ^ 2)
    (hmass : N * μ.real {x | ¬ goodInput a d (omega x) (f x)} ≤ Beta) :
    N * ∫ x, (∑ j, eDir b (h x) j * v j) ^ 2 ∂μ ≤
      (√Npsi + √B) ^ 2 +
        ((∫ x, weight a d (f x) ∂μ) * √xi + √(Vpsi * Ncov)) ^ 2 + Beta := by
  set z : X → ℝ := fun x => ∑ j, res b (h x) j * v j
  set p : X → ℝ := fun x => weight a d (f x)
  have hP : 0 ≤ ∫ x, p x ∂μ := integral_nonneg fun _ => Real.sqrt_nonneg _
  have hm := weighted_mean_bound μ p z hp hz hpz hp2 hz2
  rw [abs_of_nonneg hP] at hm
  have h1 := mul_le_mul_of_nonneg_left hmean hP
  have h2 : √(∫ x, (p x - ∫ y, p y ∂μ) ^ 2 ∂μ) *
      √(∫ x, (z x - ∫ y, z y ∂μ) ^ 2 ∂μ) ≤ √(Vpsi * Ncov) := by
    rw [Real.sqrt_mul hVpsi]
    exact mul_le_mul (Real.sqrt_le_sqrt hvarp) (Real.sqrt_le_sqrt hvarz)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmFinal : |∫ x, p x * z x ∂μ| ≤ (∫ x, p x ∂μ) * √xi + √(Vpsi * Ncov) := by
    linarith
  have hmSq : (∫ x, p x * z x ∂μ) ^ 2 ≤
      ((∫ x, p x ∂μ) * √xi + √(Vpsi * Ncov)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hmFinal 2
    rwa [sq_abs] at h
  have hsecond := second_moment_identity μ (fun x => p x * z x) hpz hpz2
  have hI : (fun x => weightSq a d (f x) * (∑ j, res b (h x) j * v j) ^ 2) =
      (fun x => (p x * z x) ^ 2) := by
    funext x
    dsimp [p, z]
    rw [mul_pow, weight_sq hd]
  have hdom := weighted_frame_domination μ h hh b v omega f hN hd hG hres
    (by rw [hI]; exact hpz2)
  rw [hI, hv, mul_one] at hdom
  have hmul := mul_le_mul_of_nonneg_left hdom hN.le
  have he : N * ((∫ x, (p x * z x) ^ 2 ∂μ) / N +
      μ.real {x | ¬ goodInput a d (omega x) (f x)}) =
      (∫ x, (p x * z x) ^ 2 ∂μ) + N * μ.real {x | ¬ goodInput a d (omega x) (f x)} := by
    field_simp
  rw [he, hsecond] at hmul
  linarith

end BstLean.Part188
