import BstLean.Part61Defs
import BstLean.Part58Poly
import BstLean.Part29Sphere

/-! Centering and the zero-tilt case for Lemma S. -/

namespace BstLean.Part61.Concentration

open MeasureTheory
open BstLean.Part40 (SphLaw)
open BstLean.Part56 (UnitV lawRK)
open BstLean.Part29 (uniformSphere)

variable {n : ℕ}

/-- A quadratic envelope gives a uniform bound for its weighted second moment. -/
lemma quadratic_envelope_bound (a r p p0 : ℝ) (ha : 0 < a)
    (hp : p ≤ p0 - a * r ^ 2 / 2) :
    r ^ 2 * Real.exp p ≤ (2 / a) * Real.exp p0 := by
  have he : (a * r ^ 2 / 2) * Real.exp (-(a * r ^ 2 / 2)) ≤ 1 := by
    exact (Real.mul_exp_neg_le_exp_neg_one _).trans
      (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num))
  have hr : r ^ 2 * Real.exp (-(a * r ^ 2 / 2)) ≤ 2 / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  calc
    _ ≤ r ^ 2 * Real.exp (p0 - a * r ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) (sq_nonneg _)
    _ = (r ^ 2 * Real.exp (-(a * r ^ 2 / 2))) * Real.exp p0 := by
      rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le

/-- For a base measure of mass at most two, no Gaussian integral is needed. -/
lemma laplace_numerator_bound {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] (u p : Ω → ℝ) (u0 p0 a : ℝ) (ha : 0 < a)
    (hmass : ν.real Set.univ ≤ 2)
    (hp : ∀ᵐ x ∂ν, p x ≤ p0 - a * (u x - u0) ^ 2 / 2) :
    (∫ x, (u x - u0) ^ 2 * Real.exp (p x) ∂ν) ≤ (4 / a) * Real.exp p0 := by
  calc
    _ ≤ ∫ _x, ((2 / a) * Real.exp p0) ∂ν := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => by positivity)) (integrable_const _)
      filter_upwards [hp] with x hx
      exact quadratic_envelope_bound a (u x - u0) (p x) p0 ha hx
    _ = ν.real Set.univ * ((2 / a) * Real.exp p0) := by simp [measureReal_def]
    _ ≤ 2 * ((2 / a) * Real.exp p0) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by ring

lemma sx_sq_le_one (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) :
    sx61 v x ^ 2 ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
  rw [hv, hx] at h
  simpa [sx61] using h

lemma moment_range {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (v : Fin n → ℝ) (hv : UnitV v) :
    0 ≤ s2mom61 μ v ∧ s2mom61 μ v ≤ 1 := by
  let := hμ.prob
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  unfold s2mom61
  calc
    _ ≤ ∫ _x, (1 : ℝ) ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (integrable_const _)
      filter_upwards [hμ.sphere] with x hx
      exact sx_sq_le_one v x hv hx
    _ = 1 := by simp

lemma centered_square_identity {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (v : Fin n → ℝ) (a : ℝ) :
    (∫ x, (sx61 v x ^ 2 - a) ^ 2 ∂μ) =
      (∫ x, (sx61 v x ^ 2 - s2mom61 μ v) ^ 2 ∂μ) +
        (s2mom61 μ v - a) ^ 2 := by
  let := hμ.prob
  have hc : Continuous (fun x => sx61 v x ^ 2) := by unfold sx61; fun_prop
  have hi := BstLean.Part58.sphere_integrable58 hμ hc
  have hi2 : Integrable (fun x => (sx61 v x ^ 2) ^ 2) μ :=
    BstLean.Part58.sphere_integrable58 hμ (hc.pow 2)
  have expand (b : ℝ) :
      (∫ x, (sx61 v x ^ 2 - b) ^ 2 ∂μ) =
        (∫ x, (sx61 v x ^ 2) ^ 2 ∂μ) - 2 * b * s2mom61 μ v + b ^ 2 := by
    have he : (fun x => (sx61 v x ^ 2 - b) ^ 2) =
        (fun x => (sx61 v x ^ 2) ^ 2 - 2 * b * sx61 v x ^ 2 + b ^ 2) := by
      funext x; ring
    have hj : Integrable (fun x => (sx61 v x ^ 2) ^ 2 - 2 * b * sx61 v x ^ 2) μ :=
      hi2.sub (hi.const_mul (2 * b))
    rw [he, integral_add hj (integrable_const (b ^ 2)),
      integral_sub hi2 (hi.const_mul (2 * b)), integral_const_mul]
    simp [s2mom61]
  rw [expand, expand]
  ring

lemma variance_le_square_about {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (v : Fin n → ℝ) (a : ℝ) :
    (∫ x, (sx61 v x ^ 2 - s2mom61 μ v) ^ 2 ∂μ) ≤
      ∫ x, (sx61 v x ^ 2 - a) ^ 2 ∂μ := by
  rw [centered_square_identity hμ v a]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma variance_le_moment {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (v : Fin n → ℝ) (hv : UnitV v) :
    (∫ x, (sx61 v x ^ 2 - s2mom61 μ v) ^ 2 ∂μ) ≤ s2mom61 μ v := by
  have hi := BstLean.Part58.sphere_integrable58 hμ
    (show Continuous (fun x => sx61 v x ^ 2) by unfold sx61; fun_prop)
  calc
    _ ≤ ∫ x, (sx61 v x ^ 2 - 0) ^ 2 ∂μ := variance_le_square_about hμ v 0
    _ ≤ ∫ x, sx61 v x ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hi
      filter_upwards [hμ.sphere] with x hx
      have h := sx_sq_le_one v x hv hx
      have h0 := sq_nonneg (sx61 v x)
      simp only [sub_zero]
      nlinarith
    _ = _ := rfl

lemma lawRK_zero (hn : 1 ≤ n) (v : Fin n → ℝ) : lawRK n 0 v = uniformSphere n := by
  let := BstLean.Part29.uniformSphere_isProbability n hn
  simp [lawRK, BstLean.Part56.rk1, BstLean.Part50.binghamA, BstLean.Part50.ZA,
    BstLean.Part50.qA]

lemma uniform_moment (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) :
    s2mom61 (uniformSphere n) v = 1 / (n : ℝ) := by
  classical
  have hm := BstLean.Part29.uniformSphere_moments n hn
  have he (x : Fin n → ℝ) : sx61 v x ^ 2 =
      ∑ i, ∑ j, (v i * v j) * (x i * x j) := by
    simp only [sx61, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  unfold s2mom61
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hm.int2 i j).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hm.int2 _ j).const_mul _),
    integral_const_mul, hm.m2]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  simpa [pow_two, UnitV] using congrArg (fun r : ℝ => r * (1 / (n : ℝ))) hv

lemma lemmaS61_nonpos (C : ℝ) (hC : C ≤ 0) : LemmaS61 C 1 1 := by
  intro n hn v hv t ht0 ht
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htzero : t = 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hC (by positivity : (0 : ℝ) ≤ n)
    linarith
  subst t
  rw [lawRK_zero hn v]
  have hμ : SphLaw n (uniformSphere n) :=
    ⟨BstLean.Part29.uniformSphere_isProbability n hn,
      BstLean.Part29.uniformSphere_ae_sphere n⟩
  calc
    _ ≤ s2mom61 (uniformSphere n) v := variance_le_moment hμ v hv
    _ = 1 / (n : ℝ) := uniform_moment hn v hv
    _ ≤ 1 / Real.sqrt n := by
      apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by linarith))
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n), Real.sqrt_nonneg (n : ℝ)]

end BstLean.Part61.Concentration
