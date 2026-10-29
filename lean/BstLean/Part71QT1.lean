import BstLean.Part71Defs
import BstLean.Part71QT1_Scalar
import BstLean.Part71QT1_Gauss
import BstLean.Part71QT1_Sphere

/-!
# Part 71, Theorem QT1: the chi-square bound for a quadratic tilt

For symmetric `A` with `λ_max(A₀) ≤ n/8` (`A₀ = ctrM A`, the traceless part), the quadratic tilt
`quadTilt n A ∝ exp(xᵀAx) σ` has `χ²(D_A‖σ) ≤ exp(8‖A₀‖_F²/n²) − 1`.

Proof. On the sphere `xᵀAx = xᵀA₀x + tr A/n`, so the density is `exp(Q₀)/Z₀` with
`Z₀ = E_σ e^{Q₀} ≥ 1` (because `E_σ Q₀ = 0`). Then `E_σ ρ² = E_σ e^{2Q₀}/Z₀² ≤ E_σ e^{2Q₀}`,
`E_σ e^{2Q₀} ≤ E_γ e^{2Q₀(g)/n}` (`sphere_le_gauss`, a tangent-line bound plus the independence of
the direction and the radius of a standard Gaussian), and `E_γ e^{2Q₀(g)/n} ≤ exp(8‖A₀‖_F²/n²)`
(`gauss_quad_bound`, diagonalization plus `1 ≤ (1 − u) e^{u + u²}` for `u ≤ 1/2`).

Helper files: `Part71QT1_Scalar.lean`, `Part71QT1_Gauss.lean`, `Part71QT1_Sphere.lean`.
-/

namespace BstLean.Part71

open MeasureTheory
open BstLean.Part29 (uniformSphere)

private lemma sphere_integrable71 {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ]
    (hs : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

theorem qf_ctrM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qf A x = qf (ctrM A) x + A.trace / n * ∑ i, x i ^ 2 := by
  unfold qf ctrM
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.mul_sum]
  ring_nf

theorem ctrM_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (ctrM A).IsHermitian := by
  unfold Matrix.IsHermitian ctrM
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, hA.eq]

theorem ctrM_trace {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (ctrM A).trace = 0 := by
  have hnpos : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  unfold ctrM
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  field_simp
  ring

/-- `E_σ xᵀBx = tr B / n`. -/
theorem sphere_mean_qf {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, qf B x ∂uniformSphere n = B.trace / n := by
  have hM := BstLean.Part29.uniformSphere_moments n hn
  have hint : ∀ i j, Integrable (fun x : Fin n → ℝ => B i j * x i * x j) (uniformSphere n) := by
    intro i j
    simpa [mul_assoc] using (hM.int2 i j).const_mul (B i j)
  have h2 : ∀ i j, ∫ x, B i j * x i * x j ∂uniformSphere n =
      B i j * (if i = j then 1 / (n : ℝ) else 0) := by
    intro i j
    rw [← hM.m2 i j, ← integral_const_mul]
    congr 1; funext x; ring
  have hsum : ∫ x, qf B x ∂uniformSphere n =
      ∑ i, ∑ j, B i j * (if i = j then 1 / (n : ℝ) else 0) := by
    unfold qf
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    exact Finset.sum_congr rfl (fun j _ => h2 i j)
  rw [hsum]
  simp [Matrix.trace, div_eq_mul_inv, Finset.sum_mul]

theorem qt1 (n : ℕ) (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hmax : ∀ v : Fin n → ℝ, qf (ctrM A) v ≤ (n : ℝ) / 8 * ∑ i, v i ^ 2) :
    ChiLaw n (quadTilt n A) (Real.exp (8 * frobM (ctrM A) / (n : ℝ) ^ 2) - 1) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hsph := BstLean.Part29.uniformSphere_ae_sphere n
  set B := ctrM A with hBdef
  set c := A.trace / n with hc
  have hqB := continuous_qf B
  have hqA := continuous_qf A
  have hon : ∀ᵐ x ∂uniformSphere n, qf A x = qf B x + c := by
    filter_upwards [hsph] with x hx
    rw [qf_ctrM A x, hx, mul_one]
  set Z₀ := ∫ x, Real.exp (qf B x) ∂uniformSphere n with hZ₀
  have hZ₀1 : 1 ≤ Z₀ := by
    have h1 : ∫ x, (1 + qf B x) ∂uniformSphere n = 1 := by
      rw [integral_add (integrable_const _) (sphere_integrable71 hsph hqB), sphere_mean_qf hn,
        ctrM_trace hn]
      simp
    rw [← h1]
    exact integral_mono (sphere_integrable71 hsph (by fun_prop))
      (sphere_integrable71 hsph (by fun_prop))
      (fun x => by have := Real.add_one_le_exp (qf B x); linarith)
  have hZ₀pos : 0 < Z₀ := by linarith
  have hZ : tiltZ n A = Real.exp c * Z₀ := by
    unfold tiltZ
    rw [hZ₀, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hon] with x hx
    rw [hx, Real.exp_add, mul_comm]
  have hZpos : 0 < tiltZ n A := by rw [hZ]; exact mul_pos (Real.exp_pos c) hZ₀pos
  let ρ : (Fin n → ℝ) → ℝ := fun x => Real.exp (qf A x) / tiltZ n A
  have hρc : Continuous ρ := by fun_prop
  refine ⟨⟨?_⟩, ρ, hρc.measurable, fun x => (div_pos (Real.exp_pos _) hZpos).le, rfl,
    sphere_integrable71 hsph (by fun_prop), ?_⟩
  · -- total mass one
    unfold quadTilt
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (sphere_integrable71 hsph hρc)
        (ae_of_all _ (fun x => (div_pos (Real.exp_pos _) hZpos).le)),
      integral_div]
    change ENNReal.ofReal (tiltZ n A / tiltZ n A) = 1
    rw [div_self hZpos.ne', ENNReal.ofReal_one]
  · -- the second moment
    set I₂ := ∫ x, Real.exp (2 * qf B x) ∂uniformSphere n with hI₂
    have hρ2 : ∫ x, ρ x ^ 2 ∂uniformSphere n = I₂ / Z₀ ^ 2 := by
      rw [hI₂, ← integral_div]
      refine integral_congr_ae ?_
      filter_upwards [hon] with x hx
      simp only [ρ]
      rw [hx, hZ, div_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      push_cast
      rw [mul_add, Real.exp_add]
      field_simp
    have hI₂nn : 0 ≤ I₂ := integral_nonneg (fun x => (Real.exp_pos _).le)
    have hI₂le : I₂ ≤ Real.exp (8 * frobM B / (n : ℝ) ^ 2) := by
      have hlin : ENNReal.ofReal I₂ =
          ∫⁻ x, ENNReal.ofReal (Real.exp (2 * qf B x)) ∂uniformSphere n :=
        ofReal_integral_eq_lintegral_ofReal (sphere_integrable71 hsph (by fun_prop))
          (ae_of_all _ (fun x => (Real.exp_pos _).le))
      have h := (sphere_le_gauss n hn B).trans
        (gauss_quad_bound n hn B (ctrM_isHermitian A hA) (ctrM_trace hn A) hmax)
      rw [← hlin] at h
      exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h
    rw [hρ2]
    calc I₂ / Z₀ ^ 2 ≤ I₂ := div_le_self hI₂nn (one_le_pow₀ hZ₀1)
      _ ≤ _ := by linarith

end BstLean.Part71
