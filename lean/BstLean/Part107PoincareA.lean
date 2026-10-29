import BstLean.Part107Defs
import BstLean.Part48Rot

/-!
# Part 107, Gaussian Poincaré inequality, file A: the pointwise path bound and second moments
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (rotX rotY rot_preserving)
open BstLean.Part105

/-- Cauchy–Schwarz on `[0, a]` for a continuous function. -/
lemma cs_interval107 (D : ℝ → ℝ) (hD : Continuous D) {a : ℝ} (ha : 0 ≤ a) :
    (∫ θ in (0 : ℝ)..a, D θ) ^ 2 ≤ a * ∫ θ in (0 : ℝ)..a, D θ ^ 2 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0; simp
  set I := ∫ θ in (0 : ℝ)..a, D θ with hI
  set c := I / a with hc
  have h1 : 0 ≤ ∫ θ in (0 : ℝ)..a, (D θ - c) ^ 2 :=
    intervalIntegral.integral_nonneg ha (fun u _ => sq_nonneg _)
  have h2 : ∫ θ in (0 : ℝ)..a, (D θ - c) ^ 2 =
      (∫ θ in (0 : ℝ)..a, D θ ^ 2) - 2 * c * I + c ^ 2 * a := by
    have e : ∀ θ, (D θ - c) ^ 2 = D θ ^ 2 - 2 * c * D θ + c ^ 2 := fun θ => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp only [sub_zero, smul_eq_mul]; rw [← hI]; ring
    · exact (hD.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hD).intervalIntegrable _ _
    · exact ((hD.pow 2).sub (continuous_const.mul hD)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [h2] at h1
  have h3 : c * a = I := by rw [hc]; field_simp
  have h4 : c ^ 2 * a = c * I := by rw [← h3]; ring
  have h5 : I ^ 2 = a * (c * I) := by rw [← h3]; ring
  rw [h5]
  have : c * I ≤ ∫ θ in (0 : ℝ)..a, D θ ^ 2 := by linarith
  exact mul_le_mul_of_nonneg_left this ha

variable {ι : Type}

lemma rotX_eq107 (θ : ℝ) (x z : ι → ℝ) : rotX θ x z = Real.cos θ • x + Real.sin θ • z := by
  funext i; simp [rotX]

lemma rotY_eq107 (θ : ℝ) (x z : ι → ℝ) : rotY θ x z = -Real.sin θ • x + Real.cos θ • z := by
  funext i; simp [rotY]

variable [Fintype ι]

lemma hasDerivAt_rotX107 (x z : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun s => rotX s x z) (rotY θ x z) θ := by
  have h := ((Real.hasDerivAt_cos θ).smul_const x).add ((Real.hasDerivAt_sin θ).smul_const z)
  simp_rw [rotX_eq107, rotY_eq107]
  exact h

omit [Fintype ι] in
lemma continuous_rotX107 (x z : ι → ℝ) : Continuous (fun s => rotX s x z) := by
  simp_rw [rotX_eq107]; fun_prop

omit [Fintype ι] in
lemma continuous_rotY107 (x z : ι → ℝ) : Continuous (fun s => rotY s x z) := by
  simp_rw [rotY_eq107]; fun_prop

/-- The pointwise path bound (steps 1 of the proof). -/
lemma path_bound107 (f : (ι → ℝ) → ℝ) (U : Set (ι → ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (x z : ι → ℝ) (hp : ∀ θ : ℝ, rotX θ x z ∈ U) {a : ℝ}
    (ha : 0 ≤ a) :
    Continuous (fun θ => fderiv ℝ f (rotX θ x z) (rotY θ x z)) ∧
    (f (rotX a x z) - f x) ^ 2 ≤
      a * ∫ θ in (0 : ℝ)..a, (fderiv ℝ f (rotX θ x z) (rotY θ x z)) ^ 2 := by
  have hc : Continuous (fun θ => fderiv ℝ f (rotX θ x z) (rotY θ x z)) := by
    have h1 : Continuous (fun θ => fderiv ℝ f (rotX θ x z)) :=
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp_continuous (continuous_rotX107 x z) hp
    exact h1.clm_apply (continuous_rotY107 x z)
  refine ⟨hc, ?_⟩
  have hd : ∀ θ, HasDerivAt (fun s => f (rotX s x z))
      (fderiv ℝ f (rotX θ x z) (rotY θ x z)) θ := by
    intro θ
    have hfd : HasFDerivAt f (fderiv ℝ f (rotX θ x z)) (rotX θ x z) :=
      ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hp θ))).hasFDerivAt
    exact hfd.comp_hasDerivAt θ (hasDerivAt_rotX107 x z θ)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := a)
    (fun θ _ => hd θ) (hc.intervalIntegrable _ _)
  have h0 : rotX 0 x z = x := by rw [rotX_eq107]; simp
  rw [h0] at hftc
  rw [← hftc]
  exact cs_interval107 _ hc ha

lemma gauss_pair107 [DecidableEq ι] (i j : ι) : ∫ z, z i * z j ∂stdGauss ι = if i = j then 1 else 0 := by
  have hw := BstLean.Part35.stdGauss_wick_step i 1 (fun _ : Fin 1 => j)
  simpa [eq_comm] using hw

lemma gauss_pair_integrable107 (i j : ι) : Integrable (fun z : ι → ℝ => z i * z j) (stdGauss ι) := by
  classical
  have h := BstLean.Part35.stdGauss_prod_integrable (ι := ι) 2 ![i, j]
  simpa [Fin.prod_univ_two] using h

lemma lin_sq_expand107 (c z : ι → ℝ) :
    (∑ i, z i * c i) ^ 2 = ∑ i, ∑ j, (c i * c j) * (z i * z j) := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma lin_sq_integrable107 (c : ι → ℝ) :
    Integrable (fun z : ι → ℝ => (∑ i, z i * c i) ^ 2) (stdGauss ι) := by
  simp_rw [lin_sq_expand107]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (gauss_pair_integrable107 i j).const_mul _

/-- `E (Σ_i z_i c_i)² = Σ_i c_i²`. -/
lemma lin_sq_integral107 [DecidableEq ι] (c : ι → ℝ) :
    ∫ z, (∑ i, z i * c i) ^ 2 ∂stdGauss ι = ∑ i, c i ^ 2 := by
  simp_rw [lin_sq_expand107]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (gauss_pair_integrable107 i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (gauss_pair_integrable107 i j).const_mul _]
  simp_rw [integral_const_mul, gauss_pair107]
  simp [sq]

/-- `fderiv f y v = Σ_i v_i ∂_i f(y)`. -/
lemma fderiv_apply_sum107 [DecidableEq ι] (f : (ι → ℝ) → ℝ) (y v : ι → ℝ) :
    fderiv ℝ f y v = ∑ i, v i * fderiv ℝ f y (Pi.single i 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : ι → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum]

end BstLean.Part107
