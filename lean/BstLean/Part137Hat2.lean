import BstLean.Part137Hat

/-!
# Part 137, item 4, the sharper constant: Lemma H2(b) with a constant below `8.3`

Role: `delegations/statements/p137-spec.md` (item 4). Paper source: `onW16c-cx.md` §2.

The two first-layer terms of `hatFluct_core` with the row independence of `M₁`:

* `sphere_relu_sq`: `E_u ReLU(⟨r, u⟩)² = |r|²/(2N)`; `sphere_relu_mean_sq`:
  `(E_u ReLU(⟨r, u⟩))² ≤ |r|²/(4N)`.
* `GamS_rows`: `Γ* = Σ_j |row_j(M₁)|²/(mN)` (the paper's `Γ* = S₁/N`).
* `GamS_L2x`: `E_{M₁}(Γ* − γ)² = 2γ²/(Nm)`.
* `cov_L2x`: `E_{M₁}(c − γ q₁)² ≤ γ²(1 + 2/N)/(2m)`, `c = t⟨h₁(u₀), h̄₁⟩`.
* `hatFluct2_pt`: for a unit vector `u₀`, `‖T̂(u₀) − γκ(q₁)‖_{L²(θ)} ≤ γ·cHat2 N m`,
  `cHat2 N m² = (6(1 + 5/m) + (κ(0)(√5 + √(2/N)) + √((1 + 2/N)/2))²)/m`.
* `innerFluct137_hat2`, `hatFluct137_var2`: `N = 2n`, `m = mW n`, `n ≥ 4096`: the bound
  `8.03·γ²/m` (the paper: `8.3`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part137

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  gaussMom gaussMom_eq)
open BstLean.Part73 (IsOrth uniformSphere_orth stdGauss_orth orth_sumsq)
open BstLean.Part80 (dot_mulVec')
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

variable {N m : ℕ}

/-! ## The sphere: symmetric moments of `ReLU(⟨r, u⟩)` -/

lemma isOrth_neg_one (K : ℕ) : IsOrth (-1 : Matrix (Fin K) (Fin K) ℝ) := by
  unfold IsOrth
  simp

lemma sphere_neg {F : (Fin N → ℝ) → ℝ} (hF : Continuous F) :
    ∫ u, F (-u) ∂uniformSphere N = ∫ u, F u ∂uniformSphere N := by
  have hmO : Measurable (fun u : Fin N → ℝ => (-1 : Matrix (Fin N) (Fin N) ℝ).mulVec u) := by
    fun_prop
  have h := integral_map (μ := uniformSphere N) hmO.aemeasurable (f := F) hF.aestronglyMeasurable
  rw [uniformSphere_orth _ (isOrth_neg_one N)] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change F (-u) = F ((-1 : Matrix (Fin N) (Fin N) ℝ).mulVec u)
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]

lemma continuous_dotR (r : Fin N → ℝ) : Continuous (fun u : Fin N → ℝ => ∑ i, r i * u i) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

lemma dotR_neg (r u : Fin N → ℝ) : ∑ i, r i * (-u) i = -∑ i, r i * u i := by
  simp [Finset.sum_neg_distrib]

lemma sphere_dot_sq (hN : 1 ≤ N) (r : Fin N → ℝ) :
    ∫ u, (∑ i, r i * u i) ^ 2 ∂uniformSphere N = normSq r / (N : ℝ) := by
  have h := sphere_lin hN r
  have e : (fun u : Fin N → ℝ => (∑ i, r i * u i) ^ 2) = fun u => (∑ i, u i * r i) ^ 2 := by
    funext u
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, h]
  unfold normSq
  ring

/-- `E_u ReLU(⟨r, u⟩)² = |r|²/(2N)`. -/
lemma sphere_relu_sq (hN : 1 ≤ N) (r : Fin N → ℝ) :
    ∫ u, relu (∑ i, r i * u i) ^ 2 ∂uniformSphere N = normSq r / (2 * (N : ℝ)) := by
  have hc : Continuous (fun u : Fin N → ℝ => relu (∑ i, r i * u i) ^ 2) :=
    (continuous_relu.comp (continuous_dotR r)).pow 2
  have hn := sphere_neg hc
  simp_rw [dotR_neg] at hn
  have hc' : Continuous (fun u : Fin N → ℝ => relu (-∑ i, r i * u i) ^ 2) :=
    (continuous_relu.comp (continuous_dotR r).neg).pow 2
  have hs := integral_add (sphere_cont_integrable hN hc) (sphere_cont_integrable hN hc')
  have e : (fun u : Fin N → ℝ => relu (∑ i, r i * u i) ^ 2 + relu (-∑ i, r i * u i) ^ 2) =
      fun u => (∑ i, r i * u i) ^ 2 := by
    funext u
    rw [relu_pow_add _ (by norm_num), sq_abs]
  rw [e, sphere_dot_sq hN, hn] at hs
  have : normSq r / (2 * (N : ℝ)) = normSq r / (N : ℝ) / 2 := by ring
  linarith

/-- `(E_u ReLU(⟨r, u⟩))² ≤ |r|²/(4N)`. -/
lemma sphere_relu_mean_sq (hN : 1 ≤ N) (r : Fin N → ℝ) :
    (∫ u, relu (∑ i, r i * u i) ∂uniformSphere N) ^ 2 ≤ normSq r / (4 * (N : ℝ)) := by
  have := uniformSphere_isProbability N hN
  have hc : Continuous (fun u : Fin N → ℝ => relu (∑ i, r i * u i)) :=
    continuous_relu.comp (continuous_dotR r)
  have hn := sphere_neg hc
  simp_rw [dotR_neg] at hn
  have hc' : Continuous (fun u : Fin N → ℝ => relu (-∑ i, r i * u i)) :=
    continuous_relu.comp (continuous_dotR r).neg
  have hs := integral_add (sphere_cont_integrable hN hc) (sphere_cont_integrable hN hc')
  have e : (fun u : Fin N → ℝ => relu (∑ i, r i * u i) + relu (-∑ i, r i * u i)) =
      fun u => |∑ i, r i * u i| := by
    funext u
    have := relu_pow_add (∑ i, r i * u i) (n := 1) (by norm_num)
    simpa using this
  rw [e, hn] at hs
  have hca : Continuous (fun u : Fin N → ℝ => |∑ i, r i * u i|) := (continuous_dotR r).abs
  have h2 := sq_integral_le (ρ := uniformSphere N) (f := fun u => |∑ i, r i * u i|)
    (sphere_cont_integrable hN (hca.pow 2))
  simp_rw [sq_abs] at h2
  rw [sphere_dot_sq hN, hs] at h2
  have e2 : normSq r / (4 * (N : ℝ)) = normSq r / (N : ℝ) / 4 := by ring
  rw [e2]
  nlinarith

/-! ## The Gaussian vector: moments with `|ξ|²` -/

section gauss

variable {K : ℕ}

lemma gauss_normSq (K : ℕ) :
    Integrable (fun ξ : Fin K → ℝ => normSq ξ) (stdGauss (Fin K)) ∧
      ∫ ξ : Fin K → ℝ, normSq ξ ∂stdGauss (Fin K) = K := by
  have e : (fun ξ : Fin K → ℝ => normSq ξ) = fun ξ => ∑ i, (fun x : ℝ => x ^ 2) (ξ i) := rfl
  rw [e]
  unfold stdGauss
  refine ⟨pi_sum_integrable (ι := Fin K) (μ := gaussianReal 0 1) (f := fun x : ℝ => x ^ 2)
    (integrable_pow_gauss 2), ?_⟩
  rw [pi_sum (ι := Fin K) (μ := gaussianReal 0 1) (f := fun x : ℝ => x ^ 2)
    (integrable_pow_gauss 2), gaussMom_eq, Fintype.card_fin]
  norm_num [gaussMom]

lemma gauss_normSq_sq (K : ℕ) :
    Integrable (fun ξ : Fin K → ℝ => normSq ξ ^ 2) (stdGauss (Fin K)) ∧
      ∫ ξ : Fin K → ℝ, normSq ξ ^ 2 ∂stdGauss (Fin K) = (K : ℝ) ^ 2 + 2 * K := by
  have i4 : Integrable (fun x : ℝ => (x ^ 2) ^ 2) (gaussianReal 0 1) := by
    simp_rw [sq_sq]; exact integrable_pow_gauss 4
  have e : (fun ξ : Fin K → ℝ => normSq ξ ^ 2) =
      fun ξ => (∑ i, (fun x : ℝ => x ^ 2) (ξ i)) ^ 2 := rfl
  rw [e]
  unfold stdGauss
  refine ⟨pi_sum_sq_integrable (ι := Fin K) (μ := gaussianReal 0 1) (f := fun x : ℝ => x ^ 2)
    (integrable_pow_gauss 2) i4, ?_⟩
  rw [pi_sum_sq (ι := Fin K) (μ := gaussianReal 0 1) (f := fun x : ℝ => x ^ 2)
    (integrable_pow_gauss 2) i4]
  simp_rw [sq_sq]
  rw [gaussMom_eq, gaussMom_eq, Fintype.card_fin]
  have : Even 4 := by decide
  simp [gaussMom, this, Nat.doubleFactorial]
  ring

lemma stdGauss_rot_integral (O : Matrix (Fin K) (Fin K) ℝ) (hO : IsOrth O)
    {G : (Fin K → ℝ) → ℝ} (hG : Measurable G) :
    ∫ ξ, G (O.mulVec ξ) ∂stdGauss (Fin K) = ∫ ξ, G ξ ∂stdGauss (Fin K) := by
  have hmO : Measurable (fun u : Fin K → ℝ => O.mulVec u) := by fun_prop
  have h := integral_map (μ := stdGauss (Fin K)) hmO.aemeasurable (f := G) hG.aestronglyMeasurable
  rw [stdGauss_orth O hO] at h
  exact h.symm

lemma measurable_dotL (u : Fin K → ℝ) : Measurable (fun ξ : Fin K → ℝ => ∑ i, ξ i * u i) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _

lemma dotL_sq_le (ξ u : Fin K → ℝ) : (∑ i, ξ i * u i) ^ 2 ≤ normSq ξ * normSq u := by
  have h := abs_dotp_le_nrm ξ u
  have h2 : dotp ξ u ^ 2 ≤ (nrm ξ * nrm u) ^ 2 := by
    rw [← sq_abs (dotp ξ u)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rwa [mul_pow, nrm_sq, nrm_sq] at h2

lemma gauss_dot_normSq_integrable (u : Fin K → ℝ) :
    Integrable (fun ξ : Fin K → ℝ => (∑ i, ξ i * u i) ^ 2 * normSq ξ) (stdGauss (Fin K)) := by
  refine Integrable.mono' ((gauss_normSq_sq K).1.const_mul (normSq u))
    (((measurable_dotL u).pow_const 2).mul measurable_normSq).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ξ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (normSq_nonneg _))]
  have := mul_le_mul_of_nonneg_right (dotL_sq_le ξ u) (normSq_nonneg ξ)
  nlinarith

/-- `E (⟨ξ, u⟩)²·|ξ|² = K + 2` for a unit vector `u` and a standard Gaussian vector `ξ` of
`ℝ^K`. -/
lemma gauss_dot_normSq (hK : 1 ≤ K) {u : Fin K → ℝ} (hu : normSq u = 1) :
    ∫ ξ : Fin K → ℝ, (∑ i, ξ i * u i) ^ 2 * normSq ξ ∂stdGauss (Fin K) = (K : ℝ) + 2 := by
  classical
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  -- the value is the same at every coordinate vector
  have hcoord : ∀ k : Fin K, ∫ ξ : Fin K → ℝ, ξ k ^ 2 * normSq ξ ∂stdGauss (Fin K) =
      ∫ ξ : Fin K → ℝ, (∑ i, ξ i * u i) ^ 2 * normSq ξ ∂stdGauss (Fin K) := by
    intro k
    have he : normSq (Pi.single k (1 : ℝ) : Fin K → ℝ) = 1 := by
      unfold normSq
      simp [Pi.single_apply]
    obtain ⟨O, hO, hOu⟩ := exists_orth_map hK hu he
    have hG : Measurable (fun ξ : Fin K → ℝ => ξ k ^ 2 * normSq ξ) :=
      ((measurable_pi_apply k).pow_const 2).mul measurable_normSq
    rw [← stdGauss_rot_integral O.transpose hO.t hG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have e1 : normSq (O.transpose.mulVec ξ) = normSq ξ := orth_sumsq hO.t ξ
    have e2 : ∑ i, ξ i * u i = (O.transpose.mulVec ξ) k := by
      rw [← hOu, dot_mulVec' O ξ (Pi.single k 1)]
      simp [Pi.single_apply]
    change (O.transpose.mulVec ξ) k ^ 2 * normSq (O.transpose.mulVec ξ) =
      (∑ i, ξ i * u i) ^ 2 * normSq ξ
    rw [e1, e2]
  have hint : ∀ k : Fin K, Integrable (fun ξ : Fin K → ℝ => ξ k ^ 2 * normSq ξ)
      (stdGauss (Fin K)) := by
    intro k
    refine Integrable.mono' (gauss_normSq_sq K).1
      (((measurable_pi_apply k).pow_const 2).mul measurable_normSq).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (normSq_nonneg _)), sq (normSq ξ)]
    refine mul_le_mul_of_nonneg_right ?_ (normSq_nonneg ξ)
    exact Finset.single_le_sum (f := fun j => ξ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hsum : ∑ k : Fin K, ∫ ξ : Fin K → ℝ, ξ k ^ 2 * normSq ξ ∂stdGauss (Fin K) =
      (K : ℝ) ^ 2 + 2 * K := by
    rw [← integral_finsetSum _ fun k _ => hint k, ← (gauss_normSq_sq K).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    change ∑ k, ξ k ^ 2 * normSq ξ = normSq ξ ^ 2
    rw [← Finset.sum_mul, sq]
    rfl
  simp_rw [hcoord] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have : (K : ℝ) * (∫ ξ : Fin K → ℝ, (∑ i, ξ i * u i) ^ 2 * normSq ξ ∂stdGauss (Fin K)) =
      (K : ℝ) * ((K : ℝ) + 2) := by rw [hsum]; ring
  exact mul_left_cancel₀ hK'.ne' this

/-- `E ReLU(⟨ξ, u⟩)²·|ξ|² = (K + 2)/2` for a unit vector `u`. -/
lemma gauss_relu_normSq (hK : 1 ≤ K) {u : Fin K → ℝ} (hu : normSq u = 1) :
    Integrable (fun ξ : Fin K → ℝ => relu (∑ i, ξ i * u i) ^ 2 * normSq ξ) (stdGauss (Fin K)) ∧
      ∫ ξ : Fin K → ℝ, relu (∑ i, ξ i * u i) ^ 2 * normSq ξ ∂stdGauss (Fin K) =
        ((K : ℝ) + 2) / 2 := by
  have hG : Measurable (fun ξ : Fin K → ℝ => relu (∑ i, ξ i * u i) ^ 2 * normSq ξ) :=
    ((measurable_relu.comp (measurable_dotL u)).pow_const 2).mul measurable_normSq
  have hi : Integrable (fun ξ : Fin K → ℝ => relu (∑ i, ξ i * u i) ^ 2 * normSq ξ)
      (stdGauss (Fin K)) := by
    refine Integrable.mono' (gauss_dot_normSq_integrable u) hG.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (normSq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (relu_sq_le _) (normSq_nonneg ξ)
  refine ⟨hi, ?_⟩
  have hneg := stdGauss_rot_integral _ (isOrth_neg_one K) hG
  have e0 : ∀ ξ : Fin K → ℝ, (-1 : Matrix (Fin K) (Fin K) ℝ).mulVec ξ = -ξ := fun ξ => by
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  have e1 : ∀ ξ : Fin K → ℝ, relu (∑ i, (-ξ) i * u i) ^ 2 * normSq (-ξ) =
      relu (-∑ i, ξ i * u i) ^ 2 * normSq ξ := by
    intro ξ
    have a : ∑ i, (-ξ) i * u i = -∑ i, ξ i * u i := by simp [Finset.sum_neg_distrib]
    have b : normSq (-ξ) = normSq ξ := by unfold normSq; simp
    rw [a, b]
  simp_rw [e0, e1] at hneg
  have hi' : Integrable (fun ξ : Fin K → ℝ => relu (-∑ i, ξ i * u i) ^ 2 * normSq ξ)
      (stdGauss (Fin K)) := by
    refine Integrable.mono' (gauss_dot_normSq_integrable u)
      (((measurable_relu.comp (measurable_dotL u).neg).pow_const 2).mul
        measurable_normSq).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (normSq_nonneg _))]
    have := relu_sq_le (-∑ i, ξ i * u i)
    rw [neg_sq] at this
    exact mul_le_mul_of_nonneg_right this (normSq_nonneg ξ)
  have hs := integral_add hi hi'
  have e : (fun ξ : Fin K → ℝ => relu (∑ i, ξ i * u i) ^ 2 * normSq ξ +
      relu (-∑ i, ξ i * u i) ^ 2 * normSq ξ) = fun ξ => (∑ i, ξ i * u i) ^ 2 * normSq ξ := by
    funext ξ
    rw [← add_mul, relu_pow_add _ (by norm_num), sq_abs]
  rw [e, gauss_dot_normSq hK hu, hneg] at hs
  linarith

end gauss

/-! ## `Γ*` as a sum over the rows of `M₁` -/

/-- **`Γ* = S₁/N`**: `Γ* = Σ_j |row_j(M₁)|²/(mN)`. -/
theorem GamS_rows (hN : 1 ≤ N) (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    GamS M₁ = ∑ j, normSq (rowOf j M₁) / ((m : ℝ) * N) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin m)), Integrable
      (fun u : Fin N → ℝ => relu (∑ i, rowOf j M₁ i * u i) ^ 2) (uniformSphere N) := fun j _ =>
    sphere_cont_integrable hN ((continuous_relu.comp (continuous_dotR _)).pow 2)
  have e : ∀ u : Fin N → ℝ, alphaU M₁ u =
      2 / (m : ℝ) * ∑ j, relu (∑ i, rowOf j M₁ i * u i) ^ 2 := fun u => rfl
  unfold GamS
  simp_rw [e]
  rw [integral_const_mul, integral_finsetSum _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sphere_relu_sq hN]
  field_simp

/-- **`E_{M₁}(Γ* − γ)² = 2γ²/(Nm)`** (in the form `‖Γ* − γ‖₂ ≤ γ√(2/(Nm))`). -/
theorem GamS_L2x (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ : Matrix (Fin m) (Fin N) ℝ => GamS M₁ - 2 / (N : ℝ))
      (2 / (N : ℝ) * √(2 / ((N : ℝ) * m))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  set v : ℝ := 2 / (N : ℝ) with hvdef
  let f : (Fin N → ℝ) → ℝ := fun r => normSq r / ((m : ℝ) * N)
  have hf : Measurable f := measurable_normSq.div_const _
  have hsc : ∀ ξ : Fin N → ℝ, normSq (√v • ξ) = v * normSq ξ := by
    intro ξ
    rw [normSq_smul, Real.sq_sqrt hv]
  have ef : ∀ ξ : Fin N → ℝ, f (√v • ξ) = v / ((m : ℝ) * N) * normSq ξ := by
    intro ξ
    simp only [f]
    rw [hsc]
    ring
  have ef2 : ∀ ξ : Fin N → ℝ, f (√v • ξ) ^ 2 = (v / ((m : ℝ) * N)) ^ 2 * normSq ξ ^ 2 := by
    intro ξ
    rw [ef, mul_pow]
  have i1 : Integrable (fun ξ : Fin N → ℝ => f (√v • ξ)) (stdGauss (Fin N)) := by
    simp_rw [ef]
    exact (gauss_normSq N).1.const_mul _
  have e1 : ∫ ξ : Fin N → ℝ, f (√v • ξ) ∂stdGauss (Fin N) = v / (m : ℝ) := by
    simp_rw [ef]
    rw [integral_const_mul, (gauss_normSq N).2]
    field_simp
  have i2 : Integrable (fun ξ : Fin N → ℝ => f (√v • ξ) ^ 2) (stdGauss (Fin N)) := by
    simp_rw [ef2]
    exact (gauss_normSq_sq N).1.const_mul _
  have e2 : ∫ ξ : Fin N → ℝ, f (√v • ξ) ^ 2 ∂stdGauss (Fin N) =
      (v / (m : ℝ)) ^ 2 * (1 + 2 / (N : ℝ)) := by
    simp_rw [ef2]
    rw [integral_const_mul, (gauss_normSq_sq N).2]
    field_simp
  obtain ⟨iQ, eQ⟩ := rows_sum_sq (m := m) v f hf i2
  rw [e1, e2] at eQ
  have hG : ∀ M₁ : Matrix (Fin m) (Fin N) ℝ, GamS M₁ = ∑ j, f (rowOf j M₁) :=
    fun M₁ => GamS_rows hN hm M₁
  have hrow : ∀ j : Fin m, Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => f (rowOf j M₁))
      (gaussMat m N v) := fun j => (row_integrable_iff (m := m) v j hf).mpr i1
  have iS : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => ∑ j, f (rowOf j M₁))
      (gaussMat m N v) := integrable_finsetSum _ fun j _ => hrow j
  have eS : ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, ∑ j, f (rowOf j M₁) ∂gaussMat m N v = v := by
    rw [integral_finsetSum _ fun j _ => hrow j]
    simp_rw [row_integral (m := m) v _ hf, e1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨iC, eC⟩ := integral_sq_sub_const iS iQ v
  simp_rw [hG]
  refine ⟨(iS.sub (integrable_const _)).aestronglyMeasurable, iC, ?_⟩
  rw [eC, eQ, eS, mul_pow, Real.sq_sqrt (by positivity)]
  refine le_of_eq ?_
  field_simp
  ring

/-! ## The covariance term with the row independence of `M₁` -/

/-- `g(r) = E_u ReLU(⟨r, u⟩)`: the coordinate of `h̄₁` as a function of the row. -/
noncomputable def gfun (N : ℕ) (r : Fin N → ℝ) : ℝ := ∫ u, relu (∑ i, r i * u i) ∂uniformSphere N

lemma continuous_relu_dot2 :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => relu (∑ i, p.1 i * p.2 i)) :=
  continuous_relu.comp (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd))

lemma measurable_gfun (hN : 1 ≤ N) : Measurable (gfun N) := by
  have := uniformSphere_isProbability N hN
  exact (continuous_relu_dot2.measurable.stronglyMeasurable.integral_prod_right').measurable

lemma gfun_nonneg (r : Fin N → ℝ) : 0 ≤ gfun N r := integral_nonneg fun _ => relu_nonneg _

/-- **The covariance term**, `c = t⟨h₁(u₀), h̄₁⟩`: `E_{M₁}(c − γ q₁)² ≤ γ²(1 + 2/N)/(2m)`. -/
theorem cov_L2x (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
        2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁) - 2 / (N : ℝ) * q1 u0)
      (2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m))) := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  set v : ℝ := 2 / (N : ℝ) with hvdef
  have hsv : 0 ≤ √v := Real.sqrt_nonneg _
  let f : (Fin N → ℝ) → ℝ := fun r => relu (∑ i, r i * u0 i) * gfun N r
  have hf : Measurable f := (measurable_relu.comp (measurable_dotL u0)).mul (measurable_gfun hN)
  have hfs : Measurable (fun ξ : Fin N → ℝ => f (√v • ξ)) := hf.comp (measurable_const_smul _)
  -- the second moment of one row
  have hdot : ∀ (ξ w : Fin N → ℝ), ∑ i, (√v • ξ) i * w i = √v * ∑ i, ξ i * w i := by
    intro ξ w
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_assoc]
  have hsc : ∀ ξ : Fin N → ℝ, normSq (√v • ξ) = v * normSq ξ := by
    intro ξ
    rw [normSq_smul, Real.sq_sqrt hv]
  have hpt : ∀ ξ : Fin N → ℝ, f (√v • ξ) ^ 2 ≤
      v ^ 2 / (4 * (N : ℝ)) * (relu (∑ i, ξ i * u0 i) ^ 2 * normSq ξ) := by
    intro ξ
    simp only [f]
    rw [mul_pow, hdot, relu_mul_of_nonneg hsv, mul_pow, Real.sq_sqrt hv]
    have hg := sphere_relu_mean_sq hN (√v • ξ)
    rw [hsc] at hg
    have h0 : 0 ≤ v * relu (∑ i, ξ i * u0 i) ^ 2 := mul_nonneg hv (sq_nonneg _)
    calc v * relu (∑ i, ξ i * u0 i) ^ 2 * gfun N (√v • ξ) ^ 2
        ≤ v * relu (∑ i, ξ i * u0 i) ^ 2 * (v * normSq ξ / (4 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hg h0
      _ = _ := by ring
  obtain ⟨iR, eR⟩ := gauss_relu_normSq hN hu0
  have i2 : Integrable (fun ξ : Fin N → ℝ => f (√v • ξ) ^ 2) (stdGauss (Fin N)) := by
    refine Integrable.mono' (iR.const_mul (v ^ 2 / (4 * (N : ℝ))))
      (hfs.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ξ
  have u2 : ∫ ξ : Fin N → ℝ, f (√v • ξ) ^ 2 ∂stdGauss (Fin N) ≤
      v ^ 2 / (4 * (N : ℝ)) * (((N : ℝ) + 2) / 2) := by
    rw [← eR, ← integral_const_mul]
    exact integral_mono i2 (iR.const_mul _) hpt
  have i1 : Integrable (fun ξ : Fin N → ℝ => f (√v • ξ)) (stdGauss (Fin N)) :=
    ((memLp_two_iff_integrable_sq hfs.aestronglyMeasurable).mpr i2).integrable one_le_two
  -- the mean of one row, by Fubini and the row formula
  have e1 : ∫ ξ : Fin N → ℝ, f (√v • ξ) ∂stdGauss (Fin N) = v / 2 * q1 u0 := by
    let H : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun p =>
      relu (∑ i, (√v • p.1) i * u0 i) * relu (∑ i, (√v • p.1) i * p.2 i)
    have hHc : Continuous H := by
      have hs : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => √v • p.1) :=
        continuous_fst.const_smul (√v)
      have h1 : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ∑ i, (√v • p.1) i * u0 i) :=
        continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hs).mul continuous_const
      have h2 : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ∑ i, (√v • p.1) i * p.2 i) :=
        continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hs).mul
          ((continuous_apply i).comp continuous_snd)
      exact (continuous_relu.comp h1).mul (continuous_relu.comp h2)
    have hin : ∀ ξ : Fin N → ℝ, ∫ u, H (ξ, u) ∂uniformSphere N = f (√v • ξ) := by
      intro ξ
      simp only [H, f, gfun]
      rw [integral_const_mul]
    have hHi : Integrable H ((stdGauss (Fin N)).prod (uniformSphere N)) := by
      rw [integrable_prod_iff hHc.aestronglyMeasurable]
      constructor
      · exact Filter.Eventually.of_forall fun ξ =>
          sphere_cont_integrable hN (hHc.comp (continuous_const.prodMk continuous_id))
      · have e : (fun ξ : Fin N → ℝ => ∫ u, ‖H (ξ, u)‖ ∂uniformSphere N) =
            fun ξ => f (√v • ξ) := by
          funext ξ
          rw [← hin ξ]
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [H]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (relu_nonneg _) (relu_nonneg _))]
        rw [e]
        exact i1
    have hsw := integral_prod_symm _ hHi
    rw [integral_prod _ hHi] at hsw
    simp_rw [hin] at hsw
    rw [hsw]
    have hrow : ∀ᵐ u ∂uniformSphere N, ∫ ξ : Fin N → ℝ, H (ξ, u) ∂stdGauss (Fin N) =
        v / 2 * kappa (dotp u0 u) := by
      filter_upwards [uniformSphere_ae_sphere N] with u hu
      have hu' : normSq u = 1 := hu
      have h2 := (rowPair137 (K := N) hv u0 u).2.1
      rw [kernelPhi_eq_psi, psi_unit _ hu0 hu'] at h2
      have e3 : v / 2 * kappa (dotp u0 u) = v * kappa (dotp u0 u) / 2 := by ring
      rw [e3]
      exact h2
    rw [integral_congr_ae hrow, integral_const_mul]
    rfl
  -- the sum over the rows
  obtain ⟨iQ, eQ⟩ := rows_sum_sq (m := m) v f hf i2
  have hrowi : ∀ j : Fin m, Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => f (rowOf j M₁))
      (gaussMat m N v) := fun j => (row_integrable_iff (m := m) v j hf).mpr i1
  have iS : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => ∑ j, f (rowOf j M₁))
      (gaussMat m N v) := integrable_finsetSum _ fun j _ => hrowi j
  have eS : ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, ∑ j, f (rowOf j M₁) ∂gaussMat m N v =
      (m : ℝ) * (v / 2 * q1 u0) := by
    rw [integral_finsetSum _ fun j _ => hrowi j]
    simp_rw [row_integral (m := m) v _ hf, e1]
    simp
  obtain ⟨iC, eC⟩ := integral_sq_sub_const iS iQ ((m : ℝ) * (v / 2 * q1 u0))
  have hsum : ∀ M₁ : Matrix (Fin m) (Fin N) ℝ,
      2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁) - v * q1 u0 =
        2 / (m : ℝ) * (∑ j, f (rowOf j M₁) - (m : ℝ) * (v / 2 * q1 u0)) := by
    intro M₁
    have e : dotp (reluV (M₁.mulVec u0)) (h1bar M₁) = ∑ j, f (rowOf j M₁) := rfl
    rw [e]
    field_simp
  simp_rw [hsum]
  refine ⟨((iS.sub (integrable_const _)).const_mul _).aestronglyMeasurable, ?_, ?_⟩
  · simp_rw [mul_pow]
    exact iC.const_mul _
  · simp_rw [mul_pow]
    rw [integral_const_mul, eC, eQ, eS, e1, Real.sq_sqrt (by positivity)]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := hm'.le
    have h3 := mul_le_mul_of_nonneg_left u2 hm0
    have h4 : (m : ℝ) * (∫ ξ : Fin N → ℝ, f (√v • ξ) ^ 2 ∂stdGauss (Fin N)) +
        (m : ℝ) * ((m : ℝ) - 1) * (v / 2 * q1 u0) ^ 2 -
        2 * ((m : ℝ) * (v / 2 * q1 u0)) * ((m : ℝ) * (v / 2 * q1 u0)) +
        ((m : ℝ) * (v / 2 * q1 u0)) ^ 2 ≤
        (m : ℝ) * (v ^ 2 / (4 * (N : ℝ)) * (((N : ℝ) + 2) / 2)) := by
      nlinarith [mul_nonneg hm0 (sq_nonneg (v / 2 * q1 u0))]
    refine (mul_le_mul_of_nonneg_left h4 (sq_nonneg _)).trans (le_of_eq ?_)
    rw [hvdef]
    field_simp
    ring

/-! ## The computed centre in the form of the paper -/

/-- **`c_N = E_u ReLU(u₁)`**: the constant of `h̄₁ = c_N·(|row_j(M₁)|)_j`. -/
noncomputable def cN (N : ℕ) : ℝ := gfun N (e0 N)

lemma gfun_unit (hN : 1 ≤ N) {ρ : Fin N → ℝ} (hρ : normSq ρ = 1) : gfun N ρ = cN N := by
  obtain ⟨O, hO, hOe⟩ := exists_orth_map hN hρ (normSq_e0 hN)
  have hmO : Measurable (fun u : Fin N → ℝ => O.transpose.mulVec u) := by fun_prop
  have hc : Continuous (fun u : Fin N → ℝ => relu (∑ i, e0 N i * u i)) :=
    continuous_relu.comp (continuous_dotR _)
  have h := integral_map (μ := uniformSphere N) hmO.aemeasurable
    (f := fun u => relu (∑ i, e0 N i * u i)) hc.aestronglyMeasurable
  rw [uniformSphere_orth O.transpose hO.t] at h
  unfold cN gfun
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : ∑ i, ρ i * u i = ∑ i, e0 N i * (O.transpose.mulVec u) i := by
    rw [← hOe]
    have := dot_mulVec' O u (e0 N)
    calc ∑ i, (O.mulVec (e0 N)) i * u i = ∑ i, u i * (O.mulVec (e0 N)) i :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∑ j, (O.transpose.mulVec u) j * e0 N j := this
      _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _
  change relu (∑ i, ρ i * u i) = relu (∑ i, e0 N i * (O.transpose.mulVec u) i)
  rw [e]

/-- `E_u ReLU(⟨r, u⟩) = c_N·|r|`. -/
theorem gfun_eq (hN : 1 ≤ N) (r : Fin N → ℝ) : gfun N r = cN N * nrm r := by
  by_cases h0 : normSq r = 0
  · have hr : r = 0 := normSq_eq_zero h0
    have hn : nrm r = 0 := by unfold nrm; rw [h0, Real.sqrt_zero]
    rw [hn, mul_zero, hr]
    unfold gfun
    simp [relu]
  · have hpos : 0 < normSq r := lt_of_le_of_ne (normSq_nonneg r) (Ne.symm h0)
    have hc : 0 < nrm r := Real.sqrt_pos.mpr hpos
    set ρ : Fin N → ℝ := (nrm r)⁻¹ • r with hρdef
    have hρ : normSq ρ = 1 := by
      rw [hρdef, normSq_smul, inv_pow, nrm_sq]
      field_simp
    have hr : r = nrm r • ρ := by
      rw [hρdef, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [← gfun_unit hN hρ]
    unfold gfun
    rw [mul_comm, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : ∑ i, r i * u i = nrm r * ∑ i, ρ i * u i := by
      conv_lhs => rw [hr]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [mul_assoc]
    change relu (∑ i, r i * u i) = nrm r * relu (∑ i, ρ i * u i)
    rw [e, relu_mul_of_nonneg hc.le]

/-- **The centre of the first layer in the form of the paper**:
`h̄₁ = c_N·(|row_j(M₁)|)_j`. -/
theorem h1bar_eq (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ) (j : Fin m) :
    h1bar M₁ j = cN N * nrm (rowOf j M₁) := by
  rw [← gfun_eq hN]
  rfl

/-! ## The sharper constant -/

/-- The sharper constant of H2(b):
`cHat2 N m² = (6(1 + 5/m) + (κ(0)(√5 + √(2/N)) + √((1 + 2/N)/2))²)/m`. -/
noncomputable def cHat2 (N m : ℕ) : ℝ :=
  √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ) +
    (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ))

/-- **Lemma H2(b)** (`onW16c-cx.md` §2), every `N, m ≥ 1`: for a unit vector `u₀`,
`‖T̂(u₀) − γ·κ(q₁)‖_{L²(θ)} ≤ γ·cHat2 N m`. -/
theorem hatFluct2_pt (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    L2le (hidGauss N m)
      (fun θ => That N m u0 θ - 2 / (N : ℝ) * kappa (q1 u0)) (2 / (N : ℝ) * cHat2 N m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have key := hatFluct_core hN hm hu0 (aG := 2 / (N : ℝ) * √(2 / ((N : ℝ) * m)))
    (aC := 2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m))) (by positivity) (by positivity)
    (GamS_L2x (N := N) (m := m) hN hm) (cov_L2x (m := m) hN hm hu0)
  refine key.congr_bound ?_
  unfold cHat2
  have hsm : √(m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have r1 : √(5 / (m : ℝ)) = √5 / √(m : ℝ) := Real.sqrt_div (by norm_num) _
  have r2 : √(2 / ((N : ℝ) * m)) = √(2 / (N : ℝ)) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have r3 : √((1 + 2 / (N : ℝ)) / (2 * m)) = √((1 + 2 / (N : ℝ)) / 2) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have e5 : kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + 2 / (N : ℝ) * √(2 / ((N : ℝ) * m))) +
      2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m)) =
      2 / (N : ℝ) * ((kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) / √(m : ℝ)) := by
    rw [r1, r2, r3]
    ring
  have hs1 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 * (1 + 5 / (m : ℝ)) / (m : ℝ) by positivity)
  have hs2 := Real.sq_sqrt hm'.le
  have e6 : (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) ^ 2 +
      (kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + 2 / (N : ℝ) * √(2 / ((N : ℝ) * m))) +
        2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m))) ^ 2 =
      (2 / (N : ℝ)) ^ 2 * (6 * (1 + 5 / (m : ℝ)) / (m : ℝ) +
        (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ)) := by
    rw [e5]
    calc (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) ^ 2 +
          (2 / (N : ℝ) * ((kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) /
            √(m : ℝ))) ^ 2
        = (2 / (N : ℝ)) ^ 2 * (√(6 * (1 + 5 / (m : ℝ)) / (m : ℝ)) ^ 2 +
            (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 /
              √(m : ℝ) ^ 2) := by ring
      _ = _ := by rw [hs1, hs2]
  rw [e6, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hγ.le]

/-- `Var_θ T̂(u₀) ≤ (γ·cHat2 N m)²` for a unit vector `u₀`. -/
theorem hatFluct2_var (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    Var[That N m u0; hidGauss N m] ≤ (2 / (N : ℝ) * cHat2 N m) ^ 2 :=
  variance_le_of_L2le (hatFluct2_pt hN hm hu0)

/-- **Lemma H2(b), the consequence**, every `N, m ≥ 1`: `E_θ Var_u T̂ ≤ (γ·cHat2 N m)²`. -/
theorem innerFluct137_hat2_gen (hN : 1 ≤ N) (hm : 1 ≤ m) :
    ∫ θ, Var[fun u => That N m u θ; uniformSphere N] ∂hidGauss N m ≤
      (2 / (N : ℝ) * cHat2 N m) ^ 2 := by
  have h := hatFluct2_pt (m := m) hN hm (normSq_e0 hN)
  exact (exchange137 hN (measurable_That hN) exch_That (normSq_e0 hN) h.int_sq).trans h.le

/-- **Lemma H2(b), over the input and `θ`**: with the constant `a = γ·κ(q₁(e₀))`,
`E_θ E_u (T̂(u) − a)² ≤ (γ·cHat2 N m)²`. -/
theorem hatFluct2_joint (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun p : (Fin N → ℝ) × HidParam N m =>
        (That N m p.1 p.2 - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2)
        ((uniformSphere N).prod (hidGauss N m)) ∧
      ∫ p, (That N m p.1 p.2 - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2
          ∂((uniformSphere N).prod (hidGauss N m)) ≤ (2 / (N : ℝ) * cHat2 N m) ^ 2 := by
  have h := hatFluct2_pt (m := m) hN hm (normSq_e0 hN)
  have hYm : Measurable (Function.uncurry fun (u : Fin N → ℝ) (θ : HidParam N m) =>
      (That N m u θ - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2) :=
    ((measurable_That hN).sub_const _).pow_const 2
  have hY : Exch (fun (u : Fin N → ℝ) (θ : HidParam N m) =>
      (That N m u θ - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2) :=
    exch_That.comp fun x => (x - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2
  obtain ⟨h1, h2⟩ := exch_avg hN hYm hY (normSq_e0 hN) h.int_sq
  exact ⟨h1, h2.trans_le h.le⟩

/-- `cHat2 N m² ≤ 8.03/m` for `N ≥ 8192`, `m ≥ 10⁶`. -/
lemma cHat2_sq_le {N m : ℕ} (hN : 8192 ≤ N) (hm : 1000000 ≤ m) :
    cHat2 N m ^ 2 ≤ 803 / 100 / (m : ℝ) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (8192 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have k1 := kappa_zero_le
  have k0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have s5 : √(5 : ℝ) ≤ 22361 / 10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have s50 : 0 ≤ √(5 : ℝ) := Real.sqrt_nonneg _
  have hNle : 2 / (N : ℝ) ≤ 2 / 8192 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have sN : √(2 / (N : ℝ)) ≤ 1 / 64 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sN0 : 0 ≤ √(2 / (N : ℝ)) := Real.sqrt_nonneg _
  have sH : √((1 + 2 / (N : ℝ)) / 2) ≤ 7072 / 10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sH0 : 0 ≤ √((1 + 2 / (N : ℝ)) / 2) := Real.sqrt_nonneg _
  unfold cHat2
  rw [Real.sq_sqrt (by positivity)]
  have h1 : 5 / (m : ℝ) ≤ 5 / 1000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have h3 : kappa 0 * (√5 + √(2 / (N : ℝ))) ≤ 31831 / 100000 * (22361 / 10000 + 1 / 64) :=
    mul_le_mul k1 (by linarith) (by positivity) (by norm_num)
  have h2 : (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 ≤
      (31831 / 100000 * (22361 / 10000 + 1 / 64) + 7072 / 10000) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  nlinarith

lemma gamma_cHat2_le {n : ℕ} (hn : 4096 ≤ n) :
    (2 / ((2 * n : ℕ) : ℝ) * cHat2 (2 * n) (mW n)) ^ 2 ≤
      803 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) := by
  have h := cHat2_sq_le (N := 2 * n) (by omega) (mW_ge_million hn)
  have e : 803 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) =
      (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (803 / 100 / (mW n : ℝ)) := by ring
  rw [mul_pow, e]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **Lemma H2(b) for the World network of the Focus** (`N = 2n`, `m = mW n`, `n ≥ 4096`):
`Var_θ T̂(u₀) ≤ 8.03·γ²/m` for a unit vector `u₀` (the paper: `8.3`). -/
theorem hatFluct137_var2 {n : ℕ} (hn : 4096 ≤ n) {u0 : Fin (2 * n) → ℝ} (hu0 : normSq u0 = 1) :
    Var[That (2 * n) (mW n) u0; hidGauss (2 * n) (mW n)] ≤
      803 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) :=
  (hatFluct2_var (by omega) (one_le_mW (by omega)) hu0).trans (gamma_cHat2_le hn)

/-- **`innerFluct137_hat2`** (Lemma H2(b), the consequence, for the computed centre
`b̂ = ψ_s(M₂ h̄₁)`): `N = 2n`, `m = mW n`, every `n ≥ 4096`: `E_θ Var_u T̂ ≤ 8.03·γ²/m`. -/
theorem innerFluct137_hat2 {n : ℕ} (hn : 4096 ≤ n) :
    ∫ θ, Var[fun u => That (2 * n) (mW n) u θ; uniformSphere (2 * n)]
        ∂hidGauss (2 * n) (mW n) ≤
      803 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) :=
  (innerFluct137_hat2_gen (by omega) (one_le_mW (by omega))).trans (gamma_cHat2_le hn)

end BstLean.Part137
