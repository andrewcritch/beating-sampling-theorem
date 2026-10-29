import BstLean.Part151Poinc
import BstLean.Part151SA

/-!
# Part 151: forms of the Poincaré inequality for a Lipschitz function

* `poincare_lip_scaled`: for `X = √v·ξ` (independent `N(0, v)` coordinates):
  `Var g(X) ≤ v·E|∇g(X)|²`.
* `poincare_mat`: for a Gaussian matrix `M ∼ gaussMat m k v` and `g` Lipschitz for the Frobenius
  norm: `Var g(M) ≤ v·E|∇g|²`, the gradient taken in the entries (written on the index type
  `Fin m × Fin k`, because `Matrix` has no norm instance).
* `poincare_mean_pi`: for `z : ℝⁿ → ℝ^m` with Lipschitz coordinates and `k ≥ 1` independent
  standard Gaussian vectors `η_j`: `E|(1/k)Σ_j z(η_j) − E z|² ≤ (1/k)·E Σ_i |∇z_i|²` (the form
  used in Lemma SA (i) of `proofs/option-n/theorem5-09-fluctuation.tex`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip matLip_continuous)

section scaled

variable {ι : Type} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {L : ℝ}

omit [DecidableEq ι] in
lemma EuLip.comp_smul (hL : EuLip g L) (c : ℝ) : EuLip (fun ξ => g (c • ξ)) (|c| * L) := by
  intro x y
  have h := hL (c • x) (c • y)
  have e : ∑ i, ((c • x) i - (c • y) i) ^ 2 = c ^ 2 * ∑ i, (x i - y i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- `|∇(g(c·))|²(ξ) = c²·|∇g|²(cξ)`. -/
lemma gradSq_comp_smul (g : (ι → ℝ) → ℝ) (c : ℝ) (ξ : ι → ℝ) :
    gradSq (fun ζ => g (c • ζ)) ξ = c ^ 2 * gradSq g (c • ξ) := by
  by_cases hc : c = 0
  · subst hc
    unfold gradSq
    have e : (fun ζ : ι → ℝ => g ((0 : ℝ) • ζ)) = fun _ => g 0 := by
      funext ζ; simp
    rw [e]
    simp
  · set iso : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) with hiso
    have hiso_apply : ∀ x : ι → ℝ, iso x = c • x := fun x => rfl
    have e : (fun ζ : ι → ℝ => g (c • ζ)) = g ∘ iso := by
      funext ζ; simp [hiso_apply]
    unfold gradSq
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iso.comp_right_fderiv]
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply]
    rw [hiso_apply, hiso_apply, map_smul, smul_eq_mul, mul_pow]

/-- **The Poincaré inequality for independent `N(0, v)` coordinates**: with `X = √v·ξ`,
`Var g(X) ≤ v·E|∇g(X)|²`, for `g` Lipschitz for the Euclidean norm. -/
theorem poincare_lip_scaled (hL0 : 0 ≤ L) (hL : EuLip g L) {v : ℝ} (hv : 0 ≤ v) :
    ∫ ξ, (g (√v • ξ) - ∫ ζ, g (√v • ζ) ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      v * ∫ ξ, gradSq g (√v • ξ) ∂stdGauss ι := by
  have hL' := EuLip.comp_smul hL (√v)
  have h := poincare_lip (mul_nonneg (abs_nonneg _) hL0) hL'
  refine h.trans (le_of_eq ?_)
  have e : ∀ ξ : ι → ℝ, ∑ i, (fderiv ℝ (fun ζ => g (√v • ζ)) ξ (Pi.single i 1)) ^ 2 =
      v * gradSq g (√v • ξ) := by
    intro ξ
    have := gradSq_comp_smul g (√v) ξ
    rw [Real.sq_sqrt hv] at this
    exact this
  simp_rw [e]
  rw [integral_const_mul]

end scaled

/-! ## A Gaussian matrix -/

section mat

variable {m k : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L : ℝ}

/-- **The Poincaré inequality for a Lipschitz function of a Gaussian matrix**
`M ∼ gaussMat m k v` (independent `N(0, v)` entries): `Var g(M) ≤ v·E|∇g(M)|²`. The gradient is
taken in the entries: `gradSq (g ∘ unflat)` on the index type `Fin m × Fin k`, at the point
`√v·ξ` (the entries of `M`). -/
theorem poincare_mat (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) :
    ∫ M, (g M - ∫ M', g M' ∂gaussMat m k v) ^ 2 ∂gaussMat m k v ≤
      v * ∫ ξ, gradSq (fun ζ : Fin m × Fin k → ℝ => g (unflat ζ)) (√v • ξ)
        ∂stdGauss (Fin m × Fin k) := by
  have hgc := matLip_continuous hL
  set T : (Fin m × Fin k → ℝ) → Matrix (Fin m) (Fin k) ℝ :=
    fun ξ => Matrix.of fun i j => Real.sqrt v * ξ (i, j) with hT
  have mT : Measurable T := measurable_ofFlat _
  have hTu : ∀ ξ : Fin m × Fin k → ℝ, T ξ = unflat (√v • ξ) := fun ξ => rfl
  have hg' : EuLip (fun ζ : Fin m × Fin k → ℝ => g (unflat ζ)) L := by
    intro x y
    have h := hL (unflat x) (unflat y)
    have e : ∑ i, ∑ j, (unflat x i j - unflat y i j) ^ 2 = ∑ p, (x p - y p) ^ 2 := by
      rw [Fintype.sum_prod_type]
      rfl
    rwa [e] at h
  have h := poincare_lip_scaled hL0 hg' hv
  have eI : ∫ M, g M ∂gaussMat m k v = ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) := by
    unfold gaussMat
    exact integral_map mT.aemeasurable hgc.measurable.aestronglyMeasurable
  have eV : ∫ M, (g M - ∫ M', g M' ∂gaussMat m k v) ^ 2 ∂gaussMat m k v =
      ∫ ξ, (g (T ξ) - ∫ M', g M' ∂gaussMat m k v) ^ 2 ∂stdGauss (Fin m × Fin k) := by
    conv_lhs => unfold gaussMat
    exact integral_map mT.aemeasurable
      ((hgc.measurable.sub measurable_const).pow_const 2).aestronglyMeasurable
  rw [eV, eI]
  simp_rw [hTu]
  exact h

end mat

/-! ## A mean of independent copies of a vector-valued Lipschitz map -/

section mean

variable {n m : ℕ}

/-- **The variance of a mean of `k` independent copies of a Lipschitz map of a Gaussian vector**:
`E|(1/k)Σ_j z(η_j) − E z|² ≤ (1/k)·E Σ_i |∇z_i|²`. -/
theorem poincare_mean_pi {z : (Fin n → ℝ) → Fin m → ℝ} {L : Fin m → ℝ} (hL0 : ∀ i, 0 ≤ L i)
    (hL : ∀ i, EuLip (fun y => z y i) (L i)) {k : ℕ} (hk : 1 ≤ k) :
    ∫ η, ∑ i, ((k : ℝ)⁻¹ * ∑ j, z (η j) i - ∫ y, z y i ∂stdGauss (Fin n)) ^ 2
        ∂(Measure.pi fun _ : Fin k => stdGauss (Fin n)) ≤
      (1 / (k : ℝ)) * ∫ y, ∑ i, gradSq (fun x => z x i) y ∂stdGauss (Fin n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hcoord : ∀ i : Fin m,
      Integrable (fun η : Fin k → Fin n → ℝ =>
        ((k : ℝ)⁻¹ * ∑ j, z (η j) i - ∫ y, z y i ∂stdGauss (Fin n)) ^ 2)
        (Measure.pi fun _ : Fin k => stdGauss (Fin n)) ∧
      ∫ η, ((k : ℝ)⁻¹ * ∑ j, z (η j) i - ∫ y, z y i ∂stdGauss (Fin n)) ^ 2
        ∂(Measure.pi fun _ : Fin k => stdGauss (Fin n)) ≤
        (∫ y, gradSq (fun x => z x i) y ∂stdGauss (Fin n)) / k := by
    intro i
    set mi := ∫ y, z y i ∂stdGauss (Fin n) with hmi
    have h2 := lip_memLp (hL0 i) (hL i)
    have hc : MemLp (fun y : Fin n → ℝ => z y i - mi) 2 (stdGauss (Fin n)) :=
      h2.sub (memLp_const mi)
    obtain ⟨hi, hle⟩ := mean_sq_pi (stdGauss (Fin n)) hc hk
    have hint : Integrable (fun y : Fin n → ℝ => z y i) (stdGauss (Fin n)) :=
      h2.integrable (by norm_num)
    have e0 : ∫ y, (z y i - mi) ∂stdGauss (Fin n) = 0 := by
      rw [integral_sub hint (integrable_const _)]
      simp [hmi]
    have e1 : ∀ η : Fin k → Fin n → ℝ,
        (k : ℝ)⁻¹ * ∑ j, (z (η j) i - mi) - ∫ y, (z y i - mi) ∂stdGauss (Fin n) =
          (k : ℝ)⁻¹ * ∑ j, z (η j) i - mi := by
      intro η
      rw [e0, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_zero]
      field_simp
    simp_rw [e1] at hi hle
    refine ⟨hi, hle.trans ?_⟩
    exact div_le_div_of_nonneg_right (poincare_lip (hL0 i) (hL i)) hk0.le
  rw [integral_finsetSum _ fun i _ => (hcoord i).1,
    integral_finsetSum _ fun i _ => gradSq_integrable (hL0 i) (hL i), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (hcoord i).2.trans (le_of_eq ?_)
  ring

end mean

end BstLean.Part151
