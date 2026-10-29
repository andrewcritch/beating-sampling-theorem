import BstLean.Part80VarBound
import BstLean.Part78Poincare2

/-!
# Part 80: the conditional variance bound with the first chaos separated (`varBoundA3`)

`Var_W V ≤ 2 Γ ((2+η) S + ((1+1/η)(4184/1000)(8·1733/1000) + 8) ‖H‖_F²) V̄`, from
`BstLean.Part78.poincareMv2`.
-/

namespace BstLean.Part80

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part78 (nsq frobH trH qfun aU zv PP gpi78 poly_cs78 aff_second)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {n : ℕ} {J : Type} [Fintype J] (D : Dat n J)

/-- The sum of the second moments of the gradient of `V`. -/
lemma grad_sumA (Γ S η : ℝ) (hΓ : 0 ≤ Γ) (hη : 0 < η) (hF : FeatOpA D.ν D.ψ Γ)
    (hx : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → nsq (aA D.ℓ D.H D.mu x) ≤ S ∧ kA D.ψ x ≤ 2) :
    ∑ α : J × Fin n, ∫ z, (eval z (pderiv α (PVA D))) ^ 2 ∂stdGauss (J × Fin n) ≤
      4 * Γ * ((1 + η) * S +
        (1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH D.H) *
          VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ := by
  have hprob := D.hν.prob
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have step1 (i : Fin n) :
      ∑ q : J, ∫ z, (eval z (pderiv (q, i) (PVA D))) ^ 2 ∂stdGauss (J × Fin n) ≤
        4 * Γ * ∫ x, ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2
          ∂stdGauss (J × Fin n) ∂D.ν := by
    rw [← integral_finsetSum _ (fun q _ => gpi78 _ 2), swap_GA, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun q _ => gpi78 _ 2)
      ((int_GA_W D i).const_mul _) (fun W => grad_sq_leA D Γ hΓ hF i W)
  refine (Finset.sum_le_sum fun i _ => step1 i).trans ?_
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => int_GA D i)]
  have step2 : ∫ x, ∑ i, ∫ W, (eval W (QpA D x) * TvA D i x W) ^ 2
        ∂stdGauss (J × Fin n) ∂D.ν ≤
      ((1 + η) * S + (1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH D.H) *
        VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ := by
    rw [← swap_Q2A D, ← integral_const_mul]
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => int_GA D i)
      ((int_Q2A D).const_mul _) ?_
    filter_upwards [D.hν.sphere] with x hxs
    exact pointwiseA D x S η hη (hx x hxs).1 (hx x hxs).2
  have h4 : 0 ≤ 4 * Γ := by positivity
  refine (mul_le_mul_of_nonneg_left step2 h4).trans (le_of_eq ?_)
  ring

/-- `r_i(x) = E_W[Q_x T_i]`. -/
noncomputable def rvA (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ W, eval W (QpA D x) * TvA D i x W ∂stdGauss (J × Fin n)

lemma continuous_rvA (i : Fin n) : Continuous (rvA D i) := by
  have h := ((PP_QpA D).mul (PP_TpA D i)).cont_gauss
  simp only [map_mul, eval_TpA] at h
  exact h

/-- `E_W ∂_{(q,i)} V = 2 E_x[r_i ψ_q]`. -/
lemma mean_gradA (q : J) (i : Fin n) :
    ∫ W, eval W (pderiv (q, i) (PVA D)) ∂stdGauss (J × Fin n) =
      2 * ∫ x, rvA D i x * D.ψ x q ∂D.ν := by
  have := D.hν.prob
  simp only [PVA_grad D]
  rw [integral_const_mul]
  congr 1
  have hPP : PP (((2 + 1) + 0)) (fun x => (QpA D x * TpA D i x) *
      (C (D.ψ x q) : MvPolynomial (J × Fin n) ℝ)) :=
    ((PP_QpA D).mul (PP_TpA D i)).mul (PP.coef (D.cψ q))
  have hI := PP_int_prod hPP D.hν
  have h := integral_integral_swap
    (f := fun (x : Fin n → ℝ) (W : J × Fin n → ℝ) =>
      eval W ((QpA D x * TpA D i x) * (C (D.ψ x q) : MvPolynomial (J × Fin n) ℝ))) hI
  simp only [map_mul, eval_TpA, eval_C] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [rvA]
  rw [integral_mul_const]

lemma mean_grad_sq_leA (Γ : ℝ) (hΓ : 0 ≤ Γ) (hF : FeatOpA D.ν D.ψ Γ) (i : Fin n) :
    ∑ q : J, (∫ W, eval W (pderiv (q, i) (PVA D)) ∂stdGauss (J × Fin n)) ^ 2 ≤
      4 * Γ * ∫ x, rvA D i x ^ 2 ∂D.ν := by
  have hb := besselVB D.hν D.hψ Γ hΓ hF _ (continuous_rvA D i)
  have e : ∀ y : ℝ, (2 * y) ^ 2 = 4 * y ^ 2 := fun y => by ring
  simp only [mean_gradA D, e]
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma TvA_aff (i : Fin n) (x : Fin n → ℝ) (W : J × Fin n → ℝ) :
    TvA D i x W = aA D.ℓ D.H D.mu x i + ∑ β : J × Fin n, (2 * D.H i β.2 * D.ψ x β.1) * W β := by
  unfold TvA
  rw [Lv_lin, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun β _ => by ring

/-- `E_W T_i² = a_i(x)² + 4 Σ_j H_ij² k(x)`. -/
lemma TvA_second (i : Fin n) (x : Fin n → ℝ) :
    ∫ W, (TvA D i x W) ^ 2 ∂stdGauss (J × Fin n) =
      aA D.ℓ D.H D.mu x i ^ 2 + 4 * (∑ j, D.H i j ^ 2) * kA D.ψ x := by
  simp only [TvA_aff]
  rw [aff_second BstLean.Part78.gaussLin, Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  unfold kA
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma rv_sq_le (x : Fin n → ℝ) (S : ℝ) (hS : nsq (aA D.ℓ D.H D.mu x) ≤ S)
    (hk : kA D.ψ x ≤ 2) :
    ∑ i, rvA D i x ^ 2 ≤
      (S + 8 * frobH D.H) * ∫ W, (eval W (QpA D x)) ^ 2 ∂stdGauss (J × Fin n) := by
  set u2 := ∫ W, (eval W (QpA D x)) ^ 2 ∂stdGauss (J × Fin n) with hu2
  have hu0 : 0 ≤ u2 := integral_nonneg fun W => sq_nonneg _
  have hfr : ∀ i, 0 ≤ ∑ j, D.H i j ^ 2 := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hF0 : 0 ≤ frobH D.H := Finset.sum_nonneg fun i _ => hfr i
  have hi (i : Fin n) : rvA D i x ^ 2 ≤
      u2 * (aA D.ℓ D.H D.mu x i ^ 2 + 4 * (∑ j, D.H i j ^ 2) * kA D.ψ x) := by
    have h := poly_cs78 (QpA D x) (TpA D i x)
    simp only [eval_TpA] at h
    rw [TvA_second] at h
    exact h
  refine (Finset.sum_le_sum fun i _ => hi i).trans ?_
  have hsum : ∑ i, u2 * (aA D.ℓ D.H D.mu x i ^ 2 + 4 * (∑ j, D.H i j ^ 2) * kA D.ψ x) =
      u2 * (nsq (aA D.ℓ D.H D.mu x) + 4 * frobH D.H * kA D.ψ x) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    simp only [nsq, frobH]
  rw [hsum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hu0
  nlinarith

/-- The first-chaos-separated variance bound for a bundled model. -/
theorem varBound_D3 (Γ S η : ℝ) (hΓ : 0 ≤ Γ) (hη : 0 < η) (hF : FeatOpA D.ν D.ψ Γ)
    (hx : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → nsq (aA D.ℓ D.H D.mu x) ≤ S ∧ kA D.ψ x ≤ 2) :
    ∫ W, (VA D.ν D.f0 D.ℓ D.H D.mu D.ψ W - VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ) ^ 2
        ∂stdGauss (J × Fin n) ≤
      2 * Γ * ((2 + η) * S +
        ((1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) + 8) * frobH D.H) *
          VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ := by
  have hprob := D.hν.prob
  have hpoin := BstLean.Part78.poincareMv2 (J × Fin n) (PVA D)
  simp only [PVA_eval] at hpoin
  refine hpoin.trans ?_
  have h1 := grad_sumA D Γ S η hΓ hη hF hx
  have h2 : ∑ α : J × Fin n, (∫ z, eval z (pderiv α (PVA D)) ∂stdGauss (J × Fin n)) ^ 2 ≤
      4 * Γ * ((S + 8 * frobH D.H) * VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine (Finset.sum_le_sum fun i _ => mean_grad_sq_leA D Γ hΓ hF i).trans ?_
    have hi (i : Fin n) : Integrable (fun x => rvA D i x ^ 2) D.ν :=
      sph_int D.hν ((continuous_rvA D i).pow 2)
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => hi i]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← swap_Q2A D, ← integral_const_mul]
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => hi i)
      ((int_Q2A D).const_mul _) ?_
    filter_upwards [D.hν.sphere] with x hxs
    exact rv_sq_le D x S (hx x hxs).1 (hx x hxs).2
  have e : 2 * Γ * ((2 + η) * S +
        ((1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) + 8) * frobH D.H) *
          VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ =
      1 / 2 * (4 * Γ * ((1 + η) * S +
        (1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH D.H) *
          VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ) +
      1 / 2 * (4 * Γ * ((S + 8 * frobH D.H) * VbarA D.ν D.f0 D.ℓ D.H D.mu D.ψ)) := by ring
  rw [e]
  linarith

/-- **The conditional variance bound, first chaos separated.** -/
theorem varBoundA3 :
    ∀ (n : ℕ) (J : Type) [Fintype J] (ν : Measure (Fin n → ℝ)), SphLaw n ν →
    ∀ (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    ∀ (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ), Continuous mu → Continuous ψ →
    ∀ Γ S η : ℝ, 0 ≤ Γ → 0 < η → FeatOpA ν ψ Γ →
      (∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → nsq (aA ℓ H mu x) ≤ S ∧ kA ψ x ≤ 2) →
      ∫ W, (VA ν f0 ℓ H mu ψ W - VbarA ν f0 ℓ H mu ψ) ^ 2 ∂stdGauss (J × Fin n) ≤
        2 * Γ * ((2 + η) * S +
          ((1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) + 8) * frobH H) *
            VbarA ν f0 ℓ H mu ψ := by
  intro n J _ ν hν f0 ℓ H hH mu ψ hmu hψ Γ S η hΓ hη hF hx
  exact varBound_D3 ⟨ν, hν, f0, ℓ, H, hH, mu, ψ, hmu, hψ⟩ Γ S η hΓ hη hF hx

end BstLean.Part80

#print axioms BstLean.Part80.varBoundA3
