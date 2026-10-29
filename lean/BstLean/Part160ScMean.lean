import BstLean.Part160ScPair

/-!
# Part 160 (file `ScMean`): a sharper lower bound of the mean of the first-layer variance

Do not use `sorry`, `native_decide` or `axiom`.

`s_h² = sO2 A₁ c τ = Γ − Γ̄`. Part 153 has `E s_h² ≥ 2(1 − 1/π)τ²` (`sO2_mean`; it is the chord
bound of `κ`). This file uses the quadratic bound of `κ` (`kappa_quad_all`).

Notation: `y = c + τ ξ`, `ρ² = |c|² + n τ²`, `u(ξ) = ⟨y, c⟩`,
`Tcos c τ = E_ξ[⟨y, c⟩²/|y|²]` (`|c|²` times the mean squared cosine of the input and `c`).

* `gauss_lin_sq`: `E_ξ (p + q·⟨ξ, r⟩)² = p² + q²·|r|²`.
* `int_Kn_le`: `E_{ξ,ξ′}[|y||y′| κ] ≤ ρ²/π + |c|²/2 + (1/2 − 1/π)(Tcos + τ²)`.
* **`sO2_mean_sharp`**:
  `E s_h² ≥ (2/n)·((1 − 1/π)ρ² − |c|²/2 − (1/2 − 1/π)(Tcos + τ²))`.
* `Tcos_le`: `Tcos ≤ (|c|⁴ + τ²|c|²)/((1 − ε)²(ρ² − τ²)) + |c|²·exp(−ε²(ρ² − τ²)/(2τ²))`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (hO gO sO2)
open BstLean.Part153 (nrm)

variable {n m : ℕ}

/-- `E_ξ (p + q·⟨ξ, r⟩)² = p² + q²·|r|²`, with integrability. -/
lemma gauss_lin_sq (r : Fin n → ℝ) (p q : ℝ) :
    Integrable (fun ξ : Fin n → ℝ => (p + q * (ξ ⬝ᵥ r)) ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, (p + q * (ξ ⬝ᵥ r)) ^ 2 ∂stdGauss (Fin n) = p ^ 2 + q ^ 2 * normSq r := by
  have mf : Measurable (fun x : ℝ => (p + q * x) ^ 2) := by fun_prop
  have i1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
    have := integrable_pow_gauss 1
    simp only [pow_one] at this
    exact this
  have i2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := integrable_pow_gauss 2
  have e1 : ∫ z : ℝ, z ∂gaussianReal 0 1 = 0 := by
    have := BstLean.Part29.gaussMom_eq 1
    rw [show BstLean.Part29.gaussMom 1 = 0 by simp [BstLean.Part29.gaussMom]] at this
    simp only [pow_one] at this
    exact this
  have e2 : ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1 = 1 := by
    have := BstLean.Part29.gaussMom_eq 2
    simpa [BstLean.Part29.gaussMom] using this
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(∑ j, r j ^ 2) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = normSq r := by rw [hs]; exact Real.sq_sqrt (normSq_nonneg r)
  have e : (fun z : ℝ => (p + q * (s * z)) ^ 2) =
      fun z => p ^ 2 + 2 * p * q * s * z + q ^ 2 * s ^ 2 * z ^ 2 := funext fun z => by ring
  have hI : Integrable (fun z : ℝ => (p + q * (s * z)) ^ 2) (gaussianReal 0 1) := by
    rw [e]
    exact ((integrable_const _).add (i1.const_mul _)).add (i2.const_mul _)
  constructor
  · refine BstLean.Part150.gauss_lin_integrable r mf ?_
    rw [← hs]; exact hI
  · have hA : ∫ z : ℝ, (p ^ 2 + 2 * p * q * s * z + q ^ 2 * s ^ 2 * z ^ 2) ∂gaussianReal 0 1 =
        ∫ z : ℝ, (p ^ 2 + 2 * p * q * s * z) ∂gaussianReal 0 1 +
          ∫ z : ℝ, q ^ 2 * s ^ 2 * z ^ 2 ∂gaussianReal 0 1 :=
      integral_add ((integrable_const _).add (i1.const_mul _)) (i2.const_mul _)
    have hB : ∫ z : ℝ, (p ^ 2 + 2 * p * q * s * z) ∂gaussianReal 0 1 =
        ∫ _z : ℝ, p ^ 2 ∂gaussianReal 0 1 + ∫ z : ℝ, 2 * p * q * s * z ∂gaussianReal 0 1 :=
      integral_add (integrable_const _) (i1.const_mul _)
    rw [BstLean.Part150.gauss_lin_integral r mf, ← hs, e, hA, hB, integral_const_mul,
      integral_const_mul, e1, e2, integral_const, probReal_univ, hs2]
    simp

/-- `|c|²` times the mean squared cosine: `E_ξ[⟨y, c⟩²/|y|²]`, `y = c + τ ξ`. -/
noncomputable def Tcos (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∫ ξ, (∑ j, (c + τ • ξ) j * c j) ^ 2 / normSq (c + τ • ξ) ∂stdGauss (Fin n)

lemma dot_sq_le (y y' : Fin n → ℝ) : (∑ j, y j * y' j) ^ 2 ≤ normSq y * normSq y' :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `d²/|y|² ≤ |y′|²` (also when `y = 0`). -/
lemma dot_sq_div_le (y y' : Fin n → ℝ) : (∑ j, y j * y' j) ^ 2 / normSq y ≤ normSq y' := by
  rcases eq_or_lt_of_le (normSq_nonneg y) with h | h
  · rw [← h, div_zero]; exact normSq_nonneg y'
  · rw [div_le_iff₀ h, mul_comm]; exact dot_sq_le y y'

lemma dot_shift (y : Fin n → ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    ∑ j, y j * (c + τ • ξ) j = (∑ j, y j * c j) + τ * (ξ ⬝ᵥ y) := by
  unfold dotProduct
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma measurable_Tcos_integrand (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun ξ : Fin n → ℝ => (∑ j, (c + τ • ξ) j * c j) ^ 2 / normSq (c + τ • ξ)) := by
  have h1 : Measurable (fun ξ : Fin n → ℝ => ∑ j, (c + τ • ξ) j * c j) :=
    Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (continuous_shift c τ).measurable).mul_const _
  exact (h1.pow_const 2).div (BstLean.Part153.cont_ns c τ).measurable

lemma integrable_Tcos_integrand (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun ξ : Fin n → ℝ => (∑ j, (c + τ • ξ) j * c j) ^ 2 / normSq (c + τ • ξ))
      (stdGauss (Fin n)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  refine Integrable.of_bound (measurable_Tcos_integrand c τ).aestronglyMeasurable (normSq c)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (normSq_nonneg _))]
  exact dot_sq_div_le _ _

/-- `(E|y|)² ≤ ρ²`. -/
lemma mean_nrm_sq_le (c : Fin n → ℝ) (τ : ℝ) :
    (∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n)) ^ 2 ≤ normSq c + (n : ℝ) * τ ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  obtain ⟨hs1, hs2⟩ := BstLean.Part153.int_normSq_shift c τ
  have hi := integrable_nrmShift c τ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hM, ← hs2]
  have i2 := hi.const_mul (2 * M)
  have h0 : 0 ≤ ∫ ξ, (nrm (c + τ • ξ) - M) ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => sq_nonneg _
  have e : (fun ξ : Fin n → ℝ => (nrm (c + τ • ξ) - M) ^ 2) =
      fun ξ => normSq (c + τ • ξ) - 2 * M * nrm (c + τ • ξ) + M ^ 2 := funext fun ξ => by
    rw [← BstLean.Part153.nrm_sq (c + τ • ξ)]; ring
  have hA : ∫ ξ, (normSq (c + τ • ξ) - 2 * M * nrm (c + τ • ξ) + M ^ 2) ∂stdGauss (Fin n) =
      ∫ ξ, (normSq (c + τ • ξ) - 2 * M * nrm (c + τ • ξ)) ∂stdGauss (Fin n) +
        ∫ _ξ, M ^ 2 ∂stdGauss (Fin n) := integral_add (hs1.sub i2) (integrable_const _)
  have hB : ∫ ξ, (normSq (c + τ • ξ) - 2 * M * nrm (c + τ • ξ)) ∂stdGauss (Fin n) =
      ∫ ξ, normSq (c + τ • ξ) ∂stdGauss (Fin n) -
        ∫ ξ, 2 * M * nrm (c + τ • ξ) ∂stdGauss (Fin n) := integral_sub hs1 i2
  rw [e, hA, hB, integral_const_mul, ← hM, integral_const, probReal_univ, one_smul] at h0
  linarith

/-- The mean of one coordinate of `y`. -/
lemma int_shift_coord (c : Fin n → ℝ) (τ : ℝ) (j : Fin n) :
    Integrable (fun ξ : Fin n → ℝ => (c + τ • ξ) j) (stdGauss (Fin n)) ∧
    ∫ ξ, (c + τ • ξ) j ∂stdGauss (Fin n) = c j := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have e : (fun ξ : Fin n → ℝ => (c + τ • ξ) j) = fun ξ => c j + τ * ξ j := funext fun ξ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hi := BstLean.Part112.int_coord (ι := Fin n) j
  rw [e]
  refine ⟨(integrable_const _).add (hi.const_mul _), ?_⟩
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul,
    BstLean.Part112.integral_coord, integral_const, probReal_univ]
  simp

/-- **The mean of the pair kernel**:
`E_{ξ,ξ′}[|y||y′| κ(⟨y,y′⟩/(|y||y′|))] ≤ ρ²/π + |c|²/2 + (1/2 − 1/π)(Tcos + τ²)`. -/
theorem int_Kn_le (c : Fin n → ℝ) (τ : ℝ) :
    ∫ z, Kn c τ z ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) ≤
      (normSq c + (n : ℝ) * τ ^ 2) / π + normSq c / 2 +
        (1 / 2 - 1 / π) * (Tcos c τ + τ ^ 2) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hc2 := c2_nonneg
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂ : Measure ((Fin n → ℝ) × (Fin n → ℝ)),
      γ₂ = (stdGauss (Fin n)).prod (stdGauss (Fin n)) := ⟨_, rfl⟩
  have hprob2 : IsProbabilityMeasure γ₂ := by rw [hγ₂]; infer_instance
  -- the four functions
  obtain ⟨fa, hfa⟩ : ∃ fa : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      fa = fun z => nrm (c + τ • z.1) * nrm (c + τ • z.2) := ⟨_, rfl⟩
  obtain ⟨fd, hfd⟩ : ∃ fd : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      fd = fun z => ∑ j, (c + τ • z.1) j * (c + τ • z.2) j := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      G = fun z => (∑ j, (c + τ • z.1) j * (c + τ • z.2) j) ^ 2 / normSq (c + τ • z.1) := ⟨_, rfl⟩
  have ia : Integrable fa γ₂ := by rw [hfa, hγ₂]; exact integrable_nrm_prod c τ
  have icoord : ∀ j : Fin n, Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (c + τ • z.1) j * (c + τ • z.2) j) γ₂ := fun j => by
    rw [hγ₂]; exact (int_shift_coord c τ j).1.mul_prod (int_shift_coord c τ j).1
  have id' : Integrable fd γ₂ := by
    rw [hfd]; exact integrable_finsetSum _ fun j _ => icoord j
  have mG : Measurable G := by
    rw [hG]
    exact ((measurable_dotz c τ).pow_const 2).div
      ((BstLean.Part153.cont_ns c τ).measurable.comp measurable_fst)
  have iN2 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => normSq (c + τ • z.2)) γ₂ := by
    have h := (integrable_const (1 : ℝ)).mul_prod (μ := stdGauss (Fin n))
      (BstLean.Part153.int_normSq_shift c τ).1
    rw [hγ₂]
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp
  have G0 : ∀ z, 0 ≤ G z := fun z => by
    rw [hG]; exact div_nonneg (sq_nonneg _) (normSq_nonneg _)
  have iG : Integrable G γ₂ := by
    refine Integrable.mono' iN2 mG.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (G0 z), hG]
    exact dot_sq_div_le _ _
  have hswap : ∫ z, G z.swap ∂γ₂ = ∫ z, G z ∂γ₂ := by
    rw [hγ₂]; exact integral_prod_swap G
  have iGs : Integrable (fun z => G z.swap) γ₂ := by
    rw [hγ₂]; rw [hγ₂] at iG; exact iG.swap
  -- pointwise
  have hpt : ∀ z, Kn c τ z ≤ fa z / π + fd z / 2 + (1 / 2 - 1 / π) * ((G z + G z.swap) / 2) := by
    intro z
    have h := pair_bound (BstLean.Part153.nrm_nonneg (c + τ • z.1))
      (BstLean.Part153.nrm_nonneg (c + τ • z.2)) (dot_abs_le (c + τ • z.1) (c + τ • z.2))
    rw [BstLean.Part153.nrm_sq, BstLean.Part153.nrm_sq] at h
    have e : (∑ j, (c + τ • z.swap.1) j * (c + τ • z.swap.2) j) =
        ∑ j, (c + τ • z.1) j * (c + τ • z.2) j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hfa, hfd, hG]
    simp only [e]
    exact h
  have j1 := ia.div_const π
  have j2 := id'.div_const 2
  have j3 : Integrable (fun z => (1 / 2 - 1 / π) * ((G z + G z.swap) / 2)) γ₂ :=
    ((iG.add iGs).div_const 2).const_mul _
  have hint : ∫ z, Kn c τ z ∂γ₂ ≤
      ∫ z, (fa z / π + fd z / 2 + (1 / 2 - 1 / π) * ((G z + G z.swap) / 2)) ∂γ₂ :=
    integral_mono (by rw [hγ₂]; exact integrable_Kn c τ) ((j1.add j2).add j3) hpt
  have hA : ∫ z, (fa z / π + fd z / 2 + (1 / 2 - 1 / π) * ((G z + G z.swap) / 2)) ∂γ₂ =
      ∫ z, (fa z / π + fd z / 2) ∂γ₂ + ∫ z, (1 / 2 - 1 / π) * ((G z + G z.swap) / 2) ∂γ₂ :=
    integral_add (j1.add j2) j3
  have hB : ∫ z, (fa z / π + fd z / 2) ∂γ₂ = ∫ z, fa z / π ∂γ₂ + ∫ z, fd z / 2 ∂γ₂ :=
    integral_add j1 j2
  have hC : ∫ z, (G z + G z.swap) ∂γ₂ = ∫ z, G z ∂γ₂ + ∫ z, G z.swap ∂γ₂ := integral_add iG iGs
  rw [← hγ₂]
  refine hint.trans ?_
  rw [hA, hB, integral_div, integral_div, integral_const_mul, integral_div, hC, hswap]
  -- (i)
  have h1 : ∫ z, fa z ∂γ₂ ≤ normSq c + (n : ℝ) * τ ^ 2 := by
    have hp := integral_prod_mul (μ := stdGauss (Fin n)) (ν := stdGauss (Fin n))
      (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) (fun ξ : Fin n → ℝ => nrm (c + τ • ξ))
    have e : ∫ z, fa z ∂γ₂ = (∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n)) ^ 2 := by
      rw [hfa, hγ₂, sq]; exact hp
    rw [e]
    exact mean_nrm_sq_le c τ
  -- (ii)
  have h2 : ∫ z, fd z ∂γ₂ = normSq c := by
    rw [hfd, integral_finsetSum _ fun j _ => icoord j]
    unfold normSq
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγ₂]
    have hp := integral_prod_mul (μ := stdGauss (Fin n)) (ν := stdGauss (Fin n))
      (fun ξ : Fin n → ℝ => (c + τ • ξ) j) (fun ξ : Fin n → ℝ => (c + τ • ξ) j)
    rw [(int_shift_coord c τ j).2] at hp
    rw [sq]; exact hp
  -- (iii)
  have h3 : ∫ z, G z ∂γ₂ ≤ Tcos c τ + τ ^ 2 := by
    rw [hγ₂] at iG ⊢
    rw [integral_prod _ iG]
    have inner : ∀ ξ : Fin n → ℝ, ∫ ξ', G (ξ, ξ') ∂stdGauss (Fin n) =
        ((∑ j, (c + τ • ξ) j * c j) ^ 2 + τ ^ 2 * normSq (c + τ • ξ)) / normSq (c + τ • ξ) := by
      intro ξ
      rw [hG]
      simp only [dot_shift]
      rw [integral_div, (gauss_lin_sq (c + τ • ξ) _ τ).2]
    simp_rw [inner]
    have hb : ∀ ξ : Fin n → ℝ,
        ((∑ j, (c + τ • ξ) j * c j) ^ 2 + τ ^ 2 * normSq (c + τ • ξ)) / normSq (c + τ • ξ) ≤
        (∑ j, (c + τ • ξ) j * c j) ^ 2 / normSq (c + τ • ξ) + τ ^ 2 := by
      intro ξ
      rcases eq_or_lt_of_le (normSq_nonneg (c + τ • ξ)) with h | h
      · rw [← h, div_zero, div_zero]; nlinarith [sq_nonneg τ]
      · rw [add_div, mul_div_assoc, div_self h.ne', mul_one]
    have hm : Measurable (fun ξ : Fin n → ℝ =>
        ((∑ j, (c + τ • ξ) j * c j) ^ 2 + τ ^ 2 * normSq (c + τ • ξ)) / normSq (c + τ • ξ)) := by
      have h1 : Measurable (fun ξ : Fin n → ℝ => ∑ j, (c + τ • ξ) j * c j) :=
        Finset.measurable_sum _ fun j _ =>
          ((measurable_pi_apply j).comp (continuous_shift c τ).measurable).mul_const _
      exact ((h1.pow_const 2).add ((BstLean.Part153.cont_ns c τ).measurable.const_mul _)).div
        (BstLean.Part153.cont_ns c τ).measurable
    have hi : Integrable (fun ξ : Fin n → ℝ =>
        ((∑ j, (c + τ • ξ) j * c j) ^ 2 + τ ^ 2 * normSq (c + τ • ξ)) / normSq (c + τ • ξ))
        (stdGauss (Fin n)) := by
      refine Integrable.of_bound hm.aestronglyMeasurable (normSq c + τ ^ 2)
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (add_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (normSq_nonneg _))) (normSq_nonneg _))]
      exact (hb ξ).trans (add_le_add (dot_sq_div_le _ _) le_rfl)
    have hadd : ∫ ξ : Fin n → ℝ, ((∑ j, (c + τ • ξ) j * c j) ^ 2 / normSq (c + τ • ξ) + τ ^ 2)
        ∂stdGauss (Fin n) = Tcos c τ + τ ^ 2 := by
      have := integral_add (integrable_Tcos_integrand c τ)
        (integrable_const (μ := stdGauss (Fin n)) (τ ^ 2))
      rw [integral_const, probReal_univ, one_smul] at this
      exact this
    rw [← hadd]
    exact integral_mono hi ((integrable_Tcos_integrand c τ).add (integrable_const _)) hb
  have e3 : (∫ z, G z ∂γ₂ + ∫ z, G z ∂γ₂) / 2 = ∫ z, G z ∂γ₂ := by ring
  rw [e3, h2]
  have h4 := mul_le_mul_of_nonneg_left h3 hc2
  have h5 : (∫ z, fa z ∂γ₂) / π ≤ (normSq c + (n : ℝ) * τ ^ 2) / π :=
    div_le_div_of_nonneg_right h1 hπ.le
  linarith

/-- **A sharper lower bound of the mean of the first-layer variance**:
`E_{A₁} s_h² ≥ (2/n)·((1 − 1/π)·ρ² − |c|²/2 − (1/2 − 1/π)·(Tcos + τ²))`. -/
theorem sO2_mean_sharp (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) :
    2 / (n : ℝ) * ((1 - 1 / π) * (normSq c + (n : ℝ) * τ ^ 2) - normSq c / 2 -
        (1 / 2 - 1 / π) * (Tcos c τ + τ ^ 2)) ≤
      ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat m n (2 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hGi, hGe⟩ := BstLean.Part153.GamS_mean (m := m) hm c τ (v := 2 / (n : ℝ))
    (by positivity)
  have eG : (fun A : Matrix (Fin m) (Fin n) ℝ => BstLean.Part153.GamS A c τ) =
      fun A => gO A c τ := funext fun A => BstLean.Part153.GamS_eq_gO hm A c τ
  rw [eG] at hGi hGe
  have hH : ∀ i : Fin m, Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => hO A c τ i ^ 2)
      (gaussMat m n (2 / (n : ℝ))) := fun i => (hO_sq_mean hn c τ i).1
  have hS : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => 2 / (m : ℝ) * ∑ i, hO A c τ i ^ 2)
      (gaussMat m n (2 / (n : ℝ))) :=
    (integrable_finsetSum _ fun i _ => hH i).const_mul _
  have e : ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat m n (2 / (n : ℝ)) =
      2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) -
        2 / (n : ℝ) * ∫ z, Kn c τ z ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
    unfold sO2
    rw [integral_sub hGi hS, hGe, integral_const_mul, integral_finsetSum _ fun i _ => hH i]
    simp_rw [fun i : Fin m => (hO_sq_mean (m := m) hn c τ i).2]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [e]
  have hK := int_Kn_le c τ
  have h2 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hK h2
  have e2 : 2 / (n : ℝ) * ((1 - 1 / π) * (normSq c + (n : ℝ) * τ ^ 2) - normSq c / 2 -
      (1 / 2 - 1 / π) * (Tcos c τ + τ ^ 2)) = 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) -
      2 / (n : ℝ) * ((normSq c + (n : ℝ) * τ ^ 2) / π + normSq c / 2 +
        (1 / 2 - 1 / π) * (Tcos c τ + τ ^ 2)) := by ring
  rw [e2]
  linarith

/-- **The squared cosine**: for `0 ≤ ε < 1`, `τ > 0`, `n ≥ 2`, with `Q = ρ² − τ²`:
`Tcos ≤ (|c|⁴ + τ²|c|²)/((1 − ε)² Q) + |c|²·exp(−ε² Q/(2τ²))`. -/
theorem Tcos_le (hn : 2 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    Tcos c τ ≤ (normSq c ^ 2 + τ ^ 2 * normSq c) /
        ((1 - ε) ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) +
      normSq c * exp (-(ε ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) / (2 * τ ^ 2)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htail := nrm_lower_tail (by omega : 1 ≤ n) c hτ hε0
  have hQ0 : 0 < normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := by
    have := normSq_nonneg c
    nlinarith [sq_pos_of_pos hτ]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := ⟨_, rfl⟩
  rw [← hQ] at hQ0 htail ⊢
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 - ε) * √Q := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact mul_pos (by linarith) (Real.sqrt_pos.mpr hQ0)
  have hr2 : r ^ 2 = (1 - ε) ^ 2 * Q := by rw [hr, mul_pow, Real.sq_sqrt hQ0.le]
  rw [← hr] at htail
  rw [← hr2]
  have hB : MeasurableSet {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} :=
    measurableSet_le (measurable_nrmShift c τ) measurable_const
  -- `u = ⟨y, c⟩`
  have eu : ∀ ξ : Fin n → ℝ, ∑ j, (c + τ • ξ) j * c j = normSq c + τ * (ξ ⬝ᵥ c) := by
    intro ξ
    unfold dotProduct normSq
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨iu, hu⟩ := gauss_lin_sq c (normSq c) τ
  have hpt : ∀ ξ : Fin n → ℝ,
      (∑ j, (c + τ • ξ) j * c j) ^ 2 / normSq (c + τ • ξ) ≤
        (normSq c + τ * (ξ ⬝ᵥ c)) ^ 2 / r ^ 2 +
          Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => normSq c) ξ := by
    intro ξ
    by_cases hx : nrm (c + τ • ξ) ≤ r
    · rw [Set.indicator_of_mem (show ξ ∈ {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} from hx)]
      have := dot_sq_div_le (c + τ • ξ) c
      have h0 : 0 ≤ (normSq c + τ * (ξ ⬝ᵥ c)) ^ 2 / r ^ 2 := by positivity
      linarith
    · rw [Set.indicator_of_notMem (show ξ ∉ {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} from hx),
        add_zero, eu]
      have hx' : r < nrm (c + τ • ξ) := not_le.mp hx
      have h1 : r ^ 2 ≤ normSq (c + τ • ξ) := by
        rw [← BstLean.Part153.nrm_sq]
        exact pow_le_pow_left₀ hr0.le hx'.le 2
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h1
  have i1 := iu.div_const (r ^ 2)
  have i2 : Integrable (Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r}
      (fun _ => normSq c)) (stdGauss (Fin n)) := (integrable_const (normSq c)).indicator hB
  have hsum : ∫ ξ : Fin n → ℝ, ((normSq c + τ * (ξ ⬝ᵥ c)) ^ 2 / r ^ 2 +
      Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => normSq c) ξ)
        ∂stdGauss (Fin n) = (normSq c ^ 2 + τ ^ 2 * normSq c) / r ^ 2 +
      (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} * normSq c := by
    rw [integral_add i1 i2, integral_div, hu, integral_indicator_const _ hB, smul_eq_mul]
  have hmono : Tcos c τ ≤ ∫ ξ : Fin n → ℝ, ((normSq c + τ * (ξ ⬝ᵥ c)) ^ 2 / r ^ 2 +
      Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => normSq c) ξ)
        ∂stdGauss (Fin n) := integral_mono (integrable_Tcos_integrand c τ) (i1.add i2) hpt
  rw [hsum] at hmono
  refine hmono.trans ?_
  have h3 : (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} * normSq c ≤
      normSq c * exp (-(ε ^ 2 * Q) / (2 * τ ^ 2)) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left htail (normSq_nonneg c)
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms int_Kn_le
open BstLean.Part160 in
#print axioms sO2_mean_sharp
open BstLean.Part160 in
#print axioms Tcos_le
