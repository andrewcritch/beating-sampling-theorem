import BstLean.Part171Inst

/-!
# Part 171 (file `Zeta`): moments of the plane coordinates of one row

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `z_{k,q} = ‖|ζ|^k‖_q = [2^{kq/2}(kq/2)!]^{1/q}` for a
two-dimensional standard Gaussian `ζ`. Here `ζ_j = (ξ₁_j, ξ₂_j)` with `ξ₁, ξ₂` independent standard
Gaussian vectors.

* `coord_lint`: `∫⁻ ofReal(ξ_j^p) dγ = ofReal(E Z^p)`.
* `zeta_mom`: `∫⁻∫⁻ ofReal((ξ₁_j² + ξ₂_j²)^k) = ofReal(Σ_i C(k, i) E Z^{2i} E Z^{2(k−i)})`.
* **`zeta_mom4`**: `E|ζ_j|⁸ = 384`; **`zeta_mom8`**: `E|ζ_j|¹⁶ = 10 321 920`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)

variable {m : ℕ}

lemma stdGauss_coord_map (j : Fin m) :
    (stdGauss (Fin m)).map (fun ξ => ξ j) = gaussianReal 0 1 := by
  have e : (fun ξ : Fin m → ℝ => ξ j) = fun ξ => ξ ⬝ᵥ Pi.single j 1 := by
    funext ξ; simp [dotProduct_single]
  rw [e, BstLean.Part131.stdGauss_dot]
  simp [dotProduct_single]

lemma coord_lint (j : Fin m) (p : ℕ) (hp : Even p) :
    ∫⁻ ξ, ENNReal.ofReal (ξ j ^ p) ∂stdGauss (Fin m) = ENNReal.ofReal (gaussMom p) := by
  have hm : Measurable (fun ξ : Fin m → ℝ => ξ j) := measurable_pi_apply j
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ p)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const p)
  have e : ∫⁻ ξ, ENNReal.ofReal (ξ j ^ p) ∂stdGauss (Fin m) =
      ∫⁻ z, ENNReal.ofReal (z ^ p) ∂(stdGauss (Fin m)).map (fun ξ => ξ j) := by
    rw [lintegral_map hf hm]
  rw [e, stdGauss_coord_map, ← gaussMom_eq,
    ofReal_integral_eq_lintegral_ofReal (BstLean.Part130.integrable_pow_gauss p)
      (Eventually.of_forall fun z => hp.pow_nonneg z)]

lemma zeta_mom (j : Fin m) (k : ℕ) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ k) ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      ENNReal.ofReal (∑ i ∈ Finset.range (k + 1),
        gaussMom (2 * i) * (k.choose i : ℝ) * gaussMom (2 * (k - i))) := by
  have hev : ∀ i, Even (2 * i) := fun i => even_two_mul i
  have hM0 : ∀ i, 0 ≤ gaussMom (2 * i) := fun i => by
    unfold gaussMom; rw [if_pos (hev i)]; positivity
  have e1 : ∀ ξ₁ ξ₂ : Fin m → ℝ, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ k) =
      ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (ξ₁ j ^ (2 * i) * (k.choose i : ℝ)) *
        ENNReal.ofReal (ξ₂ j ^ (2 * (k - i))) := by
    intro ξ₁ ξ₂
    rw [add_pow, ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (hev i).pow_nonneg (ξ₁ j); have := (hev (k - i)).pow_nonneg (ξ₂ j); positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ENNReal.ofReal_mul (by have := (hev i).pow_nonneg (ξ₁ j); positivity)]
    congr 1
    rw [← pow_mul, ← pow_mul]; ring
  simp_rw [e1]
  have hmeas : ∀ i, Measurable (fun ξ : Fin m → ℝ => ENNReal.ofReal (ξ j ^ (2 * (k - i)))) :=
    fun i => ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).pow_const _)
  have hmeas1 : ∀ i, Measurable (fun ξ : Fin m → ℝ =>
      ENNReal.ofReal (ξ j ^ (2 * i) * (k.choose i : ℝ))) :=
    fun i => ENNReal.measurable_ofReal.comp (((measurable_pi_apply j).pow_const _).mul_const _)
  have inner : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, ∑ i ∈ Finset.range (k + 1),
      ENNReal.ofReal (ξ₁ j ^ (2 * i) * (k.choose i : ℝ)) * ENNReal.ofReal (ξ₂ j ^ (2 * (k - i)))
        ∂stdGauss (Fin m) =
      ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (ξ₁ j ^ (2 * i) * (k.choose i : ℝ)) *
        ENNReal.ofReal (gaussMom (2 * (k - i))) := by
    intro ξ₁
    rw [lintegral_finsetSum _ fun i _ => (hmeas i).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul _ (hmeas i), coord_lint j _ (hev _)]
  simp_rw [inner]
  rw [lintegral_finsetSum _ fun i _ => (hmeas1 i).mul_const _]
  have outer : ∀ i, ∫⁻ ξ₁, ENNReal.ofReal (ξ₁ j ^ (2 * i) * (k.choose i : ℝ)) *
      ENNReal.ofReal (gaussMom (2 * (k - i))) ∂stdGauss (Fin m) =
      ENNReal.ofReal (gaussMom (2 * i) * (k.choose i : ℝ) * gaussMom (2 * (k - i))) := by
    intro i
    rw [lintegral_mul_const _ (hmeas1 i)]
    have e2 : ∀ ξ : Fin m → ℝ, ENNReal.ofReal (ξ j ^ (2 * i) * (k.choose i : ℝ)) =
        ENNReal.ofReal (ξ j ^ (2 * i)) * ENNReal.ofReal (k.choose i : ℝ) := fun ξ =>
      ENNReal.ofReal_mul ((hev i).pow_nonneg _)
    simp_rw [e2]
    have hmi : Measurable (fun ξ : Fin m → ℝ => ENNReal.ofReal (ξ j ^ (2 * i))) :=
      ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).pow_const _)
    rw [lintegral_mul_const _ hmi, coord_lint j _ (hev _), ← ENNReal.ofReal_mul (hM0 i), ← ENNReal.ofReal_mul (by
        have := hM0 i; positivity)]
  simp_rw [outer]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := hM0 i; have := hM0 (k - i); positivity)]

lemma gaussMom_two_mul (i : ℕ) : gaussMom (2 * i) = ((2 * i - 1).doubleFactorial : ℝ) := by
  unfold gaussMom; rw [if_pos (even_two_mul i)]

/-- **`E|ζ_j|⁸ = 384`.** -/
theorem zeta_mom4 (j : Fin m) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4) ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      ENNReal.ofReal 384 := by
  rw [zeta_mom]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

/-- **`E|ζ_j|¹⁶ = 10 321 920`.** -/
theorem zeta_mom8 (j : Fin m) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8) ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      ENNReal.ofReal 10321920 := by
  rw [zeta_mom]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, gaussMom_two_mul]
  norm_num [Nat.choose, Nat.doubleFactorial]

end BstLean.Part171
