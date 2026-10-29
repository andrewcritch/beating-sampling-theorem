import BstLean.Part166Fld

/-!
# Part 166 (file `Tr`): transfer of the key-form certificate density to Part 162's `psiA`

No proof is left open; no `native_decide` or `axiom` is used.

* `gradSq_const_mul`, `tanSq_const_mul`: `|∇(κΦ)|² = κ²|∇Φ|²` (every point, differentiable or not).
* **`psiA_sig_eq`**: for a design with the Agent centre of Part 154, `Ψ_σ = psiK sK (agKey D c)`.
* **`psiA_lam_eq`**: `e_b·Ψ_λ = psiK fK (agKey D c)`, `e_b = |b|²/n`.
-/

namespace BstLean.Part166

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part150 (rhoC thetaC bT)
open BstLean.Part161 (xLat hhMat uHat consV muI latC lamX sigX Ix)
open BstLean.Part162 (xLatH tanSq psiA)
open BstLean.Part151 (gradSq)

variable {n : ℕ}

lemma gradSq_const_mul {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ℝ) (g : (ι → ℝ) → ℝ)
    (v : ι → ℝ) : gradSq (fun w => κ * g w) v = κ ^ 2 * gradSq g v := by
  unfold gradSq
  rw [Finset.mul_sum]
  by_cases hd : DifferentiableAt ℝ g v
  · rw [fderiv_const_mul hd κ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  · by_cases hκ : κ = 0
    · subst hκ
      simp
    · have hd' : ¬ DifferentiableAt ℝ (fun w => κ * g w) v := by
        intro h
        apply hd
        have h2 := h.const_mul κ⁻¹
        have e : (fun w => κ⁻¹ * (κ * g w)) = g := by
          funext w; field_simp
        rwa [e] at h2
      rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']
      simp

lemma tanSq_const_mul (κ : ℝ) (Φ : (Fin n → ℝ) → ℝ) (c : Ret n) (s : ℝ)
    (v : Fin (n - 1) → ℝ) : tanSq (fun x => κ * Φ x) c s v = κ ^ 2 * tanSq Φ c s v := by
  unfold tanSq
  rw [gradSq_const_mul κ (fun w => Φ (xLatH c s w)) v]
  ring

lemma sqrt_sq_mul (κ t : ℝ) : √(κ ^ 2 * t) ^ 2 = κ ^ 2 * √t ^ 2 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [Real.sq_sqrt (mul_nonneg (sq_nonneg _) ht), Real.sq_sqrt ht]
  · have h1 : κ ^ 2 * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ht.le
    rw [Real.sqrt_eq_zero'.mpr h1, Real.sqrt_eq_zero'.mpr ht.le]
    simp

/-- The key of the retained data is consistent with `bK`: `D.bA = bK (agKey D c)`. -/
lemma bA_eq_bK (D : Design n) (hD : AgentCentre154 D) (c : Ret n) :
    D.bA c.1 c.2.1.1 = bK (agKey D c) := hD c

lemma sigX_eq_sK (D : Design n) (hD : AgentCentre154 D) (c : Ret n) :
    sigX D c = sK (agKey D c) := by
  funext x
  unfold sigX sK
  rw [bA_eq_bK D hD c]
  rfl

lemma fK_eq_mul (D : Design n) (hD : AgentCentre154 D) (c : Ret n) :
    fK (agKey D c) = fun x => √(normSq (D.bA c.1 c.2.1.1)) / √(n : ℝ) * lamX D c x := by
  funext x
  unfold fK lamX
  rw [bA_eq_bK D hD c]
  rfl

/-- **`Ψ_σ` in key form.** -/
theorem psiA_sig_eq (D : Design n) (hD : AgentCentre154 D) (c : Ret n) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : psiA (sigX D c) D c a v = psiK sK (agKey D c) a v := by
  unfold psiA psiK
  rw [sigX_eq_sK D hD c]
  rfl

/-- **`Ψ_λ` in key form**: `(|b|²/n)·Ψ_λ = psiK fK`. -/
theorem psiA_lam_eq (hn : 1 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n) (a : Ix n)
    (v : Fin (n - 1) → ℝ) :
    normSq (D.bA c.1 c.2.1.1) / n * psiA (lamX D c) D c a v = psiK fK (agKey D c) a v := by
  unfold psiA psiK
  rw [fK_eq_mul D hD c]
  have e : tanSq (fun x => √(normSq (D.bA c.1 c.2.1.1)) / √(n : ℝ) * lamX D c x)
      (repK (agKey D c)) (latK (agKey D c) a) v =
      (√(normSq (D.bA c.1 c.2.1.1)) / √(n : ℝ)) ^ 2 * tanSq (lamX D c) c (latC D c a) v :=
    tanSq_const_mul _ _ _ _ _
  rw [e, sqrt_sq_mul]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, Real.sq_sqrt (normSq_nonneg _), Real.sq_sqrt hn0.le]

end BstLean.Part166
