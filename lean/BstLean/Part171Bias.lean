import BstLean.Part171Swap

/-!
# Part 171 (file `Bias`): the conditional mean errors as sums of row biases

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `N_f^b = Σ_j b_j{E[X(z_j) | ζ_j] − ψ_ς(g_j)}` and the energy analogue.
Fix the retained value `c` (World data and `A₁`), a node `g` and the plane coordinates `(ξ₁, ξ₂)`.
`M₀ = Mpl h r c₁ c₂ 0` is the plane part of the second layer. `wT c g v = t_A|w(v)|²`, where
`w(v) = perp r (perp h (a(v)))` is the part of `a₁(x_v)` orthogonal to the plane `U = span(h, ā)`
(the paper's `v_v = |Π_{U^⊥}F_s(v)|²`).

* **`biasF_rows`**: `biasF = κ Σ_j b_j (E_v G((M₀a(v))_j, wT(v)) − G((M₀ā)_j, ς²))`,
  `κ = n/(√n|b|)`, `G(α, w) = psiS √w α`.
* **`biasW_rows`**: `biasW = Σ_j (E_v G₂((M₀a(v))_j, wT(v)) − G₂((M₀ā)_j, ς²))`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part134 (res)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part170 (biasF biasW exFn_Mpl exWn_Mpl flE flQ Mpl hB tA bOfY aLat vmean vmean_aLat
  aLat_normSq_le measurable_aLat G2)
open BstLean.Part137 (psiS)
open BstLean.Part131 (frob frob_nonneg)

variable {n : ℕ}

/-- `wT c g v = t_A |perp r (perp h (a(v)))|²` (the paper's `v_v`). -/
noncomputable def wT (c : Ret n) (g : ℕ) (v : Fin (n - 1) → ℝ) : ℝ :=
  tA n * normSq (perp (res (hB c) (a1Bar c (nodeS c g))) (perp (hB c) (aLat c (nodeS c g) v)))

/-- The plane part `M₀` of the second layer at the plane coordinates `(ξ₁, ξ₂)`. -/
noncomputable def M0 (c : Ret n) (g : ℕ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : Matrix (Fin (mA n)) (Fin (mA n)) ℝ :=
  Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) (cOf (tA n) (hB c) ξ₁)
    (cOf (tA n) (res (hB c) (a1Bar c (nodeS c g))) ξ₂) 0

lemma tA_nonneg (n : ℕ) : 0 ≤ tA n := by unfold tA; positivity

lemma abs_le_half_sq (x : ℝ) : |x| ≤ (x ^ 2 + 1) / 2 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

lemma relu_abs_le (x : ℝ) : |relu x| ≤ 1 + x ^ 2 := by
  rw [abs_of_nonneg (BstLean.Part130.relu_nonneg x)]
  rcases le_total x 0 with h | h
  · rw [BstLean.Part130.relu_of_nonpos h]; positivity
  · rw [BstLean.Part130.relu_of_nonneg h]; nlinarith [sq_nonneg (x - 1)]

lemma relu_sq_abs_le (x : ℝ) : |relu x ^ 2| ≤ 0 + x ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _), zero_add]
  rcases le_total x 0 with h | h
  · rw [BstLean.Part130.relu_of_nonpos h]; nlinarith [sq_nonneg x]
  · rw [BstLean.Part130.relu_of_nonneg h]

/-- The ingredients of `swap_row` at a node. -/
lemma node_bounds (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (h1 : OpB (A1 c) O) (M₀ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (j : Fin (mA n)) :
    Measurable (fun v => (M₀ *ᵥ aLat c (nodeS c g) v) j) ∧
    (∀ v, |(M₀ *ᵥ aLat c (nodeS c g) v) j| ≤ (frob M₀ * O ^ 2 + 1) / 2) ∧
    Measurable (fun v => perp (res (hB c) (a1Bar c (nodeS c g))) (perp (hB c)
      (aLat c (nodeS c g) v))) ∧
    (∀ v, normSq (perp (res (hB c) (a1Bar c (nodeS c g))) (perp (hB c)
      (aLat c (nodeS c g) v))) ≤ O ^ 2) := by
  have ha := measurable_aLat c (nodeS c g)
  refine ⟨(measurable_pi_apply j).comp ((Continuous.matrix_mulVec continuous_const
    continuous_id).measurable.comp ha), fun v => ?_,
    (BstLean.Part167.measurable_perp _).comp ((BstLean.Part167.measurable_perp _).comp ha),
    fun v => ?_⟩
  · refine (abs_le_half_sq _).trans ?_
    have := BstLean.Part171.mulVec_coord_sq_le M₀ (aLat c (nodeS c g) v) j
    have h2 := aLat_normSq_le hn c hs h1 v
    have h3 : frob M₀ * normSq (aLat c (nodeS c g) v) ≤ frob M₀ * O ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (frob_nonneg _)
    linarith
  · exact (normSq_perp_le _ _).trans ((normSq_perp_le _ _).trans (aLat_normSq_le hn c hs h1 v))

lemma sqrt_wT (c : Ret n) (g : ℕ) (v : Fin (n - 1) → ℝ) :
    √(wT c g v) = √(tA n) * √(normSq (perp (res (hB c) (a1Bar c (nodeS c g)))
      (perp (hB c) (aLat c (nodeS c g) v)))) := by
  unfold wT; rw [Real.sqrt_mul (tA_nonneg n)]

/-- **The location bias as a sum of row biases.** -/
theorem biasF_rows (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (h1 : OpB (A1 c) O) (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    biasF c g ξ₁ ξ₂ =
      (n : ℝ) / (√(n : ℝ) * √(normSq (bOfY c (M0 c g ξ₁ ξ₂ *ᵥ hB c)))) *
        ∑ j, bOfY c (M0 c g ξ₁ ξ₂ *ᵥ hB c) j *
          (∫ v, psiS (√(wT c g v)) ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j)
              ∂stdGauss (Fin (n - 1)) -
            psiS √(vsig2 c (nodeS c g)) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j)) := by
  set s := nodeS c g
  set M₀ := M0 c g ξ₁ ξ₂
  set b := bOfY c (M₀ *ᵥ hB c)
  set κ := (n : ℝ) / (√(n : ℝ) * √(normSq b))
  have hK : ∀ v, ‖aLat c s v‖ ≤ O ^ 2 + 1 := by
    intro v
    have h2 := aLat_normSq_le hn c hs h1 v
    have : ‖aLat c s v‖ ≤ √(normSq (aLat c s v)) := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i; rw [Real.norm_eq_abs]; exact BstLean.Part170.abs_le_sqrt_normSq _ i
    refine this.trans ?_
    calc √(normSq (aLat c s v)) ≤ √(O ^ 2) := Real.sqrt_le_sqrt h2
      _ = |O| := Real.sqrt_sq_eq_abs O
      _ ≤ O ^ 2 + 1 := by nlinarith [abs_le_half_sq O, sq_abs O]
  unfold biasF
  have e1 : ∀ N, BstLean.Part170.exFn (BstLean.Part170.withA2 c (Mpl (hB c) (res (hB c) (a1Bar c s))
      (cOf (tA n) (hB c) ξ₁) (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) N)) g =
      flE (stdGauss (Fin (n - 1))) (aLat c s) (hB c) M₀ b
        (fun j => psiS √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)) κ N :=
    fun N => exFn_Mpl hn c g hK _ _ N
  rw [integral_congr_ae (Eventually.of_forall e1)]
  unfold flE
  rw [vmean_aLat]
  have hint : ∀ j, Integrable (fun N => b j * (∫ v, relu ((M₀ *ᵥ aLat c s v) j +
      (N *ᵥ perp (res (hB c) (a1Bar c s)) (perp (hB c) (aLat c s v))) j) ∂stdGauss (Fin (n - 1)) -
        psiS √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j))) (gaussMat (mA n) (mA n) (tA n)) := by
    intro j
    obtain ⟨m1, b1, m2, b2⟩ := node_bounds hn c g hs h1 M₀ j
    have := (swap_row (μ := stdGauss (Fin (n - 1))) BstLean.Part130.continuous_relu relu_abs_le m1 b1 m2 b2
      (sq_nonneg O) (tA n) j).1
    exact (this.sub (integrable_const _)).const_mul _
  rw [integral_const_mul, integral_finsetSum _ fun j _ => hint j]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨m1, b1, m2, b2⟩ := node_bounds hn c g hs h1 M₀ j
  obtain ⟨hi, he⟩ := swap_row (μ := stdGauss (Fin (n - 1))) BstLean.Part130.continuous_relu
    relu_abs_le m1 b1 m2 b2 (sq_nonneg O) (tA n) j
  rw [integral_const_mul, integral_sub hi (integrable_const _), he]
  simp only [integral_const, probReal_univ, one_smul]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only; rw [sqrt_wT]
  rfl

/-- **The energy bias as a sum of row biases.** -/
theorem biasW_rows (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (h1 : OpB (A1 c) O) (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    biasW c g ξ₁ ξ₂ =
      ∑ j, (∫ v, G2 (√(wT c g v)) ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j)
              ∂stdGauss (Fin (n - 1)) -
            G2 √(vsig2 c (nodeS c g)) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j)) := by
  set s := nodeS c g
  set M₀ := M0 c g ξ₁ ξ₂
  have hK : ∀ v, ‖aLat c s v‖ ≤ O ^ 2 + 1 := by
    intro v
    have h2 := aLat_normSq_le hn c hs h1 v
    have : ‖aLat c s v‖ ≤ √(normSq (aLat c s v)) := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i; rw [Real.norm_eq_abs]; exact BstLean.Part170.abs_le_sqrt_normSq _ i
    refine this.trans ?_
    calc √(normSq (aLat c s v)) ≤ √(O ^ 2) := Real.sqrt_le_sqrt h2
      _ = |O| := Real.sqrt_sq_eq_abs O
      _ ≤ O ^ 2 + 1 := by nlinarith [abs_le_half_sq O, sq_abs O]
  unfold biasW
  have e1 : ∀ N, BstLean.Part170.exWn (BstLean.Part170.withA2 c (Mpl (hB c) (res (hB c) (a1Bar c s))
      (cOf (tA n) (hB c) ξ₁) (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) N)) g =
      flQ (stdGauss (Fin (n - 1))) (aLat c s) (hB c) M₀ N -
        ∑ j, G2 √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j) :=
    fun N => exWn_Mpl hn c g hK _ _ N
  rw [integral_congr_ae (Eventually.of_forall e1)]
  unfold flQ
  rw [vmean_aLat]
  have hint : ∀ j, Integrable (fun N => ∫ v, relu ((M₀ *ᵥ aLat c s v) j +
      (N *ᵥ perp (res (hB c) (a1Bar c s)) (perp (hB c) (aLat c s v))) j) ^ 2
        ∂stdGauss (Fin (n - 1))) (gaussMat (mA n) (mA n) (tA n)) := by
    intro j
    obtain ⟨m1, b1, m2, b2⟩ := node_bounds hn c g hs h1 M₀ j
    exact (swap_row (μ := stdGauss (Fin (n - 1))) (show Continuous (fun x : ℝ => relu x ^ 2) from BstLean.Part130.continuous_relu.pow 2)
      relu_sq_abs_le m1 b1 m2 b2 (sq_nonneg O) (tA n) j).1
  rw [integral_sub (integrable_finsetSum _ fun j _ => hint j) (integrable_const _),
    integral_finsetSum _ fun j _ => hint j]
  simp only [integral_const, probReal_univ, one_smul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨m1, b1, m2, b2⟩ := node_bounds hn c g hs h1 M₀ j
  obtain ⟨hi, he⟩ := swap_row (μ := stdGauss (Fin (n - 1))) (show Continuous (fun x : ℝ => relu x ^ 2) from BstLean.Part130.continuous_relu.pow 2)
    relu_sq_abs_le m1 b1 m2 b2 (sq_nonneg O) (tA n) j
  rw [he]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only; rw [sqrt_wT]
  rfl

end BstLean.Part171
