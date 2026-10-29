import BstLean.Part153JDefs
import BstLean.Part153Inv
import BstLean.Part152OpMom
import BstLean.Part130Mean
import BstLean.Part130Layer
import Mathlib.Analysis.Matrix.Order

/-!
# Part 153, Lemma PP: moments of the tangent Jacobian and the Markov step

Paper source: `proofs/option-n/theorem5-05-covariance.tex`, Lemma PP. This file proves a WEAKER
form of (i) (no masks: the constant is `jW n P = 2·(1 + n^{-1/2} + 𝔪_P/n)²` in place of
`j_{n,p}`), and the Markov step (ii) in a form that takes the moment bound as a hypothesis.

* §1 `opN_mul_le`, `opN_diagonal_mul_le`, `opN_mul_projT_le`, `jac_eq`, `tanB`, `jacT_le`,
  `opN_tanB_le`, `opN_jacT_le`: algebra of the operator norm.
* §2 `opN_mul_moment`: the fact (G2) for a restriction (the Gram trick):
  `E opN(A·B)^{2P} ≤ opN(B)^{2P}·(√v·(√p + √n + 𝔪_P))^{2P}`, `n` the number of columns of `B`.
* §3 `nuA n`: the distribution of `(A₁, A₂)`; `lemmaPP_i_weak`, `lemmaPP_i_weak_integral`.
* §4 `markov_Xi`, `lemmaPP_ii_Xi4`, `lemmaPP_ii_XiS`: the Markov step.
* §5 `lemmaPP_Xi4_weak`, `lemmaPP_XiS_weak`: the corollaries.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal MatrixOrder
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac mask)

/-! ## §1 Algebra of the operator norm -/

section alg

variable {p q r : ℕ}

/-- If `|M v| ≤ C·|v|` for every `v`, then `opN M ≤ C`. -/
lemma opN_le_of_forall (M : Matrix (Fin p) (Fin q) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : Fin q → ℝ, nrm (M *ᵥ v) ≤ C * nrm v) : opN M ≤ C := by
  by_cases hne : (opSet M).Nonempty
  · refine csSup_le hne ?_
    rintro x ⟨u, v, hu, hv, rfl⟩
    have h1 := (le_abs_self _).trans (abs_dot_le_nrm u (M *ᵥ v))
    have hu' : nrm u = 1 := by unfold nrm normSq; rw [hu, Real.sqrt_one]
    have hv' : nrm v = 1 := by unfold nrm normSq; rw [hv, Real.sqrt_one]
    have h2 := h v
    rw [hv', mul_one] at h2
    rw [hu', one_mul] at h1
    exact h1.trans h2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold opN
    rw [hne, Real.sSup_empty]
    exact hC

/-- **The operator norm is submultiplicative.** -/
theorem opN_mul_le (A : Matrix (Fin p) (Fin q) ℝ) (B : Matrix (Fin q) (Fin r) ℝ) :
    opN (A * B) ≤ opN A * opN B := by
  refine opN_le_of_forall _ (mul_nonneg (opN_nonneg A) (opN_nonneg B)) fun v => ?_
  rw [← Matrix.mulVec_mulVec]
  calc nrm (A *ᵥ (B *ᵥ v)) ≤ opN A * nrm (B *ᵥ v) := nrm_mulVec_le A _
    _ ≤ opN A * (opN B * nrm v) :=
        mul_le_mul_of_nonneg_left (nrm_mulVec_le B v) (opN_nonneg A)
    _ = opN A * opN B * nrm v := by ring

lemma nrm_diagonal_mulVec_le (d : Fin q → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (w : Fin q → ℝ) : nrm (Matrix.diagonal d *ᵥ w) ≤ nrm w := by
  unfold nrm normSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [Matrix.mulVec_diagonal, mul_pow]
  have h1 : d i ^ 2 ≤ 1 := pow_le_one₀ (hd0 i) (hd1 i)
  nlinarith [sq_nonneg (w i)]

/-- A diagonal matrix with entries in `[0, 1]` on the left does not increase the operator
norm. -/
theorem opN_diagonal_mul_le (d : Fin q → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (B : Matrix (Fin q) (Fin r) ℝ) : opN (Matrix.diagonal d * B) ≤ opN B := by
  refine opN_le_of_forall _ (opN_nonneg B) fun v => ?_
  rw [← Matrix.mulVec_mulVec]
  exact (nrm_diagonal_mulVec_le d hd0 hd1 _).trans (nrm_mulVec_le B v)

lemma projT_mulVec (x v : Fin q → ℝ) : projT x *ᵥ v = v - (x ⬝ᵥ v) • x := by
  unfold projT
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma normSq_projT_mulVec_le {x : Fin q → ℝ} (hx : normSq x = 1) (v : Fin q → ℝ) :
    normSq (projT x *ᵥ v) ≤ normSq v := by
  rw [projT_mulVec]
  have e : normSq (v - (x ⬝ᵥ v) • x) = normSq v - (x ⬝ᵥ v) ^ 2 := by
    unfold normSq at hx ⊢
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : ∀ i, (v i - x ⬝ᵥ v * x i) ^ 2 =
        v i ^ 2 - 2 * (x ⬝ᵥ v) * (x i * v i) + (x ⬝ᵥ v) ^ 2 * x i ^ 2 := fun i => by ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx]
    have h2 : ∑ i, x i * v i = x ⬝ᵥ v := rfl
    rw [h2]
    ring
  rw [e]
  nlinarith [sq_nonneg (x ⬝ᵥ v)]

/-- `opN (Π_x) ≤ 1` for a unit vector `x`. -/
theorem opN_projT_le {x : Fin q → ℝ} (hx : normSq x = 1) : opN (projT x) ≤ 1 := by
  refine opN_le_of_forall _ zero_le_one fun v => ?_
  rw [one_mul]
  exact Real.sqrt_le_sqrt (normSq_projT_mulVec_le hx v)

/-- `opN (B·Π_x) ≤ opN B` for a unit vector `x`. -/
theorem opN_mul_projT_le (B : Matrix (Fin p) (Fin q) ℝ) {x : Fin q → ℝ} (hx : normSq x = 1) :
    opN (B * projT x) ≤ opN B := by
  have h := (opN_mul_le B (projT x)).trans
    (mul_le_mul_of_nonneg_left (opN_projT_le hx) (opN_nonneg B))
  rwa [mul_one] at h

lemma mask_le_one (t : ℝ) : mask t ≤ 1 := by
  unfold mask; split_ifs <;> norm_num

end alg

section jacalg

variable {n m m₂ : ℕ}

/-- **The Jacobian matrix as a product**: `jac A₁ A₂ y = D₂·(A₂·(D₁·A₁))`. -/
theorem jac_eq (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (y : Fin n → ℝ) :
    jac A₁ A₂ y = Matrix.diagonal (fun j => mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j)) *
      (A₂ * (Matrix.diagonal (fun i => mask ((A₁ *ᵥ y) i)) * A₁)) := by
  ext j l
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [jac, Matrix.of_apply, Matrix.diagonal_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `B = D₁·A₁·Π_x`: the first layer of the tangent Jacobian. -/
noncomputable def tanB (A₁ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.diagonal (fun i => mask ((A₁ *ᵥ x) i)) * A₁ * projT x

lemma jacT_eq (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (x : Fin n → ℝ) :
    jacT A₁ A₂ x = Matrix.diagonal (fun j => mask ((A₂ *ᵥ reluV (A₁ *ᵥ x)) j)) *
      (A₂ * tanB A₁ x) := by
  unfold jacT tanB
  rw [jac_eq]
  simp only [Matrix.mul_assoc]

/-- `opN (𝒥(x)Π_x) ≤ opN (A₂·B)`, `B = tanB A₁ x`. (No condition on `x` is needed.) -/
theorem jacT_le (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (x : Fin n → ℝ) : opN (jacT A₁ A₂ x) ≤ opN (A₂ * tanB A₁ x) := by
  rw [jacT_eq]
  exact opN_diagonal_mul_le _ (fun _ => BstLean.Part151.mask_nonneg _) (fun _ => mask_le_one _) _

/-- `opN (tanB A₁ x) ≤ opN A₁` for a unit vector `x`. -/
theorem opN_tanB_le (A₁ : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} (hx : normSq x = 1) :
    opN (tanB A₁ x) ≤ opN A₁ := by
  unfold tanB
  exact (opN_mul_projT_le _ hx).trans
    (opN_diagonal_mul_le _ (fun _ => BstLean.Part151.mask_nonneg _) (fun _ => mask_le_one _) _)

/-- `opN (𝒥(x)Π_x) ≤ opN A₂·opN A₁` for a unit vector `x`. -/
theorem opN_jacT_le (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    {x : Fin n → ℝ} (hx : normSq x = 1) : opN (jacT A₁ A₂ x) ≤ opN A₂ * opN A₁ :=
  (jacT_le A₁ A₂ x).trans ((opN_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (opN_tanB_le A₁ hx) (opN_nonneg A₂)))

end jacalg

/-! ## §2 The fact (G2) for a restriction (the Gram trick) -/

section gram

variable {p m n : ℕ}

/-- A square matrix `R` with the same Gram matrix as `B`. -/
lemma exists_gram_sqrt (B : Matrix (Fin m) (Fin n) ℝ) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, Rᵀ * R = Bᵀ * B := by
  have hS : (Bᵀ * B).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self B
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.nonneg
  refine ⟨R, ?_⟩
  rw [hR, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

lemma normSq_mulVec_gram {k : ℕ} (R : Matrix (Fin k) (Fin n) ℝ) (v : Fin n → ℝ) :
    normSq (R *ᵥ v) = v ⬝ᵥ ((Rᵀ * R) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [normSq, dotProduct, sq]

lemma opN_le_of_gram {k : ℕ} {B : Matrix (Fin m) (Fin n) ℝ} {R : Matrix (Fin k) (Fin n) ℝ}
    (h : Rᵀ * R = Bᵀ * B) : opN R ≤ opN B := by
  refine opN_le_of_forall _ (opN_nonneg B) fun v => ?_
  have e : nrm (R *ᵥ v) = nrm (B *ᵥ v) := by
    unfold nrm
    rw [normSq_mulVec_gram, normSq_mulVec_gram, h]
  rw [e]
  exact nrm_mulVec_le B v

/-- **The fact (G2) for a restriction**: for a fixed `m × n` matrix `B` and a `p × m` Gaussian
matrix `A` with variance `v`: `E opN(A·B)^{2P} ≤ opN(B)^{2P}·(√v·(√p + √n + 𝔪_P))^{2P}`.
The number `n` is the number of COLUMNS of `B`. -/
theorem opN_mul_moment (B : Matrix (Fin m) (Fin n) ℝ) {v : ℝ} (hv : 0 ≤ v) {P : ℕ}
    (hP : 1 ≤ P) :
    Integrable (fun A : Matrix (Fin p) (Fin m) ℝ => opN (A * B) ^ (2 * P)) (gaussMat p m v) ∧
    ∫ A : Matrix (Fin p) (Fin m) ℝ, opN (A * B) ^ (2 * P) ∂gaussMat p m v ≤
      opN B ^ (2 * P) * (√v * (√p + √n + gaussMomConst P)) ^ (2 * P) := by
  obtain ⟨R, hR⟩ := exists_gram_sqrt B
  have hRB : opN R ≤ opN B := opN_le_of_gram hR
  -- the square case
  obtain ⟨hI0, hB0⟩ := opN_moment (p := p) (q := n) hv hP
  have hcont : Continuous fun M : Matrix (Fin p) (Fin n) ℝ => opN (M * R) ^ (2 * P) :=
    (opN_continuous.comp (continuous_id.matrix_mul continuous_const)).pow _
  have hdom : ∀ M : Matrix (Fin p) (Fin n) ℝ,
      opN (M * R) ^ (2 * P) ≤ opN M ^ (2 * P) * opN B ^ (2 * P) := by
    intro M
    rw [← mul_pow]
    exact pow_le_pow_left₀ (opN_nonneg _) ((opN_mul_le M R).trans
      (mul_le_mul_of_nonneg_left hRB (opN_nonneg M))) _
  have hIR : Integrable (fun M : Matrix (Fin p) (Fin n) ℝ => opN (M * R) ^ (2 * P))
      (gaussMat p n v) := by
    refine Integrable.mono' (hI0.mul_const (opN B ^ (2 * P))) hcont.aestronglyMeasurable
      (ae_of_all _ fun M => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (opN_nonneg _) _)]
    exact hdom M
  have hBR : ∫ M : Matrix (Fin p) (Fin n) ℝ, opN (M * R) ^ (2 * P) ∂gaussMat p n v ≤
      opN B ^ (2 * P) * (√v * (√p + √n + gaussMomConst P)) ^ (2 * P) := by
    calc ∫ M : Matrix (Fin p) (Fin n) ℝ, opN (M * R) ^ (2 * P) ∂gaussMat p n v
        ≤ ∫ M : Matrix (Fin p) (Fin n) ℝ, opN M ^ (2 * P) * opN B ^ (2 * P) ∂gaussMat p n v :=
          integral_mono hIR (hI0.mul_const _) hdom
      _ = (∫ M : Matrix (Fin p) (Fin n) ℝ, opN M ^ (2 * P) ∂gaussMat p n v) *
          opN B ^ (2 * P) := integral_mul_const _ _
      _ ≤ (√v * (√p + √n + gaussMomConst P)) ^ (2 * P) * opN B ^ (2 * P) :=
          mul_le_mul_of_nonneg_right hB0 (pow_nonneg (opN_nonneg _) _)
      _ = _ := mul_comm _ _
  -- transfer by the Gram matrix
  let φ : (Fin n → Fin p → ℝ) → ℝ := fun F => opN (Matrix.of fun i a => F a i) ^ (2 * P)
  have hφ : Measurable φ := by
    have h1 : Measurable fun F : Fin n → Fin p → ℝ =>
        (Matrix.of fun i a => F a i : Matrix (Fin p) (Fin n) ℝ) :=
      measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun a =>
        (measurable_pi_apply i).comp (measurable_pi_apply a)
    exact ((opN_continuous.measurable.comp h1).pow_const _)
  have hfam := gaussMat_family (m := p) v (fun a i => B i a) (fun a j => R j a) (by
    intro a b
    have := congrFun (congrFun hR a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    exact this.symm)
  have hm : ∀ (k : ℕ) (C : Matrix (Fin k) (Fin n) ℝ),
      Measurable fun (M : Matrix (Fin p) (Fin k) ℝ) (a : Fin n) => M *ᵥ (fun i => C i a) :=
    fun k C => measurable_pi_iff.mpr fun a =>
      (Continuous.matrix_mulVec continuous_id continuous_const).measurable
  have e1 : ∀ (k : ℕ) (C : Matrix (Fin k) (Fin n) ℝ) (A : Matrix (Fin p) (Fin k) ℝ),
      opN (A * C) ^ (2 * P) = φ (fun a => A *ᵥ (fun i => C i a)) := by
    intro k C A
    rfl
  have hfun : ∀ (k : ℕ) (C : Matrix (Fin k) (Fin n) ℝ),
      (fun A : Matrix (Fin p) (Fin k) ℝ => opN (A * C) ^ (2 * P)) =
        φ ∘ fun (M : Matrix (Fin p) (Fin k) ℝ) (a : Fin n) => M *ᵥ (fun i => C i a) := by
    intro k C
    funext A
    exact e1 k C A
  constructor
  · rw [hfun m B, ← integrable_map_measure hφ.aestronglyMeasurable (hm m B).aemeasurable, hfam,
      integrable_map_measure hφ.aestronglyMeasurable (hm n R).aemeasurable, ← hfun n R]
    exact hIR
  · have i1 : ∫ A : Matrix (Fin p) (Fin m) ℝ, opN (A * B) ^ (2 * P) ∂gaussMat p m v =
        ∫ F, φ F ∂(gaussMat p m v).map (fun M a => M *ᵥ (fun i => B i a)) := by
      rw [integral_map (hm m B).aemeasurable hφ.aestronglyMeasurable]
      rfl
    have i2 : ∫ M : Matrix (Fin p) (Fin n) ℝ, opN (M * R) ^ (2 * P) ∂gaussMat p n v =
        ∫ F, φ F ∂(gaussMat p n v).map (fun M a => M *ᵥ (fun j => R j a)) := by
      rw [integral_map (hm n R).aemeasurable hφ.aestronglyMeasurable]
      rfl
    rw [i1, hfam, ← i2]
    exact hBR

end gram

/-! ## §3 Lemma PP (i), weak form -/

section ppi

variable {n m m₂ : ℕ}

/-- The tangent Jacobian is jointly measurable in the weights and the point. -/
lemma measurable_jacT_joint :
    Measurable (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m₂) (Fin m) ℝ) × (Fin n → ℝ) =>
      jacT q.1.1 q.1.2 q.2) := by
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
  simp only [jacT, jac, projT, Matrix.mul_apply, Matrix.of_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, reluV, relu]
  have hmask := BstLean.Part151.measurable_mask
  fun_prop

/-- `(A₁, A₂, x) ↦ opN (𝒥(x)Π_x)` is jointly measurable. -/
lemma measurable_opN_jacT_joint :
    Measurable (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m₂) (Fin m) ℝ) × (Fin n → ℝ) =>
      opN (jacT q.1.1 q.1.2 q.2)) :=
  opN_continuous.measurable.comp measurable_jacT_joint

/-- `(A₁, A₂) ↦ opN (𝒥(x)Π_x)` is measurable, for a fixed `x`. -/
lemma measurable_opN_jacT (x : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m₂) (Fin m) ℝ =>
      opN (jacT θ.1 θ.2 x)) := by
  have hf : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m₂) (Fin m) ℝ =>
      (θ, x)) := measurable_id.prodMk measurable_const
  have h := (measurable_opN_jacT_joint (n := n) (m := m) (m₂ := m₂)).comp hf
  simpa only [Function.comp_def] using h

/-- `(θ, ξ) ↦ opN (𝒥(x)Π_x)` at `x = sphPt (c + τξ)` is jointly measurable. -/
lemma measurable_opN_jacT_sph (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m₂) (Fin m) ℝ) × (Fin n → ℝ) =>
      opN (jacT q.1.1 q.1.2 (sphPt (c + τ • q.2)))) := by
  have hf : Measurable (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m₂) (Fin m) ℝ) ×
      (Fin n → ℝ) => (q.1, sphPt (c + τ • q.2))) :=
    measurable_fst.prodMk
      (measurable_sphPt.comp (measurable_const.add (measurable_snd.const_smul τ)))
  have h := (measurable_opN_jacT_joint (n := n) (m := m) (m₂ := m₂)).comp hf
  simpa only [Function.comp_def] using h

end ppi

/-- **The distribution of `(A₁, A₂)`**: the first two weight matrices of the Agent network. -/
noncomputable abbrev nuA (n : ℕ) :
    Measure (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  (gaussMat (mA n) n (2 / (n : ℝ))).prod (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)))

/-- The weak constant `2·(1 + n^{-1/2} + 𝔪_P/n)²` (it takes the place of `j_{n,p}`). -/
noncomputable def jW (n P : ℕ) : ℝ := 2 * (1 + 1 / √(n : ℝ) + gaussMomConst P / n) ^ 2

lemma jW_nonneg (n P : ℕ) : 0 ≤ jW n P := by unfold jW; positivity

lemma c_mul_c {n : ℕ} (hn : 1 ≤ n) (g : ℝ) :
    (√(2 / (n : ℝ)) * (√((mA n : ℕ) : ℝ) + √(n : ℝ) + g)) *
      (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √(n : ℝ) + g)) =
    √(n : ℝ) * (2 * (1 + 1 / √(n : ℝ) + g / n) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have h2 : √(2 : ℝ) * √(2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
  have e1 : √(2 / (n : ℝ)) = √2 / √(n : ℝ) := Real.sqrt_div (by norm_num) _
  have e2 : √(2 / ((mA n : ℕ) : ℝ)) = √2 / (n : ℝ) := by
    rw [Real.sqrt_div (by norm_num), sqrt_mA]
  rw [e1, e2, sqrt_mA]
  generalize √(n : ℝ) = s at hs hss ⊢
  rw [← hss]
  have : √(2 : ℝ) / s * (s * s + s + g) * (√2 / (s * s) * (s * s + s + g)) =
      (√2 * √2) * ((s * s + s + g) ^ 2 / (s * s * s)) := by
    field_simp
  rw [this, h2]
  field_simp

/-- **Lemma PP (i), weak form**: for a unit vector `x`,
`E opN(𝒥(x)Π_x)^{2P} ≤ (√n·jW n P)^{2P}`. -/
theorem lemmaPP_i_weak {n : ℕ} (hn : 1 ≤ n) {P : ℕ} (hP : 1 ≤ P) {x : Fin n → ℝ}
    (hx : normSq x = 1) :
    ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P)) ∂nuA n ≤
      ENNReal.ofReal ((√(n : ℝ) * jW n P) ^ (2 * P)) := by
  have hmeas : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P))) :=
    ((measurable_opN_jacT x).pow_const _).ennreal_ofReal
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hv2 : (0 : ℝ) ≤ 2 / ((mA n : ℕ) : ℝ) := by positivity
  have hv1 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have inner : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
      ∫⁻ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ, ENNReal.ofReal (opN (jacT A₁ A₂ x) ^ (2 * P))
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      ENNReal.ofReal (opN A₁ ^ (2 * P) * (√(2 / ((mA n : ℕ) : ℝ)) *
        (√((mA n : ℕ) : ℝ) + √(n : ℝ) + gaussMomConst P)) ^ (2 * P)) := by
    intro A₁
    obtain ⟨hI, hB⟩ := opN_mul_moment (p := mA n) (tanB A₁ x) hv2 hP
    calc ∫⁻ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
          ENNReal.ofReal (opN (jacT A₁ A₂ x) ^ (2 * P))
            ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))
        ≤ ∫⁻ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
          ENNReal.ofReal (opN (A₂ * tanB A₁ x) ^ (2 * P))
            ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) :=
          lintegral_mono fun A₂ => ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ (opN_nonneg _) (jacT_le A₁ A₂ x) _)
      _ = ENNReal.ofReal (∫ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
            opN (A₂ * tanB A₁ x) ^ (2 * P) ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) :=
          (ofReal_integral_eq_lintegral_ofReal hI
            (ae_of_all _ fun _ => pow_nonneg (opN_nonneg _) _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hB.trans (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (opN_nonneg _) (opN_tanB_le A₁ hx) _)
            (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _)
              (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
                (gaussMomConst_nonneg P))) _)))
  obtain ⟨hI1, hB1⟩ := opN_moment (p := mA n) (q := n) hv1 hP
  have hc2 : 0 ≤ (√(2 / ((mA n : ℕ) : ℝ)) *
      (√((mA n : ℕ) : ℝ) + √(n : ℝ) + gaussMomConst P)) ^ (2 * P) :=
    pow_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (gaussMomConst_nonneg P))) _
  calc ∫⁻ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, ∫⁻ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
        ENNReal.ofReal (opN (jacT A₁ A₂ x) ^ (2 * P))
          ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, ENNReal.ofReal (opN A₁ ^ (2 * P) *
          (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √(n : ℝ) + gaussMomConst P)) ^ (2 * P))
          ∂gaussMat (mA n) n (2 / (n : ℝ)) := lintegral_mono inner
    _ = ENNReal.ofReal (∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, opN A₁ ^ (2 * P) *
          (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √(n : ℝ) + gaussMomConst P)) ^ (2 * P)
          ∂gaussMat (mA n) n (2 / (n : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal (hI1.mul_const _)
          (ae_of_all _ fun _ => mul_nonneg (pow_nonneg (opN_nonneg _) _) hc2)).symm
    _ ≤ ENNReal.ofReal ((√(2 / (n : ℝ)) * (√((mA n : ℕ) : ℝ) + √(n : ℝ) + gaussMomConst P)) ^
          (2 * P) * (√(2 / ((mA n : ℕ) : ℝ)) *
            (√((mA n : ℕ) : ℝ) + √(n : ℝ) + gaussMomConst P)) ^ (2 * P)) := by
        rw [integral_mul_const]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hB1 hc2)
    _ = ENNReal.ofReal ((√(n : ℝ) * jW n P) ^ (2 * P)) := by
        rw [← mul_pow, c_mul_c hn]
        rfl

/-- **Lemma PP (i), weak form, with the Bochner integral.** -/
theorem lemmaPP_i_weak_integral {n : ℕ} (hn : 1 ≤ n) {P : ℕ} (hP : 1 ≤ P) {x : Fin n → ℝ}
    (hx : normSq x = 1) :
    Integrable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      opN (jacT θ.1 θ.2 x) ^ (2 * P)) (nuA n) ∧
    ∫ θ, opN (jacT θ.1 θ.2 x) ^ (2 * P) ∂nuA n ≤ (√(n : ℝ) * jW n P) ^ (2 * P) := by
  have h5 := lemmaPP_i_weak hn hP hx
  have hnn : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
      0 ≤ opN (jacT θ.1 θ.2 x) ^ (2 * P) := fun θ => pow_nonneg (opN_nonneg _) _
  have hsm : AEStronglyMeasurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => opN (jacT θ.1 θ.2 x) ^ (2 * P)) (nuA n) :=
    ((measurable_opN_jacT x).pow_const _).aestronglyMeasurable
  refine ⟨⟨hsm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).2
    (lt_of_le_of_lt h5 ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hsm]
  exact ENNReal.toReal_le_of_le_ofReal
    (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (jW_nonneg n P)) _) h5

/-! ## §4 Lemma PP (ii): the Markov step -/

section markov

/-- `X = opN(𝒥(x)Π_x)²/|y|²` at `y = c + τξ`, `x = sphPt y`. -/
noncomputable def Xq {n : ℕ}
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹

variable {n : ℕ}

lemma Xq_nonneg (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : 0 ≤ Xq θ c τ ξ :=
  mul_nonneg (sq_nonneg _) (inv_nonneg.2 (normSq_nonneg _))

lemma measurable_Xq_joint (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) ×
      (Fin n → ℝ) => Xq q.1 c τ q.2) := by
  unfold Xq
  exact ((measurable_opN_jacT_sph c τ).pow_const 2).mul
    ((BstLean.Part130.measurable_normSq.comp
      (measurable_const.add (measurable_snd.const_smul τ))).inv)

/-- The comparison of the `L^q` and `L^P` norms on a probability space, for natural
exponents. -/
lemma lp_mono_nat {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {q P : ℕ} (hq : 1 ≤ q)
    (hqP : q ≤ P) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ) ^ (1 / (q : ℝ)) ≤
      (∫⁻ ω, ENNReal.ofReal (f ω ^ P) ∂μ) ^ (1 / (P : ℝ)) := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le (f := f) (p := (q : ℝ)) (q := (P : ℝ))
    (by exact_mod_cast hq) (by exact_mod_cast hqP) μ hf.aestronglyMeasurable
  simp only [eLpNorm'_eq_lintegral_enorm] at h
  have e : ∀ (k : ℕ) (ω : Ω), ‖f ω‖ₑ ^ (k : ℝ) = ENNReal.ofReal (f ω ^ k) := by
    intro k ω
    rw [Real.enorm_eq_ofReal (hf0 ω), ENNReal.rpow_natCast, ENNReal.ofReal_pow (hf0 ω)]
  simpa only [e] using h

lemma ofReal_integral_le_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) : ENNReal.ofReal (∫ ω, f ω ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  by_cases hI : Integrable f μ
  · exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hf0))
  · rw [integral_undef hI, ENNReal.ofReal_zero]
    exact bot_le

/-- `Ξ₄^P ≤ (t·τ²)^P·E_ξ X^P` for `P ≥ 2`. -/
lemma ofReal_Xi4_pow_le {P : ℕ} (hP : 2 ≤ P)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) :
    ENNReal.ofReal (Xi4 θ.1 θ.2 c τ) ^ P ≤ ENNReal.ofReal (2 / ((mA n : ℕ) : ℝ) * τ ^ 2) ^ P *
      ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n) := by
  have hmeas : Measurable (fun ξ : Fin n → ℝ => Xq θ c τ ξ) := by
    have hf : Measurable (fun ξ : Fin n → ℝ => (θ, ξ)) := measurable_const.prodMk measurable_id
    have h := (measurable_Xq_joint c τ).comp hf
    simpa only [Function.comp_def] using h
  have e : (fun ξ : Fin n → ℝ => opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 4 *
      (normSq (c + τ • ξ))⁻¹ ^ 2) = fun ξ => Xq θ c τ ξ ^ 2 := by
    funext ξ; unfold Xq; ring
  unfold Xi4
  rw [e, ENNReal.ofReal_mul (by positivity), mul_pow]
  refine mul_le_mul_right ?_ _
  have h0 : 0 ≤ ∫ ξ, Xq θ c τ ξ ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => sq_nonneg _
  have h1 : ENNReal.ofReal (∫ ξ, Xq θ c τ ξ ^ 2 ∂stdGauss (Fin n)) ≤
      ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ 2) ∂stdGauss (Fin n) :=
    ofReal_integral_le_lintegral fun ξ => sq_nonneg _
  have h2 := lp_mono_nat (μ := stdGauss (Fin n)) hmeas (Xq_nonneg θ c τ) (q := 2) (P := P)
    (by norm_num) hP
  simp only [Nat.cast_ofNat] at h2
  have h3 : ENNReal.ofReal (√(∫ ξ, Xq θ c τ ξ ^ 2 ∂stdGauss (Fin n))) ≤
      (∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n)) ^ (1 / (P : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num)]
    exact (ENNReal.rpow_le_rpow h1 (by norm_num)).trans h2
  calc ENNReal.ofReal (√(∫ ξ, Xq θ c τ ξ ^ 2 ∂stdGauss (Fin n))) ^ P
      ≤ ((∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n)) ^ (1 / (P : ℝ))) ^ P :=
        pow_le_pow_left' h3 P
    _ = _ := enn_root_pow _ (by omega)

/-- `Ξ^P ≤ (t·τ²)^P·E_ξ X^P` for `P ≥ 1`. -/
lemma ofReal_XiS_pow_le {P : ℕ} (hP : 1 ≤ P)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) :
    ENNReal.ofReal (XiS θ.1 θ.2 c τ) ^ P ≤ ENNReal.ofReal (2 / ((mA n : ℕ) : ℝ) * τ ^ 2) ^ P *
      ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n) := by
  have hmeas : Measurable (fun ξ : Fin n → ℝ => Xq θ c τ ξ) := by
    have hf : Measurable (fun ξ : Fin n → ℝ => (θ, ξ)) := measurable_const.prodMk measurable_id
    have h := (measurable_Xq_joint c τ).comp hf
    simpa only [Function.comp_def] using h
  have e : (fun ξ : Fin n → ℝ => opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2 *
      (normSq (c + τ • ξ))⁻¹) = fun ξ => Xq θ c τ ξ := rfl
  unfold XiS
  rw [e, ENNReal.ofReal_mul (by positivity), mul_pow]
  refine mul_le_mul_right ?_ _
  have h1 : ENNReal.ofReal (∫ ξ, Xq θ c τ ξ ∂stdGauss (Fin n)) ≤
      ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ) ∂stdGauss (Fin n) :=
    ofReal_integral_le_lintegral (Xq_nonneg θ c τ)
  have h2 := lp_mono_nat (μ := stdGauss (Fin n)) hmeas (Xq_nonneg θ c τ) (q := 1) (P := P)
    le_rfl hP
  simp only [Nat.cast_one, pow_one, div_one, ENNReal.rpow_one] at h2
  calc ENNReal.ofReal (∫ ξ, Xq θ c τ ξ ∂stdGauss (Fin n)) ^ P
      ≤ ((∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n)) ^ (1 / (P : ℝ))) ^ P :=
        pow_le_pow_left' (h1.trans h2) P
    _ = _ := enn_root_pow _ (by omega)

/-- Tonelli and the moment bound at each unit vector: `E_θ E_ξ X^P ≤ (√n·j)^{2P}·E|y|^{-2P}`. -/
lemma lintegral_Xq_le {P : ℕ} (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {j : ℝ}
    (hmom : ∀ x : Fin n → ℝ, normSq x = 1 →
      ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P)) ∂nuA n ≤
        ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P))) :
    ∫⁻ θ, ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n) ∂nuA n ≤
      ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)) *
        ENNReal.ofReal (∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ P ∂stdGauss (Fin n)) := by
  have hn : 1 ≤ n := by omega
  have hmeas : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal (Xq q.1 c τ q.2 ^ P)) :=
    ((measurable_Xq_joint c τ).pow_const _).ennreal_ofReal
  rw [lintegral_lintegral_swap (f := fun θ ξ => ENNReal.ofReal (Xq θ c τ ξ ^ P))
    hmeas.aemeasurable]
  have hpt : ∀ ξ : Fin n → ℝ, ∫⁻ θ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂nuA n ≤
      ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)) *
        ENNReal.ofReal ((normSq (c + τ • ξ))⁻¹ ^ P) := by
    intro ξ
    have e : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
        ENNReal.ofReal (Xq θ c τ ξ ^ P) =
          ENNReal.ofReal (opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ (2 * P)) *
            ENNReal.ofReal ((normSq (c + τ • ξ))⁻¹ ^ P) := by
      intro θ
      rw [← ENNReal.ofReal_mul (pow_nonneg (opN_nonneg _) _)]
      congr 1
      unfold Xq
      rw [mul_pow, pow_mul]
    simp only [e]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    gcongr
    exact hmom _ (normSq_sphPt hn _)
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact (ofReal_integral_eq_lintegral_ofReal (invMoment_le hnP c hτ).1
    (ae_of_all _ fun ξ => pow_nonneg (inv_nonneg.2 (normSq_nonneg _)) _)).symm

/-- **The Markov step, in a general form**: `Ξ'` is any function of the weights with
`Ξ'^P ≤ (t·τ²)^P·E_ξ X^P`. -/
theorem markov_Xi {P : ℕ} (hP : 1 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {j : ℝ} (hj : 0 ≤ j)
    (hmom : ∀ x : Fin n → ℝ, normSq x = 1 →
      ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P)) ∂nuA n ≤
        ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)))
    (Ξ' : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ)
    (hΞ : ∀ θ, ENNReal.ofReal (Ξ' θ) ^ P ≤ ENNReal.ofReal (2 / ((mA n : ℕ) : ℝ) * τ ^ 2) ^ P *
      ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n))
    {M : ℝ} (hM : 0 < M) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < Ξ' θ} ≤
      (j ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P := by
  have hn : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) - 1 - 2 * P := by
    have : ((2 * P + 1 : ℕ) : ℝ) < n := by exact_mod_cast hnP
    push_cast at this
    linarith
  set K : ℝ := M * (2 / (n : ℝ)) / n with hK
  have hK0 : 0 < K := by positivity
  set a : ℝ := 2 / ((mA n : ℕ) : ℝ) * τ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  set D : ℝ := j ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M) with hD
  have hD0 : 0 ≤ D := by positivity
  let Z : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞ :=
    fun θ => ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n)
  have hZm : Measurable Z :=
    Measurable.lintegral_prod_right' (f := fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) => ENNReal.ofReal (Xq q.1 c τ q.2 ^ P))
      ((measurable_Xq_joint c τ).pow_const _).ennreal_ofReal
  have hsub : {θ | K < Ξ' θ} ⊆ {θ | ENNReal.ofReal K ^ P ≤ ENNReal.ofReal a ^ P * Z θ} := by
    intro θ hθ
    exact (pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_of_lt hθ)) P).trans (hΞ θ)
  have hmk := mul_meas_ge_le_lintegral (μ := nuA n)
    (f := fun θ => ENNReal.ofReal a ^ P * Z θ) (measurable_const.mul hZm) (ENNReal.ofReal K ^ P)
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)] at hmk
  have hZ := lintegral_Xq_le hnP c hτ hmom
  obtain ⟨-, hinv⟩ := invMoment_le hnP c hτ
  -- the real computation
  have hprod : ∏ i ∈ Finset.range P, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹ ≤
      (((n : ℝ) - 1 - 2 * P)⁻¹) ^ P := by
    have : ∏ i ∈ Finset.range P, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹ ≤
        ∏ _i ∈ Finset.range P, ((n : ℝ) - 1 - 2 * P)⁻¹ := by
      refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
      · have hi' : ((i : ℝ) + 1) ≤ P := by
          exact_mod_cast Finset.mem_range.1 hi
        exact inv_nonneg.2 (by linarith)
      · have hi' : ((i : ℝ) + 1) ≤ P := by
          exact_mod_cast Finset.mem_range.1 hi
        exact inv_anti₀ hd (by linarith)
    simpa using this
  have hI0 : 0 ≤ ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ P ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => pow_nonneg (inv_nonneg.2 (normSq_nonneg _)) _
  have hreal : a ^ P * ((√(n : ℝ) * j) ^ (2 * P) *
      ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ P ∂stdGauss (Fin n)) ≤ K ^ P * D ^ P := by
    have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
    have e1 : a ^ P * ((√(n : ℝ) * j) ^ (2 * P) *
        ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ P ∂stdGauss (Fin n)) =
        (2 / (n : ℝ) * j ^ 2) ^ P *
          (τ ^ (2 * P) * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ P ∂stdGauss (Fin n)) := by
      have e2 : (√(n : ℝ) * j) ^ (2 * P) = ((n : ℝ) * j ^ 2) ^ P := by
        rw [pow_mul, mul_pow, Real.sq_sqrt hn0.le]
      have e3 : τ ^ (2 * P) = (τ ^ 2) ^ P := pow_mul _ _ _
      have e4 : (2 / (n : ℝ) * j ^ 2) ^ P * (τ ^ 2) ^ P = a ^ P * ((n : ℝ) * j ^ 2) ^ P := by
        rw [← mul_pow, ← mul_pow, ha, hmA]
        congr 1
        field_simp
      rw [e2, e3, ← mul_assoc, ← mul_assoc, e4]
    rw [e1]
    have e5 : K ^ P * D ^ P = (2 / (n : ℝ) * j ^ 2) ^ P * (((n : ℝ) - 1 - 2 * P)⁻¹) ^ P := by
      rw [← mul_pow, ← mul_pow, hK, hD]
      congr 1
      field_simp
    rw [e5]
    exact mul_le_mul_of_nonneg_left (hinv.trans hprod) (by positivity)
  have hfin : ENNReal.ofReal K ^ P * nuA n {θ | K < Ξ' θ} ≤
      ENNReal.ofReal K ^ P * ENNReal.ofReal (D ^ P) := by
    calc ENNReal.ofReal K ^ P * nuA n {θ | K < Ξ' θ}
        ≤ ENNReal.ofReal K ^ P *
          nuA n {θ | ENNReal.ofReal K ^ P ≤ ENNReal.ofReal a ^ P * Z θ} :=
          by gcongr
      _ ≤ ENNReal.ofReal a ^ P * ∫⁻ θ, Z θ ∂nuA n := hmk
      _ ≤ ENNReal.ofReal a ^ P * (ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)) *
          ENNReal.ofReal (∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ P ∂stdGauss (Fin n))) :=
          by gcongr
      _ = ENNReal.ofReal (a ^ P * ((√(n : ℝ) * j) ^ (2 * P) *
          ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ P ∂stdGauss (Fin n))) := by
          rw [ENNReal.ofReal_mul (pow_nonneg ha0 P), ENNReal.ofReal_mul
            (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hj) _), ENNReal.ofReal_pow ha0]
      _ ≤ ENNReal.ofReal (K ^ P * D ^ P) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by rw [ENNReal.ofReal_mul (pow_nonneg hK0.le _), ENNReal.ofReal_pow hK0.le]
  have htop : ENNReal.ofReal K ^ P * ENNReal.ofReal (D ^ P) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono htop hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hK0.le,
    ENNReal.toReal_ofReal (pow_nonneg hD0 _)] at hr
  rw [measureReal_def]
  exact le_of_mul_le_mul_left hr (pow_pos hK0 P)

/-- **Lemma PP (ii), the Markov step for `Ξ₄`**, with the moment bound as a hypothesis. -/
theorem lemmaPP_ii_Xi4 {P : ℕ} (hP : 2 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {j : ℝ} (hj : 0 ≤ j)
    (hmom : ∀ x : Fin n → ℝ, normSq x = 1 →
      ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P)) ∂nuA n ≤
        ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)))
    {M : ℝ} (hM : 0 < M) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤
      (j ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P :=
  markov_Xi (by omega) hnP c hτ hj hmom (fun θ => Xi4 θ.1 θ.2 c τ)
    (fun θ => ofReal_Xi4_pow_le hP θ c τ) hM

/-- **The Markov step for `Ξ`** (here `P ≥ 1` is enough). -/
theorem lemmaPP_ii_XiS {P : ℕ} (hP : 1 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {j : ℝ} (hj : 0 ≤ j)
    (hmom : ∀ x : Fin n → ℝ, normSq x = 1 →
      ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P)) ∂nuA n ≤
        ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)))
    {M : ℝ} (hM : 0 < M) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < XiS θ.1 θ.2 c τ} ≤
      (j ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P :=
  markov_Xi hP hnP c hτ hj hmom (fun θ => XiS θ.1 θ.2 c τ)
    (fun θ => ofReal_XiS_pow_le hP θ c τ) hM

/-! ## §5 The corollaries with the weak constant -/

/-- **Lemma PP, weak form, for `Ξ₄`.** -/
theorem lemmaPP_Xi4_weak {P : ℕ} (hP : 2 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {M : ℝ} (hM : 0 < M) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤
      (jW n P ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P :=
  lemmaPP_ii_Xi4 hP hnP c hτ (jW_nonneg n P)
    (fun _ hx => lemmaPP_i_weak (by omega) (by omega) hx) hM

/-- **Lemma PP, weak form, for `Ξ`.** -/
theorem lemmaPP_XiS_weak {P : ℕ} (hP : 1 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {M : ℝ} (hM : 0 < M) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < XiS θ.1 θ.2 c τ} ≤
      (jW n P ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P :=
  lemmaPP_ii_XiS hP hnP c hτ (jW_nonneg n P)
    (fun _ hx => lemmaPP_i_weak (by omega) hP hx) hM

end markov

end BstLean.Part153

open BstLean.Part153 in
#print axioms opN_mul_le
open BstLean.Part153 in
#print axioms jacT_le
open BstLean.Part153 in
#print axioms opN_jacT_le
open BstLean.Part153 in
#print axioms opN_mul_moment
open BstLean.Part153 in
#print axioms lemmaPP_i_weak
open BstLean.Part153 in
#print axioms lemmaPP_i_weak_integral
open BstLean.Part153 in
#print axioms markov_Xi
open BstLean.Part153 in
#print axioms lemmaPP_ii_Xi4
open BstLean.Part153 in
#print axioms lemmaPP_ii_XiS
open BstLean.Part153 in
#print axioms lemmaPP_Xi4_weak
open BstLean.Part153 in
#print axioms lemmaPP_XiS_weak
