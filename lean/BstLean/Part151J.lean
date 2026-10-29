import BstLean.Part151Poinc2

/-!
# Part 151: Lemma J (the Jacobian formula of the feature map holds almost everywhere) and
Lemma SA (i) in the form of the document

Role: `proofs/option-n/theorem5-04-standin-structure.tex`, Lemma J (for the feature map of `F`;
the same statement holds for any two matrices), and `theorem5-09-fluctuation.tex`, Lemma SA,
first claim.

`hid2 M₁ M₂ y = ReLU(M₂·ReLU(M₁y))`. Masks with STRICT positivity: `mask t = 1` if `t > 0`,
else `0`.

* `jac M₁ M₂ y = D₂·M₂·D₁·M₁` (masks at `y`), `jacFro M₁ M₂ y = ‖jac‖²_F`.
* `jac_at`: at a point `y` where no first-layer preactivation of a nonzero row vanishes and
  where coordinate `j` of `hid2` is differentiable, the derivative is row `j` of `jac`.
* `JacAt M₁ M₂ y`: every coordinate of `hid2 M₁ M₂` is differentiable at `y` with the partial
  derivatives `jac M₁ M₂ y`.
* **`lemmaJ`**, `lemmaJ_gauss`, `lemmaJ_shift`: `JacAt` holds for Lebesgue-almost every `y`, for
  almost every `y` under the standard Gaussian distribution, and at `c + σγ` for almost every
  `γ` (`σ ≠ 0`).
* `gradSq_hid2`: `Σ_j |∇ hid2_j(y)|² = ‖jac(y)‖²_F` where `JacAt` holds.
* **`lemmaSA_i`**: `E_η|Δ_s|² ≤ (σ²/k)·E_γ ‖J_F(c + σγ)‖²_F` (Poincaré inequality for each
  feature).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam)
open BstLean.Part139 (gamK)
open BstLean.Part148 (EuLip stdGauss_ac)

/-- The strict mask: `1` if `t > 0`, else `0`. -/
noncomputable def mask (t : ℝ) : ℝ := if 0 < t then 1 else 0

lemma mask_of_pos {t : ℝ} (h : 0 < t) : mask t = 1 := by unfold mask; simp [h]

lemma mask_of_nonpos {t : ℝ} (h : t ≤ 0) : mask t = 0 := by unfold mask; simp [not_lt.mpr h]

lemma mask_sq (t : ℝ) : mask t ^ 2 = mask t := by
  unfold mask; split_ifs <;> norm_num

lemma mask_nonneg (t : ℝ) : 0 ≤ mask t := by
  unfold mask; split_ifs <;> norm_num

lemma measurable_mask : Measurable mask :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

section jac

variable {k m₁ m₂ : ℕ}

/-- **The Jacobian matrix of the feature map** `D₂·M₂·D₁·M₁`, with the strict masks at `y`. -/
noncomputable def jac (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y : Fin k → ℝ) : Matrix (Fin m₂) (Fin k) ℝ :=
  Matrix.of fun j l => mask ((M₂ *ᵥ reluV (M₁ *ᵥ y)) j) *
    ∑ i, M₂ j i * mask ((M₁ *ᵥ y) i) * M₁ i l

/-- `‖J(y)‖²_F`: the squared Frobenius norm of the Jacobian matrix. -/
noncomputable def jacFro (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y : Fin k → ℝ) : ℝ :=
  ∑ j, ∑ l, jac M₁ M₂ y j l ^ 2

lemma jacFro_nonneg (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y : Fin k → ℝ) : 0 ≤ jacFro M₁ M₂ y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Row `i` of `M₁` as a continuous linear functional. -/
noncomputable def rowL (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (i : Fin m₁) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ l, M₁ i l • (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ)

lemma rowL_apply (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (i : Fin m₁) (y : Fin k → ℝ) :
    rowL M₁ i y = (M₁ *ᵥ y) i := by
  simp [rowL, mulVec, dotProduct]

lemma rowL_single (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (i : Fin m₁) (l : Fin k) :
    rowL M₁ i (Pi.single l 1) = M₁ i l := by
  rw [rowL_apply]
  simp [mulVec, dotProduct, Pi.single_apply]

/-- The derivative of a first-layer feature, at a point where its preactivation is not `0` or
its row is `0`. -/
lemma relu_row_hasFDerivAt (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (i : Fin m₁) {y : Fin k → ℝ}
    (h : (M₁ *ᵥ y) i ≠ 0 ∨ ∀ l, M₁ i l = 0) :
    HasFDerivAt (fun z : Fin k → ℝ => relu ((M₁ *ᵥ z) i)) (mask ((M₁ *ᵥ y) i) • rowL M₁ i) y := by
  have hc : Continuous (fun z : Fin k → ℝ => rowL M₁ i z) := (rowL M₁ i).continuous
  rcases h with h | h
  · rcases lt_or_gt_of_ne h with hneg | hpos
    · -- negative: locally `0`
      rw [mask_of_nonpos hneg.le, zero_smul]
      have hev : (fun z : Fin k → ℝ => relu ((M₁ *ᵥ z) i)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have hopen : IsOpen {z : Fin k → ℝ | rowL M₁ i z < 0} := isOpen_lt hc continuous_const
        have hy : y ∈ {z : Fin k → ℝ | rowL M₁ i z < 0} := by
          show rowL M₁ i y < 0
          rw [rowL_apply]; exact hneg
        filter_upwards [hopen.mem_nhds hy] with z hz
        have hz' : rowL M₁ i z < 0 := hz
        rw [rowL_apply] at hz'
        exact relu_of_nonpos hz'.le
      exact (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev
    · rw [mask_of_pos hpos, one_smul]
      have hev : (fun z : Fin k → ℝ => relu ((M₁ *ᵥ z) i)) =ᶠ[𝓝 y] fun z => rowL M₁ i z := by
        have hopen : IsOpen {z : Fin k → ℝ | 0 < rowL M₁ i z} := isOpen_lt continuous_const hc
        have hy : y ∈ {z : Fin k → ℝ | 0 < rowL M₁ i z} := by
          show 0 < rowL M₁ i y
          rw [rowL_apply]; exact hpos
        filter_upwards [hopen.mem_nhds hy] with z hz
        have hz' : 0 < rowL M₁ i z := hz
        rw [rowL_apply] at hz' ⊢
        exact relu_of_nonneg hz'.le
      exact (rowL M₁ i).hasFDerivAt.congr_of_eventuallyEq hev
  · have h0 : ∀ z : Fin k → ℝ, (M₁ *ᵥ z) i = 0 := by
      intro z
      simp [mulVec, dotProduct, h]
    rw [h0 y, mask_of_nonpos le_rfl, zero_smul]
    have e : (fun z : Fin k → ℝ => relu ((M₁ *ᵥ z) i)) = fun _ => (0 : ℝ) := by
      funext z
      rw [h0 z]
      exact relu_of_nonpos le_rfl
    rw [e]
    exact hasFDerivAt_const (0 : ℝ) y

/-- The second-layer preactivation `j`, and its derivative. -/
lemma pre2_hasFDerivAt (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (j : Fin m₂) {y : Fin k → ℝ} (h : ∀ i, (M₁ *ᵥ y) i ≠ 0 ∨ ∀ l, M₁ i l = 0) :
    HasFDerivAt (fun z : Fin k → ℝ => (M₂ *ᵥ reluV (M₁ *ᵥ z)) j)
      (∑ i, M₂ j i • (mask ((M₁ *ᵥ y) i) • rowL M₁ i)) y := by
  have e : (fun z : Fin k → ℝ => (M₂ *ᵥ reluV (M₁ *ᵥ z)) j) =
      fun z => ∑ i, M₂ j i * relu ((M₁ *ᵥ z) i) := by
    funext z
    simp [mulVec, dotProduct, reluV]
  rw [e]
  have hs := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m₁)))
    (A := fun i (z : Fin k → ℝ) => M₂ j i * relu ((M₁ *ᵥ z) i))
    (A' := fun i => M₂ j i • (mask ((M₁ *ᵥ y) i) • rowL M₁ i)) (x := y)
    (fun i _ => (relu_row_hasFDerivAt M₁ i (h i)).const_mul (M₂ j i))
  exact hs

/-- **The Jacobian formula at a point.** If no first-layer preactivation of a nonzero row
vanishes at `y`, the partial derivatives (`fderiv`) of coordinate `j` of `hid2 M₁ M₂` at `y` are
the entries of row `j` of `jac M₁ M₂ y`. (Where the second-layer preactivation
is `0`, the feature has a minimum, so its derivative is `0`, as the strict mask says.) -/
theorem jac_at (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (j : Fin m₂) {y : Fin k → ℝ} (h : ∀ i, (M₁ *ᵥ y) i ≠ 0 ∨ ∀ l, M₁ i l = 0) (l : Fin k) :
    fderiv ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y (Pi.single l 1) = jac M₁ M₂ y j l := by
  set g : (Fin k → ℝ) → ℝ := fun z => (M₂ *ᵥ reluV (M₁ *ᵥ z)) j with hg
  have hgd := pre2_hasFDerivAt M₁ M₂ j h
  have hz : (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) = fun z => relu (g z) := by
    funext z; rfl
  have hgc : ContinuousAt g y := hgd.continuousAt
  have hval : (∑ i, M₂ j i • (mask ((M₁ *ᵥ y) i) • rowL M₁ i)) (Pi.single l 1) =
      ∑ i, M₂ j i * mask ((M₁ *ᵥ y) i) * M₁ i l := by
    simp only [FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, rowL_single]
    exact Finset.sum_congr rfl fun i _ => by ring
  show fderiv ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y (Pi.single l 1) =
    mask (g y) * ∑ i, M₂ j i * mask ((M₁ *ᵥ y) i) * M₁ i l
  rcases lt_trichotomy (g y) 0 with hneg | hzero | hpos
  · rw [mask_of_nonpos hneg.le, zero_mul, hz]
    have hev : (fun z => relu (g z)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hgc.eventually (gt_mem_nhds hneg)] with z hz'
      exact relu_of_nonpos (le_of_lt hz')
    rw [hev.fderiv_eq]
    simp
  · rw [mask_of_nonpos hzero.le, zero_mul]
    have hmin : IsLocalMin (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y := by
      refine Filter.Eventually.of_forall fun z => ?_
      show hid2 M₁ M₂ y j ≤ hid2 M₁ M₂ z j
      have e1 : hid2 M₁ M₂ y j = relu (g y) := rfl
      have e2 : hid2 M₁ M₂ z j = relu (g z) := rfl
      rw [e1, e2, hzero, relu_of_nonpos le_rfl]
      exact relu_nonneg _
    rw [hmin.fderiv_eq_zero]
    simp
  · rw [mask_of_pos hpos, one_mul, hz]
    have hev : (fun z => relu (g z)) =ᶠ[𝓝 y] g := by
      filter_upwards [hgc.eventually (lt_mem_nhds hpos)] with z hz'
      exact relu_of_nonneg (le_of_lt hz')
    rw [hev.fderiv_eq, hgd.fderiv, hval]

/-- Every coordinate of `hid2 M₁ M₂` is differentiable at `y`, with the partial derivatives
`jac M₁ M₂ y`. -/
def JacAt (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y : Fin k → ℝ) : Prop :=
  ∀ j, DifferentiableAt ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y ∧
    ∀ l, fderiv ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y (Pi.single l 1) = jac M₁ M₂ y j l

/-- A coordinate of `hid2 M₁ M₂` is Lipschitz for the Euclidean norm. -/
lemma hid2_coord_eulip (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (j : Fin m₂) : EuLip (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) (√(frob M₂ * frob M₁)) := by
  intro x y
  have h1 := hid2_lip M₁ M₂ x y
  have h2 : (hid2 M₁ M₂ x j - hid2 M₁ M₂ y j) ^ 2 ≤ normSq (hid2 M₁ M₂ x - hid2 M₁ M₂ y) := by
    unfold normSq
    exact Finset.single_le_sum (f := fun i => (hid2 M₁ M₂ x - hid2 M₁ M₂ y) i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have e : normSq (x - y) = ∑ i, (x i - y i) ^ 2 := rfl
  have h3 : (hid2 M₁ M₂ x j - hid2 M₁ M₂ y j) ^ 2 ≤
      frob M₂ * frob M₁ * ∑ i, (x i - y i) ^ 2 := by
    rw [← e, mul_assoc]; exact h2.trans h1
  have h4 := Real.abs_le_sqrt h3
  rwa [Real.sqrt_mul (mul_nonneg (frob_nonneg _) (frob_nonneg _))] at h4

/-- **Lemma J**: for Lebesgue-almost every `y`, every coordinate of the feature map
`hid2 M₁ M₂` is differentiable at `y`, and the derivative is `jac M₁ M₂ y = D₂M₂D₁M₁`. -/
theorem lemmaJ (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) :
    ∀ᵐ y ∂(volume : Measure (Fin k → ℝ)), JacAt M₁ M₂ y := by
  -- the hyperplanes of the first layer
  have hrow : ∀ᵐ y ∂(volume : Measure (Fin k → ℝ)),
      ∀ i, (M₁ *ᵥ y) i ≠ 0 ∨ ∀ l, M₁ i l = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases h0 : ∀ l, M₁ i l = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inr h0
    · have hker : LinearMap.ker (rowL M₁ i).toLinearMap ≠ ⊤ := by
        intro htop
        apply h0
        intro l
        have hm : (Pi.single l (1 : ℝ) : Fin k → ℝ) ∈ LinearMap.ker (rowL M₁ i).toLinearMap := by
          rw [htop]; exact Submodule.mem_top
        have := LinearMap.mem_ker.mp hm
        simpa [rowL_single] using this
      have hnull := Measure.addHaar_submodule (volume : Measure (Fin k → ℝ)) _ hker
      rw [ae_iff]
      refine measure_mono_null ?_ hnull
      intro y hy
      simp only [mem_ofPred_eq, not_or, not_not] at hy
      show y ∈ LinearMap.ker (rowL M₁ i).toLinearMap
      rw [LinearMap.mem_ker]
      show rowL M₁ i y = 0
      rw [rowL_apply]; exact hy.1
  -- Rademacher
  have hdiff : ∀ᵐ y ∂(volume : Measure (Fin k → ℝ)),
      ∀ j, DifferentiableAt ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y := by
    rw [ae_all_iff]
    intro j
    exact ((hid2_coord_eulip M₁ M₂ j).lipschitz (Real.sqrt_nonneg _)).ae_differentiableAt
      (μ := volume)
  filter_upwards [hrow, hdiff] with y h1 h2 j
  exact ⟨h2 j, fun l => jac_at M₁ M₂ j h1 l⟩

/-- Lemma J for the standard Gaussian distribution. -/
theorem lemmaJ_gauss (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) :
    ∀ᵐ y ∂stdGauss (Fin k), JacAt M₁ M₂ y :=
  stdGauss_ac (lemmaJ M₁ M₂)

/-- Lemma J at the points `c + σγ`, `γ` a standard Gaussian vector, `σ ≠ 0`. -/
theorem lemmaJ_shift (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (c : Fin k → ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    ∀ᵐ γ ∂stdGauss (Fin k), JacAt M₁ M₂ (c + σ • γ) := by
  have h := lemmaJ M₁ M₂
  rw [ae_iff] at h
  refine stdGauss_ac (ae_iff.mpr ?_)
  have e : {γ : Fin k → ℝ | ¬JacAt M₁ M₂ (c + σ • γ)} =
      (fun γ : Fin k → ℝ => σ • γ) ⁻¹' ((fun x : Fin k → ℝ => c + x) ⁻¹'
        {y | ¬JacAt M₁ M₂ y}) := rfl
  rw [e, Measure.addHaar_preimage_smul _ hσ, measure_preimage_add, h, mul_zero]

/-- Where the Jacobian formula holds: `Σ_j |∇ hid2_j(y)|² = ‖J(y)‖²_F`. -/
theorem gradSq_hid2 (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    {y : Fin k → ℝ} (h : JacAt M₁ M₂ y) :
    ∑ j, gradSq (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y = jacFro M₁ M₂ y := by
  unfold gradSq jacFro
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [(h j).2 l]

/-- `Σ_j |∇ hid2_j|² = ‖J‖²_F` almost everywhere (standard Gaussian distribution). -/
theorem gradSq_hid2_ae (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) :
    ∀ᵐ y ∂stdGauss (Fin k),
      ∑ j, gradSq (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y = jacFro M₁ M₂ y :=
  (lemmaJ_gauss M₁ M₂).mono fun _ h => gradSq_hid2 M₁ M₂ h

end jac

/-! ## Lemma SA (i) -/

section SA

variable {n m : ℕ}

/-- The gradient of a feature of the shifted input: `Σ_i |∇_γ z_i(c + σγ)|² = σ²·‖J(c + σγ)‖²_F`
for almost every `γ`. -/
lemma gradSq_zS_ae (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) :
    ∀ᵐ γ ∂stdGauss (Fin n), ∑ i, gradSq (fun x : Fin n → ℝ => zS θ c σ x i) γ =
      σ ^ 2 * jacFro θ.1 θ.2 (c + σ • γ) := by
  by_cases hσ : σ = 0
  · subst hσ
    refine Filter.Eventually.of_forall fun γ => ?_
    have e : ∀ i, (fun x : Fin n → ℝ => zS θ c 0 x i) = fun _ => hid2 θ.1 θ.2 (c + 0) i := by
      intro i; funext x; simp [zS]
    unfold gradSq
    simp_rw [e]
    simp
  · filter_upwards [lemmaJ_shift θ.1 θ.2 c hσ] with γ hJ
    unfold jacFro
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold gradSq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hA : HasFDerivAt (fun x : Fin n → ℝ => c + σ • x)
        (σ • ContinuousLinearMap.id ℝ (Fin n → ℝ)) γ :=
      ((ContinuousLinearMap.id ℝ (Fin n → ℝ)).hasFDerivAt.const_smul σ).const_add c
    have hf := (hJ i).1.hasFDerivAt
    have hcomp := hf.comp γ hA
    have e : (fun x : Fin n → ℝ => zS θ c σ x i) =
        (fun z : Fin n → ℝ => hid2 θ.1 θ.2 z i) ∘ fun x : Fin n → ℝ => c + σ • x := by
      funext x; rfl
    rw [e, hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    rw [(hJ i).2 l]
    ring

lemma measurable_jacFro_shift (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) :
    AEStronglyMeasurable (fun γ : Fin n → ℝ => σ ^ 2 * jacFro θ.1 θ.2 (c + σ • γ))
      (stdGauss (Fin n)) := by
  have hm : Measurable (fun γ : Fin n → ℝ => ∑ i, gradSq (fun x : Fin n → ℝ => zS θ c σ x i) γ) :=
    Finset.measurable_sum _ fun i _ => measurable_gradSq _
  exact hm.aestronglyMeasurable.congr (gradSq_zS_ae θ c σ)

/-- **Lemma SA, first claim, in the form of the document**: for fixed `(F₁, F₂)`, `c`, `σ` and
`k ≥ 1` independent standard Gaussian vectors `η_j`:
`E_η |Δ_s|² ≤ (σ²/k)·E_γ ‖J_F(c + σγ)‖²_F`. (Multiply by `t_F` for `E_η T_s² ≤ σ²·Φ_s/k`.) -/
theorem lemmaSA_i (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ η, ENNReal.ofReal (normSq (dSamp θ c σ k η)) ∂gamK k n ≤
      ENNReal.ofReal (σ ^ 2 / k *
        ∫ γ, jacFro θ.1 θ.2 (c + σ • γ) ∂stdGauss (Fin n)) := by
  obtain ⟨hI, -⟩ := lemmaSA_fixed_int θ c σ hk
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun η => normSq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the coordinates are Lipschitz
  have hL : ∀ i, EuLip (fun x : Fin n → ℝ => zS θ c σ x i)
      (√(frob θ.2 * frob θ.1) * |σ|) := by
    intro i x y
    have h := hid2_coord_eulip θ.1 θ.2 i (c + σ • x) (c + σ • y)
    have e : ∑ l, ((c + σ • x) l - (c + σ • y) l) ^ 2 = σ ^ 2 * ∑ l, (x l - y l) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hp := poincare_mean_pi (z := zS θ c σ) (L := fun _ => √(frob θ.2 * frob θ.1) * |σ|)
    (fun _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hL hk
  have e1 : ∫ η, normSq (dSamp θ c σ k η) ∂gamK k n =
      ∫ η, ∑ i, ((k : ℝ)⁻¹ * ∑ j, zS θ c σ (η j) i - ∫ y, zS θ c σ y i ∂stdGauss (Fin n)) ^ 2
        ∂(Measure.pi fun _ : Fin k => stdGauss (Fin n)) := rfl
  rw [e1]
  refine hp.trans (le_of_eq ?_)
  rw [integral_congr_ae (gradSq_zS_ae θ c σ), integral_const_mul]
  ring

end SA

end BstLean.Part151
