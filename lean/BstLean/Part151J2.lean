import BstLean.Part151J
import BstLean.Part151R
import BstLean.Part135Dir

/-!
# Part 151: Lemma JF, the mean (the Frobenius norm of the Jacobian of the features)

Role: `proofs/option-n/theorem5-08-F-rows.tex`, Lemma JF, first claim:
`E t_F‖J_F(y)‖²_F = 2` for every `y ≠ 0`, the mean over `(F₁, F₂)`.

* `ae_dot_ne`: a standard Gaussian vector is almost surely not orthogonal to a nonzero vector.
* `half_lint`: for an even `N ≥ 0`: `2·E[1(w·h > 0)·N(w)] = E N(w)`, `w = c·ξ`.
* `jacFro_rows`: `‖J‖²_F = Σ_j 1[f′_j·h > 0]·|f′_j·D₁F₁|²`, `h = ReLU(F₁y)`.
* `lemmaJF_inner`: given `F₁`: `E_{F₂} t_F‖J_F(y)‖²_F = t_F·‖D₁F₁‖²_F`.
* **`lemmaJF_mean`**: `E_{F₁,F₂} t_F‖J_F(y)‖²_F = 2` for `y ≠ 0`, `n, m ≥ 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part148 (stdGauss_ac)
open BstLean.Part149 (stdGauss_normSq)

/-! ## Half-spaces -/

section half

variable {d : ℕ}

/-- A standard Gaussian vector is almost surely not orthogonal to a fixed nonzero vector. -/
lemma ae_dot_ne {h : Fin d → ℝ} (hh : h ≠ 0) : ∀ᵐ ξ ∂stdGauss (Fin d), ξ ⬝ᵥ h ≠ 0 := by
  suffices hvol : ∀ᵐ ξ ∂(volume : Measure (Fin d → ℝ)), ξ ⬝ᵥ h ≠ 0 from stdGauss_ac hvol
  set φ : (Fin d → ℝ) →L[ℝ] ℝ := ∑ l, h l • (ContinuousLinearMap.proj l : (Fin d → ℝ) →L[ℝ] ℝ)
    with hφ
  have hval : ∀ ξ : Fin d → ℝ, φ ξ = ξ ⬝ᵥ h := by
    intro ξ
    simp [hφ, dotProduct, mul_comm]
  have hker : LinearMap.ker φ.toLinearMap ≠ ⊤ := by
    intro htop
    apply hh
    funext l
    have hm : (Pi.single l (1 : ℝ) : Fin d → ℝ) ∈ LinearMap.ker φ.toLinearMap := by
      rw [htop]; exact Submodule.mem_top
    have h1 : φ (Pi.single l 1) = 0 := LinearMap.mem_ker.mp hm
    rw [hval] at h1
    simpa [dotProduct, Pi.single_apply] using h1
  have hnull := Measure.addHaar_submodule (volume : Measure (Fin d → ℝ)) _ hker
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro ξ hξ
  simp only [mem_ofPred_eq, not_not] at hξ
  show ξ ∈ LinearMap.ker φ.toLinearMap
  rw [LinearMap.mem_ker]
  show φ ξ = 0
  rw [hval]; exact hξ

lemma measurable_smul_dot (c : ℝ) (h : Fin d → ℝ) :
    Measurable (fun ξ : Fin d → ℝ => (c • ξ) ⬝ᵥ h) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- **The half-space identity.** For an even measurable `N ≥ 0`, a nonzero `h` and `c ≠ 0`:
`2·E[1((cξ)·h > 0)·N(cξ)] = E N(cξ)`, `ξ` a standard Gaussian vector. -/
theorem half_lint {h : Fin d → ℝ} (hh : h ≠ 0) {c : ℝ} (hc : c ≠ 0)
    {N : (Fin d → ℝ) → ℝ≥0∞} (hN : Measurable N) (hev : ∀ w, N (-w) = N w) :
    2 * ∫⁻ ξ, (if 0 < (c • ξ) ⬝ᵥ h then N (c • ξ) else 0) ∂stdGauss (Fin d) =
      ∫⁻ ξ, N (c • ξ) ∂stdGauss (Fin d) := by
  set fp : (Fin d → ℝ) → ℝ≥0∞ := fun ξ => if 0 < (c • ξ) ⬝ᵥ h then N (c • ξ) else 0 with hfp
  have mfp : Measurable fp :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_smul_dot c h))
      (hN.comp (measurable_const_smul c)) measurable_const
  have hneg : ∫⁻ ξ, fp (-ξ) ∂stdGauss (Fin d) = ∫⁻ ξ, fp ξ ∂stdGauss (Fin d) := by
    have h1 := lintegral_map (μ := stdGauss (Fin d)) mfp
      (measurable_neg : Measurable fun ξ : Fin d → ℝ => -ξ)
    rw [BstLean.Part135.stdGauss_neg] at h1
    exact h1.symm
  have hsum : ∀ᵐ ξ ∂stdGauss (Fin d), N (c • ξ) = fp ξ + fp (-ξ) := by
    filter_upwards [ae_dot_ne hh] with ξ hξ
    have e1 : (c • ξ) ⬝ᵥ h = c * (ξ ⬝ᵥ h) := by rw [smul_dotProduct, smul_eq_mul]
    have e2 : (c • -ξ) ⬝ᵥ h = -(c * (ξ ⬝ᵥ h)) := by
      rw [smul_neg, neg_dotProduct, e1]
    have e3 : N (c • -ξ) = N (c • ξ) := by rw [smul_neg, hev]
    have hne : c * (ξ ⬝ᵥ h) ≠ 0 := mul_ne_zero hc hξ
    simp only [hfp, e1, e2, e3]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [ite_eq_right (not_lt.mpr hlt.le), ite_eq_left (by linarith), zero_add]
    · rw [ite_eq_left hgt, ite_eq_right (by linarith), add_zero]
  rw [lintegral_congr_ae hsum, lintegral_add_left mfp, hneg, two_mul]

end half

/-! ## The second moment of a linear image -/

section second

variable {m n : ℕ}

/-- `E Σ_l (Σ_i (cξ)_i B_il)² = c²·‖B‖²_F` for a standard Gaussian vector `ξ` of `ℝ^m`. -/
lemma lin_image_second (B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (∑ l, (∑ i, (c • ξ) i * B i l) ^ 2) ∂stdGauss (Fin m) =
      ENNReal.ofReal (c ^ 2 * ∑ i, ∑ l, B i l ^ 2) := by
  have e : ∀ ξ : Fin m → ℝ, ENNReal.ofReal (∑ l, (∑ i, (c • ξ) i * B i l) ^ 2) =
      ∑ l, ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((ξ ⬝ᵥ fun i => B i l) ^ (2 * 1)) := by
    intro ξ
    rw [ENNReal.ofReal_sum_of_nonneg fun l _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    have : ∑ i, (c • ξ) i * B i l = c * (ξ ⬝ᵥ fun i => B i l) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  simp_rw [e]
  have hmeas : ∀ l : Fin n, Measurable (fun ξ : Fin m → ℝ =>
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((ξ ⬝ᵥ fun i => B i l) ^ (2 * 1))) := by
    intro l
    refine Measurable.const_mul (ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ _)) _
    simp only [dotProduct]
    fun_prop
  rw [lintegral_finsetSum _ fun l _ => hmeas l]
  have e2 : ∀ l : Fin n, ∫⁻ ξ, ENNReal.ofReal (c ^ 2) *
      ENNReal.ofReal ((ξ ⬝ᵥ fun i => B i l) ^ (2 * 1)) ∂stdGauss (Fin m) =
      ENNReal.ofReal (c ^ 2 * ∑ i, B i l ^ 2) := by
    intro l
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, dot_mom 1, gaussMom_two,
      ← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    simp [normSq]
  simp_rw [e2]
  rw [← ENNReal.ofReal_sum_of_nonneg fun l _ =>
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- `E 1[(cξ)·h > 0]·Σ_l (Σ_i (cξ)_i B_il)² = (c²/2)·‖B‖²_F`, if `h ≠ 0` or `B = 0`. -/
lemma half_second (B : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0)
    (hB : h = 0 → ∀ i l, B i l = 0) :
    ∫⁻ ξ, (if 0 < (c • ξ) ⬝ᵥ h then
        ENNReal.ofReal (∑ l, (∑ i, (c • ξ) i * B i l) ^ 2) else 0) ∂stdGauss (Fin m) =
      ENNReal.ofReal (c ^ 2 / 2 * ∑ i, ∑ l, B i l ^ 2) := by
  by_cases hh : h = 0
  · have hB0 := hB hh
    have e : ∑ i, ∑ l, B i l ^ 2 = 0 := by simp [hB0]
    rw [e, mul_zero, ENNReal.ofReal_zero]
    subst hh
    simp
  · set N : (Fin m → ℝ) → ℝ≥0∞ := fun w => ENNReal.ofReal (∑ l, (∑ i, w i * B i l) ^ 2)
      with hNd
    have hN : Measurable N := by
      refine ENNReal.measurable_ofReal.comp ?_
      fun_prop
    have hev : ∀ w, N (-w) = N w := by
      intro w
      simp only [hNd]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      have : ∑ i, (-w) i * B i l = -∑ i, w i * B i l := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp
      rw [this, neg_sq]
    have h2 := half_lint hh hc hN hev
    have h3 := lin_image_second B c
    have e4 : ENNReal.ofReal (c ^ 2 * ∑ i, ∑ l, B i l ^ 2) =
        2 * ENNReal.ofReal (c ^ 2 / 2 * ∑ i, ∑ l, B i l ^ 2) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [show (fun ξ : Fin m → ℝ => N (c • ξ)) =
      fun ξ => ENNReal.ofReal (∑ l, (∑ i, (c • ξ) i * B i l) ^ 2) from rfl, h3, e4] at h2
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2

end second

/-! ## Lemma JF, the mean -/

section JF

variable {n m : ℕ}

/-- The matrix `D₁F₁` (masks at `y`). -/
noncomputable def maskedF (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i l => mask ((F₁ *ᵥ y) i) * F₁ i l

/-- `‖J‖²_F = Σ_j 1[f′_j·h > 0]·|f′_j·(D₁F₁)|²`, `h = ReLU(F₁y)`, `f′_j` row `j` of `F₂`. -/
lemma jacFro_rows (F₁ : Matrix (Fin m) (Fin n) ℝ) (F₂ : Matrix (Fin m) (Fin m) ℝ)
    (y : Fin n → ℝ) :
    jacFro F₁ F₂ y = ∑ j, (if 0 < rowOf j F₂ ⬝ᵥ reluV (F₁ *ᵥ y) then
      ∑ l, (∑ i, rowOf j F₂ i * maskedF F₁ y i l) ^ 2 else 0) := by
  unfold jacFro
  refine Finset.sum_congr rfl fun j _ => ?_
  have e0 : (F₂ *ᵥ reluV (F₁ *ᵥ y)) j = rowOf j F₂ ⬝ᵥ reluV (F₁ *ᵥ y) := rfl
  have e1 : ∀ l, jac F₁ F₂ y j l = mask (rowOf j F₂ ⬝ᵥ reluV (F₁ *ᵥ y)) *
      ∑ i, rowOf j F₂ i * maskedF F₁ y i l := by
    intro l
    simp only [jac, Matrix.of_apply, maskedF, rowOf, e0]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  by_cases hpos : 0 < rowOf j F₂ ⬝ᵥ reluV (F₁ *ᵥ y)
  · rw [ite_eq_left hpos, mask_of_pos hpos]
    simp
  · rw [ite_eq_right hpos, mask_of_nonpos (not_lt.mp hpos)]
    simp

/-- `‖D₁F₁‖²_F = Σ_i 1[f_i·y > 0]·|f_i|²`. -/
lemma maskedF_fro (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    ∑ i, ∑ l, maskedF F₁ y i l ^ 2 =
      ∑ i, (if 0 < rowOf i F₁ ⬝ᵥ y then normSq (rowOf i F₁) else 0) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have e0 : (F₁ *ᵥ y) i = rowOf i F₁ ⬝ᵥ y := rfl
  simp only [maskedF, Matrix.of_apply, e0]
  by_cases hpos : 0 < rowOf i F₁ ⬝ᵥ y
  · rw [ite_eq_left hpos, mask_of_pos hpos]
    simp [normSq, rowOf]
  · rw [ite_eq_right hpos, mask_of_nonpos (not_lt.mp hpos)]
    simp

/-- If `ReLU(F₁y) = 0` then `D₁F₁ = 0`. -/
lemma maskedF_zero_of (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ)
    (h : reluV (F₁ *ᵥ y) = 0) : ∀ i l, maskedF F₁ y i l = 0 := by
  intro i l
  have hi : relu ((F₁ *ᵥ y) i) = 0 := congrFun h i
  have hle : (F₁ *ᵥ y) i ≤ 0 := by
    by_contra hc
    push Not at hc
    rw [relu_of_nonneg hc.le] at hi
    linarith
  simp [maskedF, mask_of_nonpos hle]

lemma measurable_rowform (B : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) :
    Measurable (fun w : Fin m → ℝ => if 0 < w ⬝ᵥ h then
      ENNReal.ofReal (∑ l, (∑ i, w i * B i l) ^ 2) else 0) := by
  refine Measurable.ite (measurableSet_lt measurable_const ?_) ?_ measurable_const
  · simp only [dotProduct]; fun_prop
  · refine ENNReal.measurable_ofReal.comp ?_
    fun_prop

/-- **Lemma JF, the step over `F₂`**: for fixed `F₁`, `m ≥ 1`:
`E_{F₂} t_F·‖J_F(y)‖²_F = t_F·‖D₁F₁‖²_F`, `t_F = 2/m`. -/
theorem lemmaJF_inner (hm : 1 ≤ m) (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    ∫⁻ F₂, ENNReal.ofReal (2 / (m : ℝ) * jacFro F₁ F₂ y) ∂gaussMat m m (2 / (m : ℝ)) =
      ENNReal.ofReal (2 / (m : ℝ) * ∑ i, ∑ l, maskedF F₁ y i l ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set B := maskedF F₁ y with hB
  set h := reluV (F₁ *ᵥ y) with hh
  set Φ : (Fin m → ℝ) → ℝ≥0∞ := fun w => if 0 < w ⬝ᵥ h then
    ENNReal.ofReal (∑ l, (∑ i, w i * B i l) ^ 2) else 0 with hΦ
  have mΦ : Measurable Φ := measurable_rowform B h
  have e : ∀ F₂ : Matrix (Fin m) (Fin m) ℝ, ENNReal.ofReal (2 / (m : ℝ) * jacFro F₁ F₂ y) =
      ∑ j, ENNReal.ofReal (2 / (m : ℝ)) * Φ (rowOf j F₂) := by
    intro F₂
    rw [jacFro_rows, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hΦ]
      by_cases hpos : 0 < rowOf j F₂ ⬝ᵥ h
      · rw [ite_eq_left hpos, ite_eq_left hpos, ENNReal.ofReal_mul hv.le]
      · rw [ite_eq_right hpos, ite_eq_right hpos]; simp
    · intro j _
      refine mul_nonneg hv.le ?_
      split_ifs
      · exact Finset.sum_nonneg fun l _ => sq_nonneg _
      · exact le_rfl
  simp_rw [e]
  rw [lintegral_finsetSum (μ := gaussMat m m (2 / (m : ℝ))) Finset.univ
    (f := fun j (F₂ : Matrix (Fin m) (Fin m) ℝ) => ENNReal.ofReal (2 / (m : ℝ)) * Φ (rowOf j F₂))
    fun j _ => (mΦ.comp (measurable_rowOf j)).const_mul _]
  have hrow : ∀ j : Fin m, ∫⁻ F₂ : Matrix (Fin m) (Fin m) ℝ,
      ENNReal.ofReal (2 / (m : ℝ)) * Φ (rowOf j F₂) ∂gaussMat m m (2 / (m : ℝ)) =
      ENNReal.ofReal (2 / (m : ℝ)) *
        ENNReal.ofReal (2 / (m : ℝ) / 2 * ∑ i, ∑ l, B i l ^ 2) := by
    intro j
    rw [lintegral_const_mul' (ENNReal.ofReal (2 / (m : ℝ)))
      (fun F₂ : Matrix (Fin m) (Fin m) ℝ => Φ (rowOf j F₂)) ENNReal.ofReal_ne_top,
      row_map j _ mΦ]
    congr 1
    have hc : √(2 / (m : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
    have h2 := half_second B h hc (fun h0 => maskedF_zero_of F₁ y h0)
    rw [Real.sq_sqrt hv.le] at h2
    exact h2
  simp_rw [hrow]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_mul hv.le, show (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) by simp,
    ← ENNReal.ofReal_mul hm0.le]
  congr 1
  field_simp

lemma measurable_jacFro_param (y : Fin n → ℝ) :
    Measurable (fun θ : HidParam n m => jacFro θ.1 θ.2 y) := by
  have hpre1 : ∀ i, Measurable (fun θ : HidParam n m => (θ.1 *ᵥ y) i) := by
    intro i
    simp only [mulVec, dotProduct]
    fun_prop
  have hpre2 : ∀ j, Measurable (fun θ : HidParam n m => (θ.2 *ᵥ reluV (θ.1 *ᵥ y)) j) := by
    intro j
    have e : (fun θ : HidParam n m => (θ.2 *ᵥ reluV (θ.1 *ᵥ y)) j) =
        fun θ => ∑ i, θ.2 j i * relu ((θ.1 *ᵥ y) i) := by
      funext θ
      simp [mulVec, dotProduct, reluV]
    rw [e]
    refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ (measurable_relu.comp (hpre1 i))
    fun_prop
  unfold jacFro jac
  simp only [Matrix.of_apply]
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
    Measurable.pow_const ((measurable_mask.comp (hpre2 j)).mul
      (Finset.measurable_sum _ fun i _ => Measurable.mul (Measurable.mul ?_
        (measurable_mask.comp (hpre1 i))) ?_)) 2
  · fun_prop
  · fun_prop

/-- **Lemma JF, the mean**: for every `y ≠ 0` and `n, m ≥ 1`, with `F₁ ∼ gaussMat m n (2/n)`,
`F₂ ∼ gaussMat m m (2/m)` independent: `E t_F·‖J_F(y)‖²_F = 2`, `t_F = 2/m`. -/
theorem lemmaJF_mean (hn : 1 ≤ n) (hm : 1 ≤ m) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ∫⁻ θ, ENNReal.ofReal (2 / (m : ℝ) * jacFro θ.1 θ.2 y) ∂hidGauss n m = ENNReal.ofReal 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hv' : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hmeas : Measurable (fun θ : HidParam n m =>
      ENNReal.ofReal (2 / (m : ℝ) * jacFro θ.1 θ.2 y)) :=
    ENNReal.measurable_ofReal.comp ((measurable_jacFro_param y).const_mul _)
  unfold hidGauss
  rw [lintegral_prod _ hmeas.aemeasurable]
  simp_rw [lemmaJF_inner hm _ y, maskedF_fro]
  -- the rows of `F₁`
  set Ψ : (Fin n → ℝ) → ℝ≥0∞ := fun w => if 0 < w ⬝ᵥ y then ENNReal.ofReal (normSq w) else 0
    with hΨ
  have mΨ : Measurable Ψ := by
    refine Measurable.ite (measurableSet_lt measurable_const ?_) ?_ measurable_const
    · simp only [dotProduct]; fun_prop
    · exact ENNReal.measurable_ofReal.comp measurable_normSq
  have e : ∀ F₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (2 / (m : ℝ) *
      ∑ i, (if 0 < rowOf i F₁ ⬝ᵥ y then normSq (rowOf i F₁) else 0)) =
      ∑ i, ENNReal.ofReal (2 / (m : ℝ)) * Ψ (rowOf i F₁) := by
    intro F₁
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hΨ]
      by_cases hpos : 0 < rowOf i F₁ ⬝ᵥ y
      · rw [ite_eq_left hpos, ite_eq_left hpos, ENNReal.ofReal_mul hv.le]
      · rw [ite_eq_right hpos, ite_eq_right hpos]; simp
    · intro i _
      refine mul_nonneg hv.le ?_
      split_ifs
      · exact normSq_nonneg _
      · exact le_rfl
  simp_rw [e]
  rw [lintegral_finsetSum (μ := gaussMat m n (2 / (n : ℝ))) Finset.univ
    (f := fun i (F₁ : Matrix (Fin m) (Fin n) ℝ) => ENNReal.ofReal (2 / (m : ℝ)) * Ψ (rowOf i F₁))
    fun i _ => (mΨ.comp (measurable_rowOf i)).const_mul _]
  have hrow : ∀ i : Fin m, ∫⁻ F₁ : Matrix (Fin m) (Fin n) ℝ,
      ENNReal.ofReal (2 / (m : ℝ)) * Ψ (rowOf i F₁) ∂gaussMat m n (2 / (n : ℝ)) =
      ENNReal.ofReal (2 / (m : ℝ)) := by
    intro i
    rw [lintegral_const_mul' (ENNReal.ofReal (2 / (m : ℝ)))
      (fun F₁ : Matrix (Fin m) (Fin n) ℝ => Ψ (rowOf i F₁)) ENNReal.ofReal_ne_top,
      row_map i _ mΨ]
    have hc : √(2 / (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hv').ne'
    set N : (Fin n → ℝ) → ℝ≥0∞ := fun w => ENNReal.ofReal (normSq w) with hNd
    have hN : Measurable N := ENNReal.measurable_ofReal.comp measurable_normSq
    have hev : ∀ w, N (-w) = N w := fun w => by
      simp only [hNd]; rw [BstLean.Part135.normSq_neg]
    have h2 := half_lint hy hc hN hev
    have h3 : ∫⁻ ξ, N (√(2 / (n : ℝ)) • ξ) ∂stdGauss (Fin n) = 2 := by
      obtain ⟨hi, hval⟩ := stdGauss_normSq n
      have e3 : ∀ ξ : Fin n → ℝ, N (√(2 / (n : ℝ)) • ξ) =
          ENNReal.ofReal (2 / (n : ℝ) * normSq ξ) := by
        intro ξ
        simp only [hNd]
        rw [normSq_smul, Real.sq_sqrt hv'.le]
      simp_rw [e3]
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _)
        (Filter.Eventually.of_forall fun ξ => mul_nonneg hv'.le (normSq_nonneg _)),
        integral_const_mul, hval]
      have : 2 / (n : ℝ) * n = 2 := by field_simp
      rw [this]; simp
    rw [h3] at h2
    have h4 : ∫⁻ ξ, Ψ (√(2 / (n : ℝ)) • ξ) ∂stdGauss (Fin n) = 1 := by
      have h5 : (2 : ℝ≥0∞) * ∫⁻ ξ, Ψ (√(2 / (n : ℝ)) • ξ) ∂stdGauss (Fin n) = 2 * 1 := by
        rw [mul_one]; exact h2
      exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h5
    rw [h4, mul_one]
  simp_rw [hrow]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) by simp, ← ENNReal.ofReal_mul hm0.le]
  congr 1
  field_simp

end JF

end BstLean.Part151
