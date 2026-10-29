import BstLean.Part153PPs

/-!
# Part 153, Lemma PP (i) with the sharp constant: step (B) and the result

Paper source: `proofs/option-n/theorem5-05-covariance.tex`, Lemma PP (i).

* §1 `nrm_transpose_mulVec_moment`, **`stepB`**: the integral over `A₁`.
* §2 the constants `n1S`, `b2S`, `epsS`, `n2S`, `rcS`, `rchiS`, **`jS`** and their identities.
* §3 **`lemmaPP_i_sharp`**: `E opN(𝒥(x)Π_x)^{2P} ≤ (√n·jS n P η)^{2P}`.
* §4 `lemmaPP_Xi4_sharp`, `lemmaPP_XiS_sharp`: the Markov step with `jS`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal MatrixOrder
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac mask measurable_mask mask_nonneg)

/-! ## §1 Step (B): the integral over `A₁` -/

section stepB

variable {n m : ℕ}

lemma projT_transpose (x : Fin n → ℝ) : (projT x)ᵀ = projT x := by
  unfold projT
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_vecMulVec]

lemma mask_mul_relu (t : ℝ) : mask t * relu t = relu t := by
  by_cases ht : 0 < t
  · rw [BstLean.Part151.mask_of_pos ht, one_mul]
  · rw [relu_of_nonpos (not_lt.mp ht), mul_zero]

lemma diag_mask_mulVec_hatV (h : Fin m → ℝ) :
    Matrix.diagonal (fun i => mask (h i)) *ᵥ hatV (reluV h) = hatV (reluV h) := by
  funext i
  rw [Matrix.mulVec_diagonal]
  simp only [hatV, Pi.smul_apply, smul_eq_mul, reluV]
  rw [mul_left_comm, mask_mul_relu]

/-- `Tᵀâ = (A₁Π_x)ᵀâ` for `T = tanB A₁ x`, `â = hatV (ReLU(A₁x))`. -/
lemma tanB_transpose_mulVec (A₁ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    (tanB A₁ x)ᵀ *ᵥ hatV (reluV (A₁ *ᵥ x)) = (A₁ * projT x)ᵀ *ᵥ hatV (reluV (A₁ *ᵥ x)) := by
  unfold tanB
  rw [Matrix.mul_assoc, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, Matrix.diagonal_transpose,
    diag_mask_mulVec_hatV]

/-- The `2P`-th moment of `|Mᵀa|` for a Gaussian `m × n` matrix `M` and `|a| ≤ 1`. -/
theorem nrm_transpose_mulVec_moment (a : Fin m → ℝ) (ha : normSq a ≤ 1) (v : ℝ)
    {P : ℕ} (hP : 1 ≤ P) :
    ∫⁻ M : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (nrm (Mᵀ *ᵥ a)) ^ (2 * P) ∂gaussMat m n v ≤
      ENNReal.ofReal ((√v * (√(n : ℝ) + gaussMomConst P)) ^ (2 * P)) := by
  have hmn : Measurable (nrm : (Fin n → ℝ) → ℝ) := BstLean.Part130.measurable_normSq.sqrt
  have hφ : Measurable fun y : Fin n → ℝ => ENNReal.ofReal (nrm y) ^ (2 * P) :=
    hmn.ennreal_ofReal.pow_const _
  have hmv : Measurable fun M : Matrix (Fin m) (Fin n) ℝ => Mᵀ *ᵥ a :=
    (Continuous.matrix_mulVec (continuous_id.matrix_transpose) continuous_const).measurable
  have h1 : ∫⁻ M : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (nrm (Mᵀ *ᵥ a)) ^ (2 * P)
      ∂gaussMat m n v = ∫⁻ ζ : Fin n → ℝ, ENNReal.ofReal (nrm ((√v * √(normSq a)) • ζ)) ^ (2 * P)
        ∂stdGauss (Fin n) := by
    rw [← lintegral_map hφ hmv, gaussMat_transpose_mulVec,
      lintegral_map hφ (measurable_const_smul _)]
  rw [h1]
  have hsa : √(normSq a) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ha
  have h2 : ∀ ζ : Fin n → ℝ, ENNReal.ofReal (nrm ((√v * √(normSq a)) • ζ)) ^ (2 * P) ≤
      (ENNReal.ofReal (√v) * ENNReal.ofReal (nrm ζ)) ^ (2 * P) := by
    intro ζ
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _
    rw [nrm_smul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    refine mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _)
    calc √v * √(normSq a) ≤ √v * 1 := mul_le_mul_of_nonneg_left hsa (Real.sqrt_nonneg _)
      _ = √v := mul_one _
  refine (lintegral_mono h2).trans ?_
  have h3 : ∫⁻ ζ : Fin n → ℝ, ENNReal.ofReal (nrm ζ) ^ (2 * P) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal ((√(n : ℝ) + gaussMomConst P) ^ (2 * P)) := by
    have h := nrm_moment_lintegral n hP
    have e6 : ∀ ζ : Fin n → ℝ, ENNReal.ofReal (nrm ζ) ^ (2 * P) =
        ENNReal.ofReal (nrm ζ ^ (2 * P)) := fun ζ => (ENNReal.ofReal_pow (nrm_nonneg _) _).symm
    simpa only [e6] using h
  exact lintegral_pow_const_mul_le (Real.sqrt_nonneg _) h3

lemma measurable_hatV_reluV (m : ℕ) :
    Measurable fun h : Fin m → ℝ => hatV (reluV h) := by
  unfold hatV
  exact (measurable_nrm_reluV m).inv.smul measurable_reluV

/-- **Step (B).** For a unit vector `x`, a Gaussian `m × n` matrix `A₁` with variance `v > 0`,
`T = tanB A₁ x`, `â = hatV (ReLU(A₁x))`, and constants `r, c₂ ≥ 0`:
`‖r·|Tᵀâ| + c₂·opN(T)‖_{L^{2P}} ≤ r·√v(√n + 𝔪_P) + c₂·splitC`. -/
theorem stepB {x : Fin n → ℝ} (hx : normSq x = 1) {v : ℝ} (hv : 0 < v) {r c₂ : ℝ} (hr : 0 ≤ r)
    (hc₂ : 0 ≤ c₂) {P : ℕ} (hP : 1 ≤ P) {η : ℝ} (hη : 0 ≤ η) :
    ∫⁻ A₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal
        ((r * nrm ((tanB A₁ x)ᵀ *ᵥ hatV (reluV (A₁ *ᵥ x))) + c₂ * opN (tanB A₁ x)) ^ (2 * P))
        ∂gaussMat m n v ≤
      ENNReal.ofReal ((r * (√v * (√(n : ℝ) + gaussMomConst P)) +
        c₂ * splitC v m (√(n : ℝ) + gaussMomConst P) η (2 * P)) ^ (2 * P)) := by
  have hN : 1 ≤ 2 * P := by omega
  have hsv : 0 < √v := Real.sqrt_pos.2 hv
  have h𝔪 := gaussMomConst_nonneg P
  have h𝔫 : 0 ≤ √(n : ℝ) + gaussMomConst P := add_nonneg (Real.sqrt_nonneg _) h𝔪
  have hχ : 0 ≤ √v * (√(n : ℝ) + gaussMomConst P) := mul_nonneg hsv.le h𝔫
  have hB : ∀ K : ℝ, 0 ≤ √v * (√K + (√(n : ℝ) + gaussMomConst P)) := fun K =>
    mul_nonneg hsv.le (add_nonneg (Real.sqrt_nonneg _) h𝔫)
  have hB' : ∀ K : ℝ, 0 ≤ √v * (√K + √(n : ℝ) + gaussMomConst P) := fun K =>
    mul_nonneg hsv.le (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h𝔪)
  let Φ : (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞ := fun h B =>
    ENNReal.ofReal ((r * nrm (Bᵀ *ᵥ hatV (reluV h)) +
      c₂ * opN (Matrix.diagonal (fun j => mask (h j)) * B)) ^ (2 * P))
  have hΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        q.2ᵀ *ᵥ hatV (reluV q.1) := by
      refine measurable_pi_iff.mpr fun l => ?_
      have hh := (measurable_hatV_reluV m).comp
        (measurable_fst : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => q.1)
      show Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        ∑ j, q.2 j l * hatV (reluV q.1) j
      refine Finset.measurable_sum _ fun j _ => ?_
      have hf : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => q.2 j l :=
        (measurable_pi_apply l).comp ((measurable_pi_apply j).comp measurable_snd)
      have hg : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
          hatV (reluV q.1) j := (measurable_pi_apply j).comp hh
      exact hf.mul hg
    have h2 : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        Matrix.diagonal (fun j => mask (q.1 j)) * q.2 := by
      refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
      have e : (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
          (Matrix.diagonal (fun j => mask (q.1 j)) * q.2) j l) =
          fun q => mask (q.1 j) * q.2 j l := by
        funext q
        rw [Matrix.diagonal_mul]
      show Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
          (Matrix.diagonal (fun j => mask (q.1 j)) * q.2) j l)
      rw [e]
      exact (measurable_mask.comp ((measurable_pi_apply j).comp measurable_fst)).mul
        ((measurable_pi_apply l).comp ((measurable_pi_apply j).comp measurable_snd))
    have h3 : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        nrm (q.2ᵀ *ᵥ hatV (reluV q.1)) :=
      (BstLean.Part130.measurable_normSq.comp h1).sqrt
    have h4 := opN_continuous.measurable.comp h2
    exact ((((h3.const_mul r).add (h4.const_mul c₂))).pow_const _).ennreal_ofReal
  have step1 : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal
      ((r * nrm ((tanB A₁ x)ᵀ *ᵥ hatV (reluV (A₁ *ᵥ x))) + c₂ * opN (tanB A₁ x)) ^ (2 * P)) =
      Φ (A₁ *ᵥ x) (A₁ * projT x) := by
    intro A₁
    simp only [Φ]
    rw [tanB_transpose_mulVec]
    unfold tanB
    rw [Matrix.mul_assoc]
  simp only [step1]
  rw [gaussMat_decomp' hx hv.le hΦ]
  -- the integral over `M`, for a fixed `g`
  have inner : ∀ g : Fin m → ℝ, ∫⁻ M : Matrix (Fin m) (Fin n) ℝ, Φ (√v • g) (M * projT x)
      ∂gaussMat m n v ≤ ENNReal.ofReal ((r * (√v * (√(n : ℝ) + gaussMomConst P)) +
        c₂ * (√v * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P)))) ^ (2 * P)) := by
    intro g
    have hm : (fun j => mask ((√v • g) j)) = fun j => mask (g j) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul, mask_mul_pos hsv]
    obtain ⟨â, hâ⟩ : ∃ â, â = hatV (reluV (√v • g)) := ⟨_, rfl⟩
    have hâ1 : normSq â ≤ 1 := hâ ▸ normSq_hatV_le _
    have e : ∀ M : Matrix (Fin m) (Fin n) ℝ, Φ (√v • g) (M * projT x) ≤
        (ENNReal.ofReal r * ENNReal.ofReal (nrm (Mᵀ *ᵥ â)) +
          ENNReal.ofReal c₂ * ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) *
            (M * projT x)))) ^ (2 * P) := by
      intro M
      simp only [Φ]
      rw [hm, ← hâ, ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul hc₂,
        ← ENNReal.ofReal_add (mul_nonneg hr (nrm_nonneg _)) (mul_nonneg hc₂ (opN_nonneg _)),
        ← ENNReal.ofReal_pow (add_nonneg (mul_nonneg hr (nrm_nonneg _))
          (mul_nonneg hc₂ (opN_nonneg _)))]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (add_nonneg (mul_nonneg hr (nrm_nonneg _))
          (mul_nonneg hc₂ (opN_nonneg _))) ?_ _)
      have h5 : nrm ((M * projT x)ᵀ *ᵥ â) ≤ nrm (Mᵀ *ᵥ â) := by
        rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, projT_transpose]
        exact nrm_projT_le hx _
      exact add_le_add (mul_le_mul_of_nonneg_left h5 hr) le_rfl
    refine (lintegral_mono e).trans ?_
    have hX : Measurable fun M : Matrix (Fin m) (Fin n) ℝ =>
        ENNReal.ofReal r * ENNReal.ofReal (nrm (Mᵀ *ᵥ â)) :=
      measurable_const.mul ((BstLean.Part130.measurable_normSq.comp
        (Continuous.matrix_mulVec (continuous_id.matrix_transpose)
          continuous_const).measurable).sqrt.ennreal_ofReal)
    have hY : Measurable fun M : Matrix (Fin m) (Fin n) ℝ => ENNReal.ofReal c₂ *
        ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) * (M * projT x))) :=
      measurable_const.mul ((opN_continuous.comp (continuous_const.matrix_mul
        (continuous_id.matrix_mul continuous_const))).measurable.ennreal_ofReal)
    refine lintegral_pow_add_le hX.aemeasurable hY.aemeasurable (mul_nonneg hr hχ)
      (mul_nonneg hc₂ (hB _)) hN
      (lintegral_pow_const_mul_le hr (nrm_transpose_mulVec_moment â hâ1 v hP))
      (lintegral_pow_const_mul_le hc₂ ?_)
    have hR := opN_rowsel_moment (p := m) (fun j => mask (g j))
      (fun j => by unfold mask; split_ifs <;> simp) (projT x) hv.le hP
    have e3 : ∀ M : Matrix (Fin m) (Fin n) ℝ,
        ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) * (M * projT x))) ^ (2 * P) =
        ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) * (M * projT x)) ^ (2 * P)) :=
      fun M => (ENNReal.ofReal_pow (opN_nonneg _) _).symm
    simp only [e3]
    refine hR.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (mul_nonneg (opN_nonneg _) (hB' _)) ?_ _))
    have e4 : √(∑ i, mask (g i)) + √(n : ℝ) + gaussMomConst P =
        √(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P) := by ring
    rw [e4]
    calc opN (projT x) * (√v * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P)))
        ≤ 1 * (√v * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P))) :=
          mul_le_mul_of_nonneg_right (opN_projT_le hx) (hB _)
      _ = _ := one_mul _
  refine (lintegral_mono inner).trans ?_
  -- the integral over `g`
  have e5 : ∀ g : Fin m → ℝ, ENNReal.ofReal ((r * (√v * (√(n : ℝ) + gaussMomConst P)) +
        c₂ * (√v * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P)))) ^ (2 * P)) =
      (ENNReal.ofReal (r * (√v * (√(n : ℝ) + gaussMomConst P))) +
        ENNReal.ofReal c₂ * ENNReal.ofReal
          (√v * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P)))) ^ (2 * P) := by
    intro g
    rw [← ENNReal.ofReal_mul hc₂, ← ENNReal.ofReal_add (mul_nonneg hr hχ)
        (mul_nonneg hc₂ (hB _)),
      ENNReal.ofReal_pow (add_nonneg (mul_nonneg hr hχ) (mul_nonneg hc₂ (hB _)))]
  simp only [e5]
  have hY : Measurable fun g : Fin m → ℝ => ENNReal.ofReal c₂ * ENNReal.ofReal
      (√v * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P))) :=
    measurable_const.mul
      ((((measurable_cnt m).sqrt.add_const _).const_mul _).ennreal_ofReal)
  have m2 := cnt_moment (p := m) v (c := √(n : ℝ) + gaussMomConst P) h𝔫 hη hN
  refine lintegral_pow_add_le aemeasurable_const hY.aemeasurable (mul_nonneg hr hχ)
    (mul_nonneg hc₂ (splitC_nonneg _ _ h𝔫 _ _)) hN ?_ (lintegral_pow_const_mul_le hc₂ m2)
  rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_pow (mul_nonneg hr hχ)]

end stepB

/-! ## §2 The constants -/

/-- `n₁ = √(1+2η) + √2/√n + √2·𝔪_P/n`. -/
noncomputable def n1S (n P : ℕ) (η : ℝ) : ℝ :=
  √(1 + 2 * η) + √2 / √(n : ℝ) + √2 * gaussMomConst P / n

/-- `b₂ = √2·(1 + 1/√n + 𝔪_P/n)`. -/
noncomputable def b2S (n P : ℕ) : ℝ := √2 * (1 + 1 / √(n : ℝ) + gaussMomConst P / n)

/-- `ε² = exp(−η²n²/P)`. -/
noncomputable def epsS (n P : ℕ) (η : ℝ) : ℝ := Real.exp (-(η ^ 2 * (n : ℝ) ^ 2 / P))

/-- `n₂ = n₁ + ε²·b₂`. -/
noncomputable def n2S (n P : ℕ) (η : ℝ) : ℝ := n1S n P η + epsS n P η * b2S n P

/-- `r_c = 1 + √2·𝔪_P/n`. -/
noncomputable def rcS (n P : ℕ) : ℝ := 1 + √2 * gaussMomConst P / n

/-- `r_χ = √2·(1 + 𝔪_P/√n)`. -/
noncomputable def rchiS (n P : ℕ) : ℝ := √2 * (1 + gaussMomConst P / √(n : ℝ))

/-- **The sharp constant** `jS = n₂² + r_c·r_χ/√n` (it takes the place of `j_{n,p}`). -/
noncomputable def jS (n P : ℕ) (η : ℝ) : ℝ := n2S n P η ^ 2 + rcS n P * rchiS n P / √(n : ℝ)

lemma n2S_nonneg (n P : ℕ) {η : ℝ} (hη : 0 ≤ η) : 0 ≤ n2S n P η := by
  have := gaussMomConst_nonneg P
  unfold n2S n1S epsS b2S
  positivity

lemma rcS_nonneg (n P : ℕ) : 0 ≤ rcS n P := by
  have := gaussMomConst_nonneg P
  unfold rcS
  positivity

lemma rchiS_nonneg (n P : ℕ) : 0 ≤ rchiS n P := by
  have := gaussMomConst_nonneg P
  unfold rchiS
  positivity

lemma jS_nonneg (n P : ℕ) (η : ℝ) : 0 ≤ jS n P η := by
  have h1 := rcS_nonneg n P
  have h2 := rchiS_nonneg n P
  unfold jS
  positivity

section consts

variable {n : ℕ}

lemma sqrt_two_div_mA (_hn : 1 ≤ n) : √(2 / ((mA n : ℕ) : ℝ)) = √2 / (n : ℝ) := by
  rw [Real.sqrt_div (by norm_num), sqrt_mA]

lemma rc_eq (hn : 1 ≤ n) (g : ℝ) :
    √(2 / ((mA n : ℕ) : ℝ)) * (√(((mA n : ℕ) : ℝ) / 2) + g) = 1 + √2 * g / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : √(2 : ℝ) * √(2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [sqrt_two_div_mA hn, Real.sqrt_div (Nat.cast_nonneg _), sqrt_mA]
  have : √2 / (n : ℝ) * ((n : ℝ) / √2 + g) = (√2 / √2) * ((n : ℝ) / n) + √2 * g / n := by ring
  rw [this, div_self h2p.ne', div_self hn0.ne', one_mul]

lemma rchi_eq (hn : 1 ≤ n) (g : ℝ) :
    √(2 / (n : ℝ)) * (√(n : ℝ) + g) = √2 * (1 + g / √(n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  rw [Real.sqrt_div (by norm_num)]
  field_simp

lemma eps_eq {P : ℕ} (hP : 1 ≤ P) (η : ℝ) :
    Real.exp (-2 * η ^ 2 * ((mA n : ℕ) : ℝ)) ^ ((1 : ℝ) / ((2 * P : ℕ) : ℝ)) = epsS n P η := by
  have hP0 : (P : ℝ) ≠ 0 := by
    have : 0 < P := hP
    exact_mod_cast this.ne'
  unfold epsS
  rw [← Real.exp_mul]
  congr 1
  unfold mA
  push_cast
  field_simp

lemma sqrt_half_eta (_hn : 1 ≤ n) {η : ℝ} (hη : 0 ≤ η) :
    √2 * √((1 / 2 + η) * ((mA n : ℕ) : ℝ)) = √(1 + 2 * η) * n := by
  rw [Real.sqrt_mul (by positivity), sqrt_mA, ← mul_assoc, ← Real.sqrt_mul (by norm_num)]
  congr 2
  ring

lemma n2_eq (hn : 1 ≤ n) {P : ℕ} (hP : 1 ≤ P) {η : ℝ} (hη : 0 ≤ η) :
    splitC (2 / ((mA n : ℕ) : ℝ)) (mA n) (√(n : ℝ) + gaussMomConst P) η (2 * P) = n2S n P η := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  unfold splitC n2S n1S b2S
  rw [eps_eq hP, sqrt_two_div_mA hn, sqrt_mA]
  have e1 : √2 / (n : ℝ) * (√((1 / 2 + η) * ((mA n : ℕ) : ℝ)) + (√(n : ℝ) + gaussMomConst P)) =
      √(1 + 2 * η) + √2 / √(n : ℝ) + √2 * gaussMomConst P / n := by
    have : √2 / (n : ℝ) * (√((1 / 2 + η) * ((mA n : ℕ) : ℝ)) + (√(n : ℝ) + gaussMomConst P)) =
        (√2 * √((1 / 2 + η) * ((mA n : ℕ) : ℝ))) / n + √2 * √(n : ℝ) / n +
          √2 * gaussMomConst P / n := by ring
    rw [this, sqrt_half_eta hn hη]
    congr 2
    · field_simp
    · rw [div_eq_div_iff hn0.ne' hs.ne']
      linear_combination √2 * hss
  have e2 : √2 / (n : ℝ) * ((n : ℝ) + (√(n : ℝ) + gaussMomConst P)) =
      √2 * (1 + 1 / √(n : ℝ) + gaussMomConst P / n) := by
    have : √2 / (n : ℝ) * ((n : ℝ) + (√(n : ℝ) + gaussMomConst P)) =
        √2 * ((n : ℝ) / n + √(n : ℝ) / n + gaussMomConst P / n) := by ring
    rw [this]
    congr 3
    · field_simp
    · rw [div_eq_div_iff hn0.ne' hs.ne']
      linear_combination hss
  rw [e1, e2]

lemma n2_eq' (hn : 1 ≤ n) {P : ℕ} (hP : 1 ≤ P) {η : ℝ} (hη : 0 ≤ η) :
    splitC (2 / (n : ℝ)) (mA n) (√(n : ℝ) + gaussMomConst P) η (2 * P) =
      √(n : ℝ) * n2S n P η := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have e0 : √(2 / (n : ℝ)) = √(n : ℝ) * √(2 / ((mA n : ℕ) : ℝ)) := by
    rw [sqrt_two_div_mA hn, Real.sqrt_div (by norm_num), mul_div_assoc',
      div_eq_div_iff hs.ne' hn0.ne']
    linear_combination -√2 * hss
  rw [← n2_eq hn hP hη]
  unfold splitC
  rw [e0]
  ring

end consts

/-! ## §3 Lemma PP (i), sharp form -/

/-- **Lemma PP (i), sharp form**: for a unit vector `x`, `n ≥ 1`, `P ≥ 1`, `η ≥ 0`:
`E opN(𝒥(x)Π_x)^{2P} ≤ (√n·jS n P η)^{2P}`. -/
theorem lemmaPP_i_sharp {n : ℕ} (hn : 1 ≤ n) {P : ℕ} (hP : 1 ≤ P) {η : ℝ} (hη : 0 ≤ η)
    {x : Fin n → ℝ} (hx : normSq x = 1) :
    ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P)) ∂nuA n ≤
      ENNReal.ofReal ((√(n : ℝ) * jS n P η) ^ (2 * P)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hmeas : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P))) :=
    ((measurable_opN_jacT x).pow_const _).ennreal_ofReal
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hmA0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    unfold mA
    positivity
  have ht : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by positivity
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hA := fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
    stepA_hat (p := mA n) A₁ x ht hP hη
  simp only [rc_eq hn, n2_eq hn hP hη] at hA
  refine (lintegral_mono hA).trans ?_
  have hBb := stepB (m := mA n) hx hv1 (rcS_nonneg n P) (n2S_nonneg n P hη) hP hη
  unfold rcS at hBb
  refine hBb.trans (le_of_eq ?_)
  rw [rchi_eq hn, n2_eq' hn hP hη]
  congr 2
  have key : ∀ R N s : ℝ, 0 < s → R + N * (s * N) = s * (N ^ 2 + R / s) := by
    intro R N s hs
    have h : s * (R / s) = R := by field_simp
    linear_combination -h
  unfold jS rcS rchiS
  exact key _ _ _ hs

/-! ## §4 The Markov step with the sharp constant -/

/-- **Lemma PP for `Ξ₄` with the sharp constant.** -/
theorem lemmaPP_Xi4_sharp {n : ℕ} {P : ℕ} (hP : 2 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) {M : ℝ} (hM : 0 < M) {η : ℝ} (hη : 0 ≤ η) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤
      (jS n P η ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P :=
  lemmaPP_ii_Xi4 hP hnP c hτ (jS_nonneg n P η)
    (fun _ hx => lemmaPP_i_sharp (by omega) (by omega) hη hx) hM

/-- **Lemma PP for `Ξ` with the sharp constant.** -/
theorem lemmaPP_XiS_sharp {n : ℕ} {P : ℕ} (hP : 1 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) {M : ℝ} (hM : 0 < M) {η : ℝ} (hη : 0 ≤ η) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < XiS θ.1 θ.2 c τ} ≤
      (jS n P η ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P :=
  lemmaPP_ii_XiS hP hnP c hτ (jS_nonneg n P η)
    (fun _ hx => lemmaPP_i_sharp (by omega) hP hη hx) hM

end BstLean.Part153

open BstLean.Part153 in
#print axioms stepB
open BstLean.Part153 in
#print axioms lemmaPP_i_sharp
open BstLean.Part153 in
#print axioms lemmaPP_Xi4_sharp
open BstLean.Part153 in
#print axioms lemmaPP_XiS_sharp
