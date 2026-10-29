import BstLean.Part151U4
import BstLean.Part151U3
import BstLean.Part151J3

/-!
# Part 151, item 4 (d): Lemma U (i) in the form of the document, conditional on `c_A = c`

Role: `delegations/statements/p151-spec.md`, item 4 (d). Paper source:
`proofs/option-n/theorem5-09-fluctuation.tex`, Lemma U (i): `E_G T_U² ≤ ‖C_r‖_op·Φ_U`.

Notation of `Part151U3`: `b = bh (W, (A₁, A₂)) ≠ 0`, `t_A = 2/m_A`, `t_F = 2/m_F`,
`M′ ∼ gaussMat n m_A t_A` (the residual part of `A₃` given `c_A = c`). The input of `F` is
`yU c M′ ξ = λ(ξ)·c + M′·r(ξ)`.

* `PhiU θF c = E_{M′} E_ξ t_F·‖J_F(y_ξ(M′))‖²_F`: the quantity `Φ_U` of the document, given
  `c_A = c`.
* **`lemmaU_i`**: `E[T_U² | c_A = c] ≤ Mr·Φ_U(c)`, if `‖C_r‖_op ≤ Mr` (hypothesis `hMr`).
* **`lemmaU_i_events`**: outside an event of `A₃` of probability at most
  `2·exp(−2u²/(π²ℓ_U²))`: `T_U < √(Mr·Φ_U(A₃b)) + u` and `X_× < u`.
* **`lemmaU_JU`**: the event `E_{JU}` for a fixed `c`:
  `Pr_{F₁,F₂}(Φ_U(c) > 2(1 + δ)(1 + δ′)) ≤ (432/m_F²)(1 + 63/m_F)(1/δ⁴ + 1/δ′⁴)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part134 (lam res measurable_lam measurable_res normSq_ne_zero projPerp glue)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part149 (normSq_res_le lam_sq_le)
open BstLean.Part150 (CMap)

/-! ## The Jacobian matrix: measurability and a bound -/

section jacfacts

variable {k m₁ m₂ : ℕ}

lemma mask_le_one (t : ℝ) : mask t ≤ 1 := by
  unfold mask; split_ifs <;> norm_num

lemma measurable_jac_entry (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (j : Fin m₂) (l : Fin k) : Measurable (fun y : Fin k → ℝ => jac M₁ M₂ y j l) := by
  have h1 : ∀ i, Continuous (fun y : Fin k → ℝ => (M₁ *ᵥ y) i) := fun i =>
    (continuous_apply i).comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have h2 : Continuous (fun y : Fin k → ℝ => (M₂ *ᵥ reluV (M₁ *ᵥ y)) j) :=
    (continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      (continuous_reluV.comp (Continuous.matrix_mulVec continuous_const continuous_id)))
  show Measurable (fun y : Fin k → ℝ => mask ((M₂ *ᵥ reluV (M₁ *ᵥ y)) j) *
    ∑ i, M₂ j i * mask ((M₁ *ᵥ y) i) * M₁ i l)
  refine (measurable_mask.comp h2.measurable).mul (Finset.measurable_sum _ fun i _ => ?_)
  exact (measurable_const.mul (measurable_mask.comp (h1 i).measurable)).mul measurable_const

lemma jac_sq_le (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y : Fin k → ℝ) (j : Fin m₂) (l : Fin k) :
    jac M₁ M₂ y j l ^ 2 ≤ (∑ i, |M₂ j i| * |M₁ i l|) ^ 2 := by
  have hB0 : 0 ≤ ∑ i, |M₂ j i| * |M₁ i l| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 : |∑ i, M₂ j i * mask ((M₁ *ᵥ y) i) * M₁ i l| ≤ ∑ i, |M₂ j i| * |M₁ i l| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (mask_nonneg _)]
    have := mask_le_one ((M₁ *ᵥ y) i)
    have h0 := mask_nonneg ((M₁ *ᵥ y) i)
    have ha := abs_nonneg (M₂ j i)
    have hb := abs_nonneg (M₁ i l)
    calc |M₂ j i| * mask ((M₁ *ᵥ y) i) * |M₁ i l| ≤ |M₂ j i| * 1 * |M₁ i l| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this ha) hb
      _ = _ := by ring
  have h2 : |jac M₁ M₂ y j l| ≤ ∑ i, |M₂ j i| * |M₁ i l| := by
    show |mask ((M₂ *ᵥ reluV (M₁ *ᵥ y)) j) * ∑ i, M₂ j i * mask ((M₁ *ᵥ y) i) * M₁ i l| ≤ _
    rw [abs_mul, abs_of_nonneg (mask_nonneg _)]
    have := mask_le_one ((M₂ *ᵥ reluV (M₁ *ᵥ y)) j)
    have h0 := mask_nonneg ((M₂ *ᵥ reluV (M₁ *ᵥ y)) j)
    nlinarith [abs_nonneg (∑ i, M₂ j i * mask ((M₁ *ᵥ y) i) * M₁ i l)]
  rw [← sq_abs (jac M₁ M₂ y j l)]
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

/-- The set where coordinate `j` of the feature map is differentiable with the partial
derivatives `jac`. -/
def SJ (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (j : Fin m₂) :
    Set (Fin k → ℝ) :=
  {y | DifferentiableAt ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y ∧
    ∀ l, fderiv ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y (Pi.single l 1) = jac M₁ M₂ y j l}

lemma SJ_meas (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (j : Fin m₂) :
    MeasurableSet (SJ M₁ M₂ j) := by
  have h1 : MeasurableSet {y : Fin k → ℝ |
      DifferentiableAt ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y} :=
    measurableSet_of_differentiableAt ℝ _
  have h2 : MeasurableSet {y : Fin k → ℝ | ∀ l,
      fderiv ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y (Pi.single l 1) = jac M₁ M₂ y j l} := by
    have e : {y : Fin k → ℝ | ∀ l,
        fderiv ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y (Pi.single l 1) = jac M₁ M₂ y j l} =
        ⋂ l, {y | fderiv ℝ (fun z : Fin k → ℝ => hid2 M₁ M₂ z j) y (Pi.single l 1) =
          jac M₁ M₂ y j l} := by
      ext y; simp
    rw [e]
    exact MeasurableSet.iInter fun l => measurableSet_eq_fun
      (measurable_fderiv_apply_const ℝ _ _) (measurable_jac_entry M₁ M₂ j l)
  exact h1.inter h2

lemma SJ_ae (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (j : Fin m₂) :
    ∀ᵐ y ∂(volume : Measure (Fin k → ℝ)), y ∈ SJ M₁ M₂ j :=
  (lemmaJ M₁ M₂).mono fun _ h => h j

end jacfacts

/-! ## Lemma U (i) -/

section U5

variable {n : ℕ} (bh : CMap n) (W : MlpParam (2 * n) (mW n) n)
  (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

/-- The residual `r(ξ) = Π_b a₂(x(ξ))`. -/
noncomputable def rU (ξ : Fin n → ℝ) : Fin (mA n) → ℝ :=
  res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ)

/-- The input of `F` given `c_A = c`: `y_ξ(M′) = λ(ξ)·c + M′·r(ξ)`. -/
noncomputable def yU (c : Fin n → ℝ) (M' : Matrix (Fin n) (Fin (mA n)) ℝ) (ξ : Fin n → ℝ) :
    Fin n → ℝ :=
  yG (lamU bh W A₁ A₂) (rU bh W A₁ A₂) c M' ξ

/-- **`Φ_U` given `c_A = c`**: `E_{M′} E_ξ t_F·‖J_F(y_ξ(M′))‖²_F`. -/
noncomputable def PhiU (θF : HidParam n (mF n)) (c : Fin n → ℝ) : ℝ :=
  ∫ M', ∫ ξ, 2 / (mF n : ℝ) * jacFro θF.1 θF.2 (yU bh W A₁ A₂ c M' ξ) ∂stdGauss (Fin n)
    ∂gaussMat n (mA n) (2 / (mA n : ℝ))

lemma measurable_lamU : Measurable (lamU bh W A₁ A₂) :=
  (measurable_lam _).comp (measurable_hU W A₁ A₂)

lemma measurable_rU : Measurable (rU bh W A₁ A₂) :=
  (measurable_res _).comp (measurable_hU W A₁ A₂)

lemma lamU_sq_le (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (ξ : Fin n → ℝ) :
    lamU bh W A₁ A₂ ξ ^ 2 ≤ frob A₂ * frob A₁ / normSq (bh (W, (A₁, A₂))) := by
  have hb0 : 0 < normSq (bh (W, (A₁, A₂))) :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  exact (lam_sq_le hb _).trans (div_le_div_of_nonneg_right (hU_le W A₁ A₂ hn ξ) hb0.le)

lemma rU_le (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (ξ : Fin n → ℝ) :
    normSq (rU bh W A₁ A₂ ξ) ≤ frob A₂ * frob A₁ :=
  (normSq_res_le hb _).trans (hU_le W A₁ A₂ hn ξ)

/-- Row `k` of the Jacobian matrix, as a function of the input. -/
noncomputable def aJ (θF : HidParam n (mF n)) (k : Fin (mF n)) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun l => jac θF.1 θF.2 y k l

lemma measurable_aJ (θF : HidParam n (mF n)) (k : Fin (mF n)) : Measurable (aJ θF k) :=
  measurable_pi_iff.mpr fun l => measurable_jac_entry θF.1 θF.2 k l

lemma aJ_le (θF : HidParam n (mF n)) (k : Fin (mF n)) (y : Fin n → ℝ) :
    ∑ l, aJ θF k y l ^ 2 ≤ ∑ l, (∑ i, |θF.2 k i| * |θF.1 i l|) ^ 2 :=
  Finset.sum_le_sum fun l _ => jac_sq_le θF.1 θF.2 y k l

/-- `Ψ_k(M′) = E_ξ (z_F)_k(y_ξ(M′))`. -/
noncomputable def PsiU (θF : HidParam n (mF n)) (k : Fin (mF n)) (c : Fin n → ℝ)
    (M' : Matrix (Fin n) (Fin (mA n)) ℝ) : ℝ :=
  PsiG (stdGauss (Fin n)) (psiF θF k) (lamU bh W A₁ A₂) (rU bh W A₁ A₂) c M'

lemma psiF_eulip (θF : HidParam n (mF n)) (k : Fin (mF n)) :
    EuLip (psiF θF k) (√(frob θF.2 * frob θF.1)) :=
  hid2_coord_eulip θF.1 θF.2 k

/-- The variance of one feature mean: `Var_{M′} Ψ_k ≤ Mr·E_{M′} E_ξ Σ_l J_{kl}²`. -/
lemma PsiU_var (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n)) {Mr : ℝ}
    (hMr0 : 0 ≤ Mr)
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2) (k : Fin (mF n)) (c : Fin n → ℝ) :
    ∫ M', (PsiU bh W A₁ A₂ θF k c M' - ∫ M'', PsiU bh W A₁ A₂ θF k c M''
        ∂gaussMat n (mA n) (2 / (mA n : ℝ))) ^ 2 ∂gaussMat n (mA n) (2 / (mA n : ℝ)) ≤
      Mr * ∫ M', AG (stdGauss (Fin n)) (aJ θF k) (lamU bh W A₁ A₂) (rU bh W A₁ A₂) c M'
        ∂gaussMat n (mA n) (2 / (mA n : ℝ)) := by
  have hmA : (0 : ℝ) < mA n := by
    have : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hv : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  exact poincU (stdGauss (Fin n)) (Real.sqrt_nonneg _) (psiF_eulip θF k)
    (measurable_lamU bh W A₁ A₂) (measurable_rU bh W A₁ A₂)
    (lamU_sq_le bh W A₁ A₂ hn hb) (rU_le bh W A₁ A₂ hn hb) c hv hMr0 hMr
    (SJ_meas θF.1 θF.2 k) (SJ_ae θF.1 θF.2 k) (measurable_aJ θF k) (aJ_le θF k)
    (fun y hy => hy)

/-- **Lemma U (i), in the form of the document, given `c_A = c`**: if `‖C_r‖_op ≤ Mr`
(hypothesis `hMr`), then `E[T_U² | c_A = c] ≤ Mr·Φ_U(c)`, `Φ_U = E t_F‖J_F‖²_F` over the inputs
`y_ξ(M′)`. -/
theorem lemmaU_i (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n)) {Mr : ℝ}
    (hMr0 : 0 ≤ Mr)
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2) (c : Fin n → ℝ) :
    TUsqCond bh W A₁ A₂ θF c ≤ Mr * PhiU bh W A₁ A₂ θF c := by
  set γM := gaussMat n (mA n) (2 / (mA n : ℝ)) with hγM
  have htF : (0 : ℝ) ≤ 2 / (mF n : ℝ) := by positivity
  set s : Fin (mF n) → ℝ := fun k => ∫ M', PsiU bh W A₁ A₂ θF k c M' ∂γM with hs
  -- the conditional mean
  have hΨeq : ∀ (k : Fin (mF n)) (M' : Matrix (Fin n) (Fin (mA n)) ℝ),
      PsiU bh W A₁ A₂ θF k c M' = ∫ ξ, FU bh W A₁ A₂ θF k c (M', ξ) ∂stdGauss (Fin n) :=
    fun k M' => rfl
  have hdU : ∀ (k : Fin (mF n)) (M' : Matrix (Fin n) (Fin (mA n)) ℝ),
      dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF k =
        PsiU bh W A₁ A₂ θF k c M' - s k := by
    intro k M'
    obtain ⟨hint, hzero⟩ := dU_condMean bh W A₁ A₂ hn hb θF k c
    simp_rw [dU_glue bh W A₁ A₂ hn hb θF k c] at hint hzero
    rw [dU_glue bh W A₁ A₂ hn hb θF k c M', hΨeq]
    congr 1
    -- the stand-in mean is the mean of `Ψ_k`
    have hI : Integrable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
        ∫ ξ, FU bh W A₁ A₂ θF k c (M', ξ) ∂stdGauss (Fin n)) γM := by
      have := hint.add (integrable_const (BstLean.Part149.outStand (stdGauss (Fin n))
        (hU W A₁ A₂) (2 / (mA n : ℝ)) (bh (W, (A₁, A₂))) (psiF θF k) c))
      refine this.congr (Filter.Eventually.of_forall fun M' => ?_)
      simp only [Pi.add_apply, sub_add_cancel]
    rw [integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_eq_zero] at hzero
    simp only [hs, hΨeq]
    exact hzero.symm
  -- `T_U²` along the glued matrices
  have hTU : ∀ M' : Matrix (Fin n) (Fin (mA n)) ℝ,
      TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) ^ 2 =
        ∑ k, 2 / (mF n : ℝ) * (PsiU bh W A₁ A₂ θF k c M' - s k) ^ 2 := by
    intro M'
    unfold TU
    rw [Real.sq_sqrt (mul_nonneg htF (normSq_nonneg _))]
    unfold normSq
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hdU k M']
  -- integrability of the squares
  have hmA : (0 : ℝ) < mA n := by
    have : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hv : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  have hsq : ∀ k : Fin (mF n), Integrable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
      (PsiU bh W A₁ A₂ θF k c M' - s k) ^ 2) γM := by
    intro k
    have hGL := PsiG_eulip (stdGauss (Fin n)) (Real.sqrt_nonneg _) (psiF_eulip θF k)
      (measurable_lamU bh W A₁ A₂) (measurable_rU bh W A₁ A₂)
      (lamU_sq_le bh W A₁ A₂ hn hb) (rU_le bh W A₁ A₂ hn hb) c hv.le
    have hK0 : 0 ≤ √(frob θF.2 * frob θF.1) * √(2 / (mA n : ℝ) * (frob A₂ * frob A₁)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hmem := lip_memLp hK0 hGL
    have h2 := (hmem.sub (memLp_const (s k))).integrable_sq
    have hcont := hGL.continuous hK0
    have hm : Measurable (fun x : Fin n × Fin (mA n) → ℝ =>
        (PsiU bh W A₁ A₂ θF k c (Tv (2 / (mA n : ℝ)) x) - s k) ^ 2) :=
      ((hcont.measurable).sub measurable_const).pow_const 2
    -- the function of `M′` is the function of `x` at `x = flat(M′)/√v`; use the map
    rw [hγM, gaussMat_eq_Tv]
    have hΨm : AEStronglyMeasurable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
        (PsiU bh W A₁ A₂ θF k c M' - s k) ^ 2)
        ((stdGauss (Fin n × Fin (mA n))).map (Tv (2 / (mA n : ℝ)))) := by
      have hI := (dU_condMean bh W A₁ A₂ hn hb θF k c).1
      simp_rw [hdU k] at hI
      have h3 : AEStronglyMeasurable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
          PsiU bh W A₁ A₂ θF k c M' - s k) γM := hI.aestronglyMeasurable
      rw [hγM, gaussMat_eq_Tv] at h3
      exact h3.pow 2
    exact (integrable_map_measure hΨm (measurable_Tv _).aemeasurable).mpr h2
  -- the variance bound of each feature
  have hvar := fun k => PsiU_var bh W A₁ A₂ hn hb θF hMr0 hMr k c
  -- assemble
  have hAint := fun k : Fin (mF n) => integrable_AG (stdGauss (Fin n))
    (measurable_lamU bh W A₁ A₂) (measurable_rU bh W A₁ A₂) c (measurable_aJ θF k)
    (aJ_le θF k) (2 / (mA n : ℝ))
  have hLHS : TUsqCond bh W A₁ A₂ θF c =
      ∑ k, 2 / (mF n : ℝ) * ∫ M', (PsiU bh W A₁ A₂ θF k c M' - s k) ^ 2 ∂γM := by
    unfold TUsqCond
    simp_rw [hTU]
    rw [integral_finsetSum _ fun k _ => (hsq k).const_mul _]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hRHS : PhiU bh W A₁ A₂ θF c =
      ∑ k, 2 / (mF n : ℝ) * ∫ M', AG (stdGauss (Fin n)) (aJ θF k) (lamU bh W A₁ A₂)
        (rU bh W A₁ A₂) c M' ∂γM := by
    unfold PhiU
    have hin : ∀ M' : Matrix (Fin n) (Fin (mA n)) ℝ,
        ∫ ξ, 2 / (mF n : ℝ) * jacFro θF.1 θF.2 (yU bh W A₁ A₂ c M' ξ) ∂stdGauss (Fin n) =
          ∑ k, 2 / (mF n : ℝ) * AG (stdGauss (Fin n)) (aJ θF k) (lamU bh W A₁ A₂)
            (rU bh W A₁ A₂) c M' := by
      intro M'
      rw [integral_const_mul]
      unfold jacFro AG
      rw [integral_finsetSum, Finset.mul_sum]
      · rfl
      · intro k _
        have hm : Measurable (fun ξ : Fin n → ℝ =>
            ∑ l, jac θF.1 θF.2 (yU bh W A₁ A₂ c M' ξ) k l ^ 2) :=
          Finset.measurable_sum _ fun l _ => ((measurable_jac_entry θF.1 θF.2 k l).comp
            (measurable_yG_right (measurable_lamU bh W A₁ A₂) (measurable_rU bh W A₁ A₂) c
              M')).pow_const 2
        refine Integrable.of_bound hm.aestronglyMeasurable
          (∑ l, (∑ i, |θF.2 k i| * |θF.1 i l|) ^ 2) (Filter.Eventually.of_forall fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun l _ => sq_nonneg _)]
        exact aJ_le θF k _
    simp_rw [hin]
    rw [integral_finsetSum _ fun k _ => (hAint k).const_mul _]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  rw [hLHS, hRHS, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := mul_le_mul_of_nonneg_left (hvar k) htF
  calc 2 / (mF n : ℝ) * ∫ M', (PsiU bh W A₁ A₂ θF k c M' - s k) ^ 2 ∂γM
      ≤ 2 / (mF n : ℝ) * (Mr * ∫ M', AG (stdGauss (Fin n)) (aJ θF k) (lamU bh W A₁ A₂)
        (rU bh W A₁ A₂) c M' ∂γM) := h
    _ = _ := by ring

/-- **Lemma U (i) and (iii) together.** Over the last matrix `A₃` of `A`, outside an event of
probability at most `2·exp(−2u²/(π²ℓ_U²))`:
`T_U < √(Mr·Φ_U(A₃b)) + u` and `−√t_F·⟨w_×, Δ_U⟩ < u`. -/
theorem lemmaU_i_events (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | ¬ (TU bh W A₁ A₂ θF A₃ <
              √(Mr * PhiU bh W A₁ A₂ θF (A₃.mulVec (bh (W, (A₁, A₂))))) + u ∧
            -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
              dU bh W (A₁, A₂, A₃) θF i) < u)} ≤
      2 * Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * ellU n LF Mr ^ 2)) := by
  have h := lemmaU_events bh W A₁ A₂ hn hb θF hMr0 hLF hMr hw hw1 hu
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans h
  intro A₃ hA
  simp only [mem_ofPred_eq] at hA ⊢
  intro hgood
  apply hA
  refine ⟨?_, hgood.2⟩
  have h1 := Real.sqrt_le_sqrt
    (lemmaU_i bh W A₁ A₂ hn hb θF hMr0 hMr (A₃.mulVec (bh (W, (A₁, A₂)))))
  linarith [hgood.1]

/-- **The event `E_{JU}` for a fixed `c`**: over `(F₁, F₂)`,
`Pr(Φ_U(c) > 2(1 + δ)(1 + δ′)) ≤ (432/m_F²)(1 + 63/m_F)(1/δ⁴ + 1/δ′⁴)`. -/
theorem lemmaU_JU (hn : 1 ≤ n) (c : Fin n → ℝ) {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') :
    (hidGauss n (mF n)).real {θF | 2 * (1 + δ) * (1 + δ') < PhiU bh W A₁ A₂ θF c} ≤
      432 / (mF n : ℝ) ^ 2 * (1 + 63 / (mF n)) * (1 / δ ^ 4 + 1 / δ' ^ 4) := by
  have hmF : 1 ≤ mF n := mF_pos hn
  set P := (gaussMat n (mA n) (2 / (mA n : ℝ))).prod (stdGauss (Fin n)) with hP
  set Yv : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ) → Fin n → ℝ :=
    fun q => yU bh W A₁ A₂ c q.1 q.2 with hYv
  have hY : Measurable Yv :=
    measurable_yG (measurable_lamU bh W A₁ A₂) (measurable_rU bh W A₁ A₂) c
  have h := lemmaJF P hn hmF hY hδ hδ'
  have e : ∀ θF : HidParam n (mF n), PhiU bh W A₁ A₂ θF c = PhiJ P Yv θF := by
    intro θF
    unfold PhiU PhiJ
    have hm : Measurable (fun q : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ) =>
        2 / (mF n : ℝ) * jacFro θF.1 θF.2 (Yv q)) := by
      unfold jacFro
      exact measurable_const.mul (Finset.measurable_sum _ fun k _ =>
        Finset.measurable_sum _ fun l _ =>
          ((measurable_jac_entry θF.1 θF.2 k l).comp hY).pow_const 2)
    have hint : Integrable (fun q : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ) =>
        2 / (mF n : ℝ) * jacFro θF.1 θF.2 (Yv q)) P := by
      refine Integrable.of_bound hm.aestronglyMeasurable
        (2 / (mF n : ℝ) * ∑ k, ∑ l, (∑ i, |θF.2 k i| * |θF.1 i l|) ^ 2)
        (Filter.Eventually.of_forall fun q => ?_)
      have htF : (0 : ℝ) ≤ 2 / (mF n : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htF (jacFro_nonneg _ _ _))]
      refine mul_le_mul_of_nonneg_left ?_ htF
      unfold jacFro
      exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => jac_sq_le _ _ _ k l
    rw [hP, integral_prod _ hint]
  simp_rw [e]
  exact h

end U5

end BstLean.Part151
