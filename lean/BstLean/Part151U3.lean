import BstLean.Part151U2
import BstLean.Part132Defs

/-!
# Part 151, item 4 (d): Lemma U (iii), the event `E_×`; the conditional mean of `Δ_U`

Role: `delegations/statements/p151-spec.md`, item 4 (d). Paper source:
`proofs/option-n/theorem5-09-fluctuation.tex`, Lemma U (ii) (`E_G⟨Δ_U, w⟩ = 0`) and (iii).

* **`dU_condMean`**: given `c_A = c`, the conditional mean of every coordinate of `Δ_U` over the
  residual part of `A₃` is `0` (Lemma A3 (a), (b) of the document, for the features of `F`).
* **`lemmaU_Ecross`**: the event `E_×` with its charge `exp(−2u²/(π²ℓ_U²))`.
* `TU_condMean_le`: the conditional mean of `T_U` is at most the conditional root mean square.
* **`lemmaU_events`**: outside two events of total charge `2·exp(−2u²/(π²ℓ_U²))`:
  `T_U ≤ (conditional root mean square of T_U given c_A) + u` and `X_× ≤ u`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (frob_integrable)
open BstLean.Part133 (sq_integral_le)
open BstLean.Part134 (lam res sig measurable_lam measurable_sig measurable_res normSq_ne_zero
  cDist measurable_mulVec_joint projPerp glue glue_res measurable_glue measurable_mul_right)
open BstLean.Part136 (HidParam)
open BstLean.Part149 (outTrue outStand normSq_res_le lam_sq_le)
open BstLean.Part150 (CMap)

section U3

variable {n : ℕ} (bh : CMap n) (W : MlpParam (2 * n) (mW n) n)
  (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

lemma lam_self {m : ℕ} {b : Fin m → ℝ} (hb : b ≠ 0) : lam b b = 1 := by
  have h0 := normSq_ne_zero hb
  unfold lam
  have : ∑ j, b j * b j = normSq b := Finset.sum_congr rfl fun j _ => (sq _).symm
  rw [this, div_self h0]

/-- The integrand `(M′, ξ) ↦ ψ_i(λ(ξ)c + M′ r(ξ))`. -/
noncomputable def FU (θF : HidParam n (mF n)) (i : Fin (mF n)) (c : Fin n → ℝ)
    (q : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ)) : ℝ :=
  psiF θF i (lam (bh (W, (A₁, A₂))) (hU W A₁ A₂ q.2) • c +
    q.1.mulVec (res (bh (W, (A₁, A₂))) (hU W A₁ A₂ q.2)))

lemma measurable_FU (θF : HidParam n (mF n)) (i : Fin (mF n)) (c : Fin n → ℝ) :
    Measurable (FU bh W A₁ A₂ θF i c) := by
  unfold FU
  have hh := measurable_hU W A₁ A₂
  refine (continuous_psiF θF i).measurable.comp (Measurable.add ?_ ?_)
  · exact ((measurable_lam _).comp (hh.comp measurable_snd)).smul_const c
  · exact measurable_mulVec_joint.comp
      (measurable_fst.prodMk ((measurable_res _).comp (hh.comp measurable_snd)))

lemma integrable_FU (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (i : Fin (mF n)) (c : Fin n → ℝ) :
    Integrable (FU bh W A₁ A₂ θF i c)
      ((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (stdGauss (Fin n))) := by
  set b := bh (W, (A₁, A₂)) with hbd
  set H : ℝ := frob A₂ * frob A₁ with hH
  have hH0 : 0 ≤ H := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  set C : ℝ := frob θF.2 * frob θF.1 with hC
  have hC0 : 0 ≤ C := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  have hdom : Integrable (fun q : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ) =>
      1 + C * (1 + (2 * (H / normSq b * normSq c) + 2 * (frob q.1 * H))))
      ((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (stdGauss (Fin n))) := by
    have h1 : Integrable (fun q : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ) => frob q.1)
        ((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (stdGauss (Fin n))) :=
      (frob_integrable n (mA n) (2 / (mA n : ℝ))).comp_fst _
    exact (integrable_const _).add (((integrable_const _).add
      ((integrable_const _).add ((h1.mul_const H).const_mul 2))).const_mul C)
  refine hdom.mono' (measurable_FU bh W A₁ A₂ θF i c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  set y := lam b (hU W A₁ A₂ q.2) • c + q.1.mulVec (res b (hU W A₁ A₂ q.2)) with hy
  have h1 : FU bh W A₁ A₂ θF i c q ^ 2 ≤ C * (1 + normSq y) := psiF_sq_le θF i y
  have h2 := normSq_add_le (lam b (hU W A₁ A₂ q.2) • c) (q.1.mulVec (res b (hU W A₁ A₂ q.2)))
  rw [normSq_smul] at h2
  have h3 : lam b (hU W A₁ A₂ q.2) ^ 2 ≤ H / normSq b :=
    (lam_sq_le hb _).trans (div_le_div_of_nonneg_right (hU_le W A₁ A₂ hn q.2) hb0.le)
  have h4 : normSq (q.1.mulVec (res b (hU W A₁ A₂ q.2))) ≤ frob q.1 * H :=
    (normSq_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left
      ((normSq_res_le hb _).trans (hU_le W A₁ A₂ hn q.2)) (frob_nonneg _))
  have h5 : lam b (hU W A₁ A₂ q.2) ^ 2 * normSq c ≤ H / normSq b * normSq c :=
    mul_le_mul_of_nonneg_right h3 (normSq_nonneg c)
  have h6 : normSq y ≤ 2 * (H / normSq b * normSq c) + 2 * (frob q.1 * H) := by
    rw [hy]; linarith
  have h7 : FU bh W A₁ A₂ θF i c q ^ 2 ≤
      C * (1 + (2 * (H / normSq b * normSq c) + 2 * (frob q.1 * H))) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) hC0)
  nlinarith [sq_nonneg (|FU bh W A₁ A₂ θF i c q| - 1), sq_abs (FU bh W A₁ A₂ θF i c q)]

/-- `Δ_U` at a glued matrix: the true mean minus the stand-in mean at `c`. -/
lemma dU_glue (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (i : Fin (mF n)) (c : Fin n → ℝ) (M' : Matrix (Fin n) (Fin (mA n)) ℝ) :
    dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i =
      (∫ ξ, FU bh W A₁ A₂ θF i c (M', ξ) ∂stdGauss (Fin n)) -
        outStand (stdGauss (Fin n)) (hU W A₁ A₂) (2 / (mA n : ℝ)) (bh (W, (A₁, A₂)))
          (psiF θF i) c := by
  rw [dU_coord bh W A₁ A₂ hn hb, glue_b bh W A₁ A₂ hb, lam_self hb, one_smul]
  unfold outTrue FU
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show psiF θF i ((glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))).mulVec
    (hU W A₁ A₂ ξ)) = _
  rw [glue_res]

/-- **The conditional mean of `Δ_U` given `c_A = c` is `0`** (every coordinate). -/
theorem dU_condMean (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (i : Fin (mF n)) (c : Fin n → ℝ) :
    Integrable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
        dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i)
      (gaussMat n (mA n) (2 / (mA n : ℝ))) ∧
    ∫ M', dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i
      ∂gaussMat n (mA n) (2 / (mA n : ℝ)) = 0 := by
  simp_rw [dU_glue bh W A₁ A₂ hn hb θF i c]
  have hF := integrable_FU bh W A₁ A₂ hn hb θF i c
  set b := bh (W, (A₁, A₂)) with hbd
  set v : ℝ := 2 / (mA n : ℝ) with hv
  have hI : Integrable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
      ∫ ξ, FU bh W A₁ A₂ θF i c (M', ξ) ∂stdGauss (Fin n)) (gaussMat n (mA n) v) :=
    hF.integral_prod_left
  refine ⟨hI.sub (integrable_const _), ?_⟩
  have hF' : Integrable (Function.uncurry fun (M' : Matrix (Fin n) (Fin (mA n)) ℝ)
      (ξ : Fin n → ℝ) => FU bh W A₁ A₂ θF i c (M', ξ))
      ((gaussMat n (mA n) v).prod (stdGauss (Fin n))) := hF
  rw [integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_integral_swap hF', sub_eq_zero]
  unfold outStand
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  -- one input
  set g : (Fin n → ℝ) → ℝ := fun y => psiF θF i (lam b (hU W A₁ A₂ ξ) • c + y) with hg
  have hgm : Measurable g :=
    (continuous_psiF θF i).measurable.comp (measurable_const.add measurable_id)
  have hs : Measurable (fun γ : Fin n → ℝ =>
      (√v * √(normSq (res b (hU W A₁ A₂ ξ)))) • γ) :=
    measurable_const_smul _
  calc ∫ M', FU bh W A₁ A₂ θF i c (M', ξ) ∂gaussMat n (mA n) v
      = ∫ M', g (M'.mulVec (res b (hU W A₁ A₂ ξ))) ∂gaussMat n (mA n) v := rfl
    _ = ∫ y, g y ∂(gaussMat n (mA n) v).map (fun M => M.mulVec (res b (hU W A₁ A₂ ξ))) :=
        (integral_map (measurable_mulVec_right _).aemeasurable hgm.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂(stdGauss (Fin n)).map
          (fun γ => (√v * √(normSq (res b (hU W A₁ A₂ ξ)))) • γ) := by
        rw [gaussMat_mulVec]
    _ = ∫ γ, g ((√v * √(normSq (res b (hU W A₁ A₂ ξ)))) • γ) ∂stdGauss (Fin n) :=
        integral_map hs.aemeasurable hgm.aestronglyMeasurable
    _ = _ := rfl

/-- **Lemma U (iii), the event `E_×`.** `w c` is a direction (`|w c| ≤ 1`), a measurable
function of `c_A = c`. Over the last matrix `A₃` of `A`:
`Pr(−√t_F·⟨w(A₃ b), Δ_U⟩ ≥ u) ≤ exp(−2u²/(π²ℓ_U²))`. -/
theorem lemmaU_Ecross (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | u ≤ -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
            dU bh W (A₁, A₂, A₃) θF i)} ≤
      Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * ellU n LF Mr ^ 2)) := by
  have h := lemmaU_Ecross_sub bh W A₁ A₂ hn hb θF hMr0 hLF hMr hw hw1 hu
  have hz : ∀ c : Fin n → ℝ, ∫ M', -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
      dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i)
      ∂gaussMat n (mA n) (2 / (mA n : ℝ)) = 0 := by
    intro c
    rw [integral_neg, integral_const_mul, integral_finsetSum _ fun i _ =>
      ((dU_condMean bh W A₁ A₂ hn hb θF i c).1).const_mul _]
    simp_rw [integral_const_mul, (dU_condMean bh W A₁ A₂ hn hb θF _ c).2]
    simp
  simp_rw [hz, zero_add] at h
  exact h

/-! ## The conditional root mean square, and the two events together -/

/-- The conditional mean square of `T_U` given `c_A = c`. -/
noncomputable def TUsqCond (θF : HidParam n (mF n)) (c : Fin n → ℝ) : ℝ :=
  ∫ M', TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) ^ 2
    ∂gaussMat n (mA n) (2 / (mA n : ℝ))

lemma FU_sq_le (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (i : Fin (mF n)) (c : Fin n → ℝ) (q : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ)) :
    FU bh W A₁ A₂ θF i c q ^ 2 ≤ frob θF.2 * frob θF.1 *
      (1 + (2 * (frob A₂ * frob A₁ / normSq (bh (W, (A₁, A₂))) * normSq c) +
        2 * (frob q.1 * (frob A₂ * frob A₁)))) := by
  set b := bh (W, (A₁, A₂)) with hbd
  set H : ℝ := frob A₂ * frob A₁ with hH
  have hC0 : 0 ≤ frob θF.2 * frob θF.1 := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  set y := lam b (hU W A₁ A₂ q.2) • c + q.1.mulVec (res b (hU W A₁ A₂ q.2)) with hy
  have h1 : FU bh W A₁ A₂ θF i c q ^ 2 ≤ frob θF.2 * frob θF.1 * (1 + normSq y) :=
    psiF_sq_le θF i y
  have h2 := normSq_add_le (lam b (hU W A₁ A₂ q.2) • c) (q.1.mulVec (res b (hU W A₁ A₂ q.2)))
  rw [normSq_smul] at h2
  have h3 : lam b (hU W A₁ A₂ q.2) ^ 2 ≤ H / normSq b :=
    (lam_sq_le hb _).trans (div_le_div_of_nonneg_right (hU_le W A₁ A₂ hn q.2) hb0.le)
  have h4 : normSq (q.1.mulVec (res b (hU W A₁ A₂ q.2))) ≤ frob q.1 * H :=
    (normSq_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left
      ((normSq_res_le hb _).trans (hU_le W A₁ A₂ hn q.2)) (frob_nonneg _))
  have h5 : lam b (hU W A₁ A₂ q.2) ^ 2 * normSq c ≤ H / normSq b * normSq c :=
    mul_le_mul_of_nonneg_right h3 (normSq_nonneg c)
  have h6 : normSq y ≤ 2 * (H / normSq b * normSq c) + 2 * (frob q.1 * H) := by
    rw [hy]; linarith
  exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) hC0)

lemma measurable_TU_glue (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (c : Fin n → ℝ) :
    Measurable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
      TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂)))))) :=
  (measurable_TU bh W A₁ A₂ hn hb θF).comp ((measurable_glue _).comp
    (measurable_const.prodMk (measurable_mul_right _)))

lemma TU_glue_sq_int (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (c : Fin n → ℝ) :
    Integrable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
      TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) ^ 2)
      (gaussMat n (mA n) (2 / (mA n : ℝ))) := by
  set b := bh (W, (A₁, A₂)) with hbd
  set C : ℝ := frob θF.2 * frob θF.1 with hC
  set H : ℝ := frob A₂ * frob A₁ with hH
  have hC0 : 0 ≤ C := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  have hH0 : 0 ≤ H := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  have htF : (0 : ℝ) ≤ 2 / (mF n : ℝ) := by positivity
  set s : Fin (mF n) → ℝ := fun i =>
    outStand (stdGauss (Fin n)) (hU W A₁ A₂) (2 / (mA n : ℝ)) b (psiF θF i) c with hs
  set Kf : Matrix (Fin n) (Fin (mA n)) ℝ → ℝ := fun M' =>
    C * (1 + (2 * (H / normSq b * normSq c) + 2 * (frob M' * H))) with hKf
  have hKint : Integrable Kf (gaussMat n (mA n) (2 / (mA n : ℝ))) :=
    ((integrable_const _).add ((integrable_const _).add
      (((frob_integrable n (mA n) _).mul_const H).const_mul 2))).const_mul C
  have hdom : Integrable (fun M' : Matrix (Fin n) (Fin (mA n)) ℝ =>
      2 / (mF n : ℝ) * ∑ i : Fin (mF n), (2 * Kf M' + 2 * s i ^ 2))
      (gaussMat n (mA n) (2 / (mA n : ℝ))) :=
    (integrable_finsetSum _ fun i _ => (hKint.const_mul 2).add (integrable_const _)).const_mul _
  refine hdom.mono' ((measurable_TU_glue bh W A₁ A₂ hn hb θF c).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun M' => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold TU
  rw [Real.sq_sqrt (mul_nonneg htF (normSq_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ htF
  unfold normSq
  refine Finset.sum_le_sum fun i _ => ?_
  rw [dU_glue bh W A₁ A₂ hn hb θF i c M']
  have hpt : ∀ ξ, FU bh W A₁ A₂ θF i c (M', ξ) ^ 2 ≤ Kf M' := fun ξ =>
    FU_sq_le bh W A₁ A₂ hn hb θF i c (M', ξ)
  have hm : Measurable (fun ξ : Fin n → ℝ => FU bh W A₁ A₂ θF i c (M', ξ)) :=
    (measurable_FU bh W A₁ A₂ θF i c).comp (measurable_const.prodMk measurable_id)
  have h2int : Integrable (fun ξ : Fin n → ℝ => FU bh W A₁ A₂ θF i c (M', ξ) ^ 2)
      (stdGauss (Fin n)) := by
    refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (Kf M')
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ξ
  have h1 := sq_integral_le h2int
  have h3 : ∫ ξ, FU bh W A₁ A₂ θF i c (M', ξ) ^ 2 ∂stdGauss (Fin n) ≤ Kf M' := by
    have := integral_mono h2int (integrable_const (Kf M')) hpt
    simpa using this
  have h4 : (∫ ξ, FU bh W A₁ A₂ θF i c (M', ξ) ∂stdGauss (Fin n)) ^ 2 ≤ Kf M' := h1.trans h3
  show ((∫ ξ, FU bh W A₁ A₂ θF i c (M', ξ) ∂stdGauss (Fin n)) - s i) ^ 2 ≤ _
  nlinarith [sq_nonneg ((∫ ξ, FU bh W A₁ A₂ θF i c (M', ξ) ∂stdGauss (Fin n)) + s i)]

/-- The conditional mean of `T_U` given `c_A = c` is at most the conditional root mean square. -/
theorem TU_condMean_le (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (c : Fin n → ℝ) :
    ∫ M', TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂)))))
      ∂gaussMat n (mA n) (2 / (mA n : ℝ)) ≤ √(TUsqCond bh W A₁ A₂ θF c) := by
  have h := sq_integral_le (TU_glue_sq_int bh W A₁ A₂ hn hb θF c)
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- **Lemma U (iii), the two events together.** Over the last matrix `A₃` of `A`, outside an
event of probability at most `2·exp(−2u²/(π²ℓ_U²))`:
`T_U < √(E[T_U² | c_A]) + u` and `−√t_F·⟨w_×, Δ_U⟩ < u`. -/
theorem lemmaU_events (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | ¬ (TU bh W A₁ A₂ θF A₃ <
              √(TUsqCond bh W A₁ A₂ θF (A₃.mulVec (bh (W, (A₁, A₂))))) + u ∧
            -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
              dU bh W (A₁, A₂, A₃) θF i) < u)} ≤
      2 * Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * ellU n LF Mr ^ 2)) := by
  have h1 := lemmaU_EU bh W A₁ A₂ hn hb θF hMr0 hLF hMr hu
  have h2 := lemmaU_Ecross bh W A₁ A₂ hn hb θF hMr0 hLF hMr hw hw1 hu
  set S1 : Set (Matrix (Fin n) (Fin (mA n)) ℝ) := {A₃ |
    (∫ M', TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) (A₃.mulVec (bh (W, (A₁, A₂))))
      (M' * projPerp (bh (W, (A₁, A₂))))) ∂gaussMat n (mA n) (2 / (mA n : ℝ))) + u ≤
      TU bh W A₁ A₂ θF A₃} with hS1
  set S2 : Set (Matrix (Fin n) (Fin (mA n)) ℝ) := {A₃ |
    u ≤ -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
      dU bh W (A₁, A₂, A₃) θF i)} with hS2
  have hun := measureReal_union_le (μ := gaussMat n (mA n) (2 / (mA n : ℝ))) S1 S2
  refine (measureReal_mono (s₂ := S1 ∪ S2) ?_ (measure_ne_top _ _)).trans (by linarith)
  intro A₃ hA
  simp only [mem_ofPred_eq, not_and_or, not_lt] at hA
  rcases hA with h | h
  · refine Or.inl ?_
    have := TU_condMean_le bh W A₁ A₂ hn hb θF (A₃.mulVec (bh (W, (A₁, A₂))))
    show _ + u ≤ _
    linarith
  · exact Or.inr h

end U3

end BstLean.Part151
