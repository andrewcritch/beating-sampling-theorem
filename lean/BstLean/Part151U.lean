import BstLean.Part151ST
import BstLean.Part149StandIn

/-!
# Part 151, item 4 (d): Lemma U (the fluctuation term), mean forms

Role: `delegations/statements/p151-spec.md`, item 4 (d). Paper source:
`proofs/option-n/theorem5-09-fluctuation.tex`, Lemma U (i).

Fix `W`, `A₁`, `A₂` (so the centre `b = bh (W, (A₁, A₂))`, `λ(x)`, `σ(x)` are fixed) and integrate
the last matrix `A₃` of `A` (entries `N(0, t_A)`, `t_A = 2/m_A`). `Δ_U = dU bh W (A₁, A₂, A₃) θF`.
`L` is a frame constant of the unit residual directions `e(ξ) = r(x)/|r(x)|`:
`E_ξ ⟨e(ξ), w⟩² ≤ L·|w|²` for every `w`.

* `dU_coord`: coordinate `i` of `Δ_U` is `outTrue − outStand` of Part 149 for the test function
  `ψ_i = (z_F)_i`.
* **`lemmaU_fixed`**: `E_{A₃}|Δ_U|² ≤ L·E_c E_ξ E_γ |z_F(λc + σγ) − z_F(λc)|²`,
  `c ∼ N(0, t_A|b|²·I_n)`.
* **`lemmaU_mean`**: `E_{F₁,F₂} E_{A₃} t_F|Δ_U|² ≤ L·2·E_ξ σ(x)²`.
* **`lemmaU_fixedF`**: for fixed `(F₁, F₂)` with a Lipschitz constant `LF` of `z_F`:
  `E_{A₃} t_F|Δ_U|² ≤ L·t_F·LF²·n·E_ξ σ(x)²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part134 (lam res sig measurable_lam measurable_sig normSq_ne_zero cDist eDir
  measurable_mulVec_joint)
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part141 (cenA tauWA)
open BstLean.Part149 (thA tauOutOf stdGauss_normSq outTrue outStand standIn_lint
  measurable_standOut3)
open BstLean.Part150 (CMap)

/-- `Σ_i ∫⁻ f_i ≤ ∫⁻ Σ_i f_i` (no measurability). -/
lemma sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- `E_{F₁,F₂} t_F|z_F(y) − z_F(y′)|² ≤ (2/n)|y − y′|²` (Lemma TR for two points). -/
lemma feat_pt {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (y y' : Fin n → ℝ) :
    ∫⁻ θ : HidParam n m, ENNReal.ofReal (2 / (m : ℝ) * normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y'))
        ∂hidGauss n m ≤ ENNReal.ofReal (2 / (n : ℝ) * normSq (y - y')) := by
  have h := lemmaTR_mean (Measure.dirac ()) hn hm (X := fun _ : Unit => y)
    (Y := fun _ : Unit => y') measurable_const measurable_const (integrable_const _)
  have e : ∀ θ : HidParam n m, dPair (Measure.dirac ()) (fun _ : Unit => y) (fun _ : Unit => y') θ =
      hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y' := by
    intro θ; funext i
    simp [dPair]
  simp_rw [e] at h
  simpa using h

section U

variable {n : ℕ}

/-- The test function `ψ_i = (z_F)_i`. -/
noncomputable def psiF (θF : HidParam n (mF n)) (i : Fin (mF n)) (y : Fin n → ℝ) : ℝ :=
  hid2 θF.1 θF.2 y i

lemma continuous_psiF (θF : HidParam n (mF n)) (i : Fin (mF n)) : Continuous (psiF θF i) :=
  (continuous_apply i).comp ((continuous_hid2_joint (N := n) (m := mF n)).comp
    ((continuous_const (y := θF)).prodMk continuous_id))

lemma psiF_sq_le (θF : HidParam n (mF n)) (i : Fin (mF n)) (y : Fin n → ℝ) :
    psiF θF i y ^ 2 ≤ frob θF.2 * frob θF.1 * (1 + normSq y) := by
  have h1 := normSq_hid2_le θF.1 θF.2 y
  have h2 : psiF θF i y ^ 2 ≤ normSq (hid2 θF.1 θF.2 y) := by
    unfold normSq psiF
    exact Finset.single_le_sum (f := fun j => hid2 θF.1 θF.2 y j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : 0 ≤ frob θF.2 * frob θF.1 := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  nlinarith [normSq_nonneg y]

variable (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
  (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

/-- The hidden map `ξ ↦ a₂(x(ξ))`; it does not depend on `A₃`. -/
noncomputable def hU (ξ : Fin n → ℝ) : Fin (mA n) → ℝ := hid2 A₁ A₂ (xIn W ξ)

/-- `λ(x(ξ))` for the centre `b = bh (W, (A₁, A₂))`. -/
noncomputable def lamU (ξ : Fin n → ℝ) : ℝ := lam (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ)

/-- `σ(x(ξ)) = √t_A·|r(x)|`. -/
noncomputable def sigU (ξ : Fin n → ℝ) : ℝ :=
  sig (2 / (mA n : ℝ)) (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ)

lemma measurable_hU : Measurable (hU W A₁ A₂) :=
  measurable_a2v W (A₁, A₂, (0 : Matrix (Fin n) (Fin (mA n)) ℝ))

lemma measurable_sigU : Measurable (sigU bh W A₁ A₂) :=
  (measurable_sig _ _).comp (measurable_hU W A₁ A₂)

lemma hU_le (hn : 1 ≤ n) (ξ : Fin n → ℝ) : normSq (hU W A₁ A₂ ξ) ≤ frob A₂ * frob A₁ :=
  a2v_le W (A₁, A₂, (0 : Matrix (Fin n) (Fin (mA n)) ℝ)) hn ξ

lemma sigU_sq_int (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) :
    Integrable (fun ξ => sigU bh W A₁ A₂ ξ ^ 2) (stdGauss (Fin n)) := by
  refine Integrable.of_bound ((measurable_sigU bh W A₁ A₂).pow_const 2).aestronglyMeasurable
    (2 / (mA n : ℝ) * (frob A₂ * frob A₁)) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sigX_sq_le bh W (A₁, A₂, (0 : Matrix (Fin n) (Fin (mA n)) ℝ)) hn hb ξ

/-- **Coordinate `i` of `Δ_U` is the stand-in error of Part 149** for the test function
`(z_F)_i`, the input variable `ξ`, the hidden map `ξ ↦ a₂(x(ξ))` and the centre `b`. -/
theorem dU_coord (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (A₃ : Matrix (Fin n) (Fin (mA n)) ℝ)
    (θF : HidParam n (mF n)) (i : Fin (mF n)) :
    dU bh W (A₁, A₂, A₃) θF i =
      outTrue (stdGauss (Fin n)) (hU W A₁ A₂) (psiF θF i) A₃ -
        outStand (stdGauss (Fin n)) (hU W A₁ A₂) (2 / (mA n : ℝ)) (bh (W, (A₁, A₂)))
          (psiF θF i) (A₃.mulVec (bh (W, (A₁, A₂)))) := by
  have hb' : cenB bh W (A₁, A₂, A₃) ≠ 0 := hb
  have hXY := XY_int bh W (A₁, A₂, A₃) hn hb'
  have hpair := hid2_pair_integrable (P2 n) (measurable_Xm bh W (A₁, A₂, A₃))
    (measurable_Ym bh W (A₁, A₂, A₃)) hXY θF i
  have hYγ : Integrable (fun γ : Fin n → ℝ =>
      zS θF (cAv bh W (A₁, A₂, A₃)) (sigP bh W (A₁, A₂, A₃)) γ i) (stdGauss (Fin n)) :=
    (zS_coord_memLp θF _ _ i).integrable (by norm_num)
  have hY : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      hid2 θF.1 θF.2 (Ym bh W (A₁, A₂, A₃) q) i) (P2 n) := hYγ.comp_snd _
  have hX : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      hid2 θF.1 θF.2 (Xm bh W (A₁, A₂, A₃) q) i) (P2 n) := by
    refine (hpair.add hY).congr (Filter.Eventually.of_forall fun q => ?_)
    exact sub_add_cancel _ _
  have e2 : ∫ q, hid2 θF.1 θF.2 (Xm bh W (A₁, A₂, A₃) q) i ∂P2 n =
      outStand (stdGauss (Fin n)) (hU W A₁ A₂) (2 / (mA n : ℝ)) (bh (W, (A₁, A₂)))
        (psiF θF i) (A₃.mulVec (bh (W, (A₁, A₂)))) := by
    rw [integral_prod _ hX]
    rfl
  have h3 : dU bh W (A₁, A₂, A₃) θF i =
      ∫ ξ, hid2 θF.1 θF.2 (mlpEval (A₁, A₂, A₃) (xIn W ξ)) i ∂stdGauss (Fin n) -
        ∫ q, hid2 θF.1 θF.2 (Xm bh W (A₁, A₂, A₃) q) i ∂P2 n := rfl
  rw [h3, e2]
  rfl

lemma measurable_dU_coord (θF : HidParam n (mF n)) (i : Fin (mF n)) :
    Measurable (fun A₃ : Matrix (Fin n) (Fin (mA n)) ℝ =>
      outTrue (stdGauss (Fin n)) (hU W A₁ A₂) (psiF θF i) A₃ -
        outStand (stdGauss (Fin n)) (hU W A₁ A₂) (2 / (mA n : ℝ)) (bh (W, (A₁, A₂)))
          (psiF θF i) (A₃.mulVec (bh (W, (A₁, A₂))))) := by
  have hψ := (continuous_psiF θF i).measurable
  have hh := measurable_hU W A₁ A₂
  have m1 : Measurable (outTrue (stdGauss (Fin n)) (hU W A₁ A₂) (psiF θF i)) := by
    unfold outTrue
    refine StronglyMeasurable.measurable ?_
    refine StronglyMeasurable.integral_prod_right'
      (f := fun q : Matrix (Fin n) (Fin (mA n)) ℝ × (Fin n → ℝ) =>
        psiF θF i (q.1.mulVec (hU W A₁ A₂ q.2))) ?_
    exact (hψ.comp (measurable_mulVec_joint.comp
      (measurable_fst.prodMk (hh.comp measurable_snd)))).stronglyMeasurable
  have m2 : Measurable (outStand (stdGauss (Fin n)) (hU W A₁ A₂) (2 / (mA n : ℝ))
      (bh (W, (A₁, A₂))) (psiF θF i)) := by
    unfold outStand
    have h3 := hψ.comp (measurable_standOut3 (n := n) hh (2 / (mA n : ℝ)) (bh (W, (A₁, A₂))))
    have hin : StronglyMeasurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ∫ γ, psiF θF i (lam (bh (W, (A₁, A₂))) (hU W A₁ A₂ p.2) • p.1 +
          sig (2 / (mA n : ℝ)) (bh (W, (A₁, A₂))) (hU W A₁ A₂ p.2) • γ) ∂stdGauss (Fin n)) :=
      StronglyMeasurable.integral_prod_right'
        (f := fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
          psiF θF i (lam (bh (W, (A₁, A₂))) (hU W A₁ A₂ q.1.2) • q.1.1 +
            sig (2 / (mA n : ℝ)) (bh (W, (A₁, A₂))) (hU W A₁ A₂ q.1.2) • q.2))
        h3.stronglyMeasurable
    exact (StronglyMeasurable.integral_prod_right' hin).measurable
  exact m1.sub (m2.comp (measurable_mulVec_joint.comp (measurable_id.prodMk measurable_const)))

/-- **Lemma U, mean over `A₃` for fixed `(F₁, F₂)`**:
`E_{A₃}|Δ_U|² ≤ L·E_c E_ξ E_γ |z_F(λ(ξ)c + σ(ξ)γ) − z_F(λ(ξ)c)|²`, `c ∼ N(0, t_A|b|²·I_n)`. -/
theorem lemmaU_fixed (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin (mA n) → ℝ, ∫ ξ, (∑ j, eDir (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2
      ∂stdGauss (Fin n) ≤ L * ∑ j, w j ^ 2) (θF : HidParam n (mF n)) :
    ∫⁻ A₃, ENNReal.ofReal (normSq (dU bh W (A₁, A₂, A₃) θF))
        ∂gaussMat n (mA n) (2 / (mA n : ℝ)) ≤
      ENNReal.ofReal L * ∫⁻ c, ∫⁻ ξ, ∫⁻ γ, ENNReal.ofReal (normSq
        (hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c + sigU bh W A₁ A₂ ξ • γ) -
          hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c))) ∂stdGauss (Fin n) ∂stdGauss (Fin n)
        ∂cDist n (2 / (mA n : ℝ)) (bh (W, (A₁, A₂))) := by
  set b := bh (W, (A₁, A₂)) with hbd
  set v : ℝ := 2 / (mA n : ℝ) with hv
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hC0 : 0 ≤ frob θF.2 * frob θF.1 := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  -- each coordinate
  have hi : ∀ i : Fin (mF n),
      ∫⁻ A₃, ENNReal.ofReal ((dU bh W (A₁, A₂, A₃) θF i) ^ 2) ∂gaussMat n (mA n) v ≤
      ENNReal.ofReal L * ∫⁻ c, ∫⁻ ξ, ∫⁻ γ, ENNReal.ofReal
        ((psiF θF i (lam b (hU W A₁ A₂ ξ) • c + sig v b (hU W A₁ A₂ ξ) • γ) -
          psiF θF i (lam b (hU W A₁ A₂ ξ) • c)) ^ 2) ∂stdGauss (Fin n) ∂stdGauss (Fin n)
        ∂cDist n v b := by
    intro i
    have h := standIn_lint (stdGauss (Fin n)) hv0 hb (measurable_hU W A₁ A₂)
      (hU_le W A₁ A₂ hn) (continuous_psiF θF i).measurable (psiF_sq_le θF i) hL0 hL
    simp_rw [dU_coord bh W A₁ A₂ hn hb]
    exact h
  have e0 : ∀ A₃ : Matrix (Fin n) (Fin (mA n)) ℝ,
      ENNReal.ofReal (normSq (dU bh W (A₁, A₂, A₃) θF)) =
        ∑ i, ENNReal.ofReal ((dU bh W (A₁, A₂, A₃) θF i) ^ 2) := by
    intro A₃
    unfold normSq
    exact ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _
  simp_rw [e0]
  rw [lintegral_finsetSum]
  swap
  · intro i _
    simp_rw [dU_coord bh W A₁ A₂ hn hb]
    exact ENNReal.measurable_ofReal.comp ((measurable_dU_coord bh W A₁ A₂ θF i).pow_const 2)
  refine (Finset.sum_le_sum fun i _ => hi i).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  refine (sum_lintegral_le _ _ _).trans (lintegral_mono fun c => ?_)
  refine (sum_lintegral_le _ _ _).trans (lintegral_mono fun ξ => ?_)
  refine (sum_lintegral_le _ _ _).trans (lintegral_mono fun γ => ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  exact le_of_eq rfl

/-- `∫ |γ|² dγ = n` as a lower integral with a factor. -/
lemma lint_normSq_gauss (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ γ : Fin n → ℝ, ENNReal.ofReal (a * normSq γ) ∂stdGauss (Fin n) =
      ENNReal.ofReal (a * n) := by
  obtain ⟨hi, he⟩ := stdGauss_normSq n
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul a)
    (Filter.Eventually.of_forall fun γ => mul_nonneg ha (normSq_nonneg _)),
    integral_const_mul, he]

lemma add_sub_smul (c γ : Fin n → ℝ) (lmb σ : ℝ) :
    normSq ((lmb • c + σ • γ) - lmb • c) = σ ^ 2 * normSq γ := by
  rw [add_sub_cancel_left, normSq_smul]

/-- **Lemma U, mean form over `A₃` and `(F₁, F₂)`**: `E t_F|Δ_U|² ≤ L·2·E_ξ σ(x)²`. -/
theorem lemmaU_mean (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin (mA n) → ℝ, ∫ ξ, (∑ j, eDir (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2
      ∂stdGauss (Fin n) ≤ L * ∑ j, w j ^ 2) :
    ∫⁻ θF : HidParam n (mF n), ∫⁻ A₃, ENNReal.ofReal
        (2 / (mF n : ℝ) * normSq (dU bh W (A₁, A₂, A₃) θF))
        ∂gaussMat n (mA n) (2 / (mA n : ℝ)) ∂hidGauss n (mF n) ≤
      ENNReal.ofReal (L * (2 * ∫ ξ, sigU bh W A₁ A₂ ξ ^ 2 ∂stdGauss (Fin n))) := by
  have hmF := mF_pos (n := n) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : (0 : ℝ) ≤ 2 / (mF n : ℝ) := by positivity
  set b := bh (W, (A₁, A₂)) with hbd
  set ν := (cDist n (2 / (mA n : ℝ)) b).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))
    with hν
  -- the integrand, jointly measurable
  set g : HidParam n (mF n) × ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (2 / (mF n : ℝ) * normSq
      (hid2 p.1.1 p.1.2 (lamU bh W A₁ A₂ p.2.2.1 • p.2.1 + sigU bh W A₁ A₂ p.2.2.1 • p.2.2.2) -
        hid2 p.1.1 p.1.2 (lamU bh W A₁ A₂ p.2.2.1 • p.2.1))) with hg
  have mlam : Measurable (lamU bh W A₁ A₂) := (measurable_lam _).comp (measurable_hU W A₁ A₂)
  have msig := measurable_sigU bh W A₁ A₂
  have mg : Measurable g := by
    have my0 : Measurable (fun p : HidParam n (mF n) × ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) =>
        lamU bh W A₁ A₂ p.2.2.1 • p.2.1) :=
      (mlam.comp (by fun_prop)).smul (by fun_prop)
    have my1 : Measurable (fun p : HidParam n (mF n) × ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) =>
        lamU bh W A₁ A₂ p.2.2.1 • p.2.1 + sigU bh W A₁ A₂ p.2.2.1 • p.2.2.2) :=
      my0.add ((msig.comp (by fun_prop)).smul (by fun_prop))
    have hj := (continuous_hid2_joint (N := n) (m := mF n)).measurable
    have h1 := hj.comp (measurable_fst.prodMk my1)
    have h0 := hj.comp (measurable_fst.prodMk my0)
    exact ENNReal.measurable_ofReal.comp
      ((continuous_normSq.measurable.comp (h1.sub h0)).const_mul _)
  -- step 1: `lemmaU_fixed` for each `θF`
  have s1 : ∀ θF : HidParam n (mF n), ∫⁻ A₃, ENNReal.ofReal
      (2 / (mF n : ℝ) * normSq (dU bh W (A₁, A₂, A₃) θF)) ∂gaussMat n (mA n) (2 / (mA n : ℝ)) ≤
      ENNReal.ofReal L * ∫⁻ p, g (θF, p) ∂ν := by
    intro θF
    have h := lemmaU_fixed bh W A₁ A₂ hn hb hL0 hL θF
    have e1 : ∀ A₃ : Matrix (Fin n) (Fin (mA n)) ℝ,
        ENNReal.ofReal (2 / (mF n : ℝ) * normSq (dU bh W (A₁, A₂, A₃) θF)) =
          ENNReal.ofReal (2 / (mF n : ℝ)) * ENNReal.ofReal (normSq (dU bh W (A₁, A₂, A₃) θF)) :=
      fun A₃ => ENNReal.ofReal_mul ht0
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl h).trans ?_
    rw [← mul_assoc, mul_comm (ENNReal.ofReal (2 / (mF n : ℝ))), mul_assoc]
    refine mul_le_mul' le_rfl ?_
    have mgθ : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => g (θF, p)) :=
      mg.comp (measurable_const.prodMk measurable_id)
    rw [hν, lintegral_prod _ mgθ.aemeasurable]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun c => ?_
    have mgc : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g (θF, (c, q))) :=
      mg.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [lintegral_prod _ mgc.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun γ => ?_
    simp only [hg]
    rw [ENNReal.ofReal_mul ht0]
  refine (lintegral_mono s1).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap (f := fun θF p => g (θF, p)) mg.aemeasurable]
  -- step 2: the mean over `(F₁, F₂)` inside
  have s2 : ∀ p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ),
      ∫⁻ θF, g (θF, p) ∂hidGauss n (mF n) ≤
        ENNReal.ofReal (2 / (n : ℝ) * (sigU bh W A₁ A₂ p.2.1 ^ 2 * normSq p.2.2)) := by
    intro p
    have h := feat_pt hn hmF (lamU bh W A₁ A₂ p.2.1 • p.1 + sigU bh W A₁ A₂ p.2.1 • p.2.2)
      (lamU bh W A₁ A₂ p.2.1 • p.1)
    rw [add_sub_smul] at h
    exact h
  refine (mul_le_mul' le_rfl (lintegral_mono s2)).trans ?_
  have mq : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal (2 / (n : ℝ) * (sigU bh W A₁ A₂ p.2.1 ^ 2 * normSq p.2.2))) :=
    ENNReal.measurable_ofReal.comp
      ((((msig.comp (by fun_prop)).pow_const 2).mul
        (continuous_normSq.measurable.comp (by fun_prop))).const_mul _)
  rw [hν, lintegral_prod _ mq.aemeasurable]
  have inner : ∀ c : Fin n → ℝ, ∫⁻ q : (Fin n → ℝ) × (Fin n → ℝ),
      ENNReal.ofReal (2 / (n : ℝ) * (sigU bh W A₁ A₂ q.1 ^ 2 * normSq q.2))
        ∂(stdGauss (Fin n)).prod (stdGauss (Fin n)) =
      ENNReal.ofReal (2 * ∫ ξ, sigU bh W A₁ A₂ ξ ^ 2 ∂stdGauss (Fin n)) := by
    intro c
    have mqc : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        ENNReal.ofReal (2 / (n : ℝ) * (sigU bh W A₁ A₂ q.1 ^ 2 * normSq q.2))) :=
      ENNReal.measurable_ofReal.comp
        ((((msig.comp measurable_fst).pow_const 2).mul
          (continuous_normSq.measurable.comp measurable_snd)).const_mul _)
    rw [lintegral_prod _ mqc.aemeasurable]
    have e : ∀ ξ : Fin n → ℝ, ∫⁻ γ : Fin n → ℝ,
        ENNReal.ofReal (2 / (n : ℝ) * (sigU bh W A₁ A₂ ξ ^ 2 * normSq γ)) ∂stdGauss (Fin n) =
        ENNReal.ofReal (2 * sigU bh W A₁ A₂ ξ ^ 2) := by
      intro ξ
      have h := lint_normSq_gauss (n := n) (2 / (n : ℝ) * sigU bh W A₁ A₂ ξ ^ 2) (by positivity)
      have e1 : ∀ γ : Fin n → ℝ, 2 / (n : ℝ) * (sigU bh W A₁ A₂ ξ ^ 2 * normSq γ) =
          2 / (n : ℝ) * sigU bh W A₁ A₂ ξ ^ 2 * normSq γ := fun γ => by ring
      simp_rw [e1]
      rw [h]
      congr 1
      field_simp
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal ((sigU_sq_int bh W A₁ A₂ hn hb).const_mul 2)
      (Filter.Eventually.of_forall fun ξ => by positivity), integral_const_mul]
  have hI := lintegral_congr (μ := cDist n (2 / (mA n : ℝ)) b) inner
  refine le_of_eq ?_
  refine Eq.trans (congrArg (fun z => ENNReal.ofReal L * z) hI) ?_
  rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_mul hL0]

/-- **Lemma U, mean over `A₃` for fixed `(F₁, F₂)` with a Lipschitz constant `LF` of `z_F`**:
`E_{A₃} t_F|Δ_U|² ≤ L·t_F·LF²·n·E_ξ σ(x)²`. -/
theorem lemmaU_fixedF (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin (mA n) → ℝ, ∫ ξ, (∑ j, eDir (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2
      ∂stdGauss (Fin n) ≤ L * ∑ j, w j ^ 2) (θF : HidParam n (mF n)) {LF : ℝ}
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y')) :
    ∫⁻ A₃, ENNReal.ofReal (2 / (mF n : ℝ) * normSq (dU bh W (A₁, A₂, A₃) θF))
        ∂gaussMat n (mA n) (2 / (mA n : ℝ)) ≤
      ENNReal.ofReal (L * (2 / (mF n : ℝ)) * LF ^ 2 * n *
        ∫ ξ, sigU bh W A₁ A₂ ξ ^ 2 ∂stdGauss (Fin n)) := by
  have ht0 : (0 : ℝ) ≤ 2 / (mF n : ℝ) := by positivity
  have h := lemmaU_fixed bh W A₁ A₂ hn hb hL0 hL θF
  have e1 : ∀ A₃ : Matrix (Fin n) (Fin (mA n)) ℝ,
      ENNReal.ofReal (2 / (mF n : ℝ) * normSq (dU bh W (A₁, A₂, A₃) θF)) =
        ENNReal.ofReal (2 / (mF n : ℝ)) * ENNReal.ofReal (normSq (dU bh W (A₁, A₂, A₃) θF)) :=
    fun A₃ => ENNReal.ofReal_mul ht0
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h).trans ?_
  have inner : ∀ (c ξ : Fin n → ℝ), ∫⁻ γ, ENNReal.ofReal (normSq
      (hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c + sigU bh W A₁ A₂ ξ • γ) -
        hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c))) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (LF ^ 2 * n * sigU bh W A₁ A₂ ξ ^ 2) := by
    intro c ξ
    have h1 : ∀ γ : Fin n → ℝ, ENNReal.ofReal (normSq
        (hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c + sigU bh W A₁ A₂ ξ • γ) -
          hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c))) ≤
        ENNReal.ofReal (LF ^ 2 * sigU bh W A₁ A₂ ξ ^ 2 * normSq γ) := by
      intro γ
      refine ENNReal.ofReal_le_ofReal ?_
      have := hLF (lamU bh W A₁ A₂ ξ • c + sigU bh W A₁ A₂ ξ • γ) (lamU bh W A₁ A₂ ξ • c)
      rw [add_sub_smul] at this
      linarith
    refine (lintegral_mono h1).trans (le_of_eq ?_)
    rw [lint_normSq_gauss _ (by positivity)]
    congr 1; ring
  have outer : ∀ c : Fin n → ℝ, ∫⁻ ξ, ∫⁻ γ, ENNReal.ofReal (normSq
      (hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c + sigU bh W A₁ A₂ ξ • γ) -
        hid2 θF.1 θF.2 (lamU bh W A₁ A₂ ξ • c))) ∂stdGauss (Fin n) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (LF ^ 2 * n * ∫ ξ, sigU bh W A₁ A₂ ξ ^ 2 ∂stdGauss (Fin n)) := by
    intro c
    refine (lintegral_mono (inner c)).trans (le_of_eq ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((sigU_sq_int bh W A₁ A₂ hn hb).const_mul (LF ^ 2 * n))
      (Filter.Eventually.of_forall fun ξ => by positivity), integral_const_mul]
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono outer))).trans (le_of_eq ?_)
  rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_mul hL0,
    ← ENNReal.ofReal_mul ht0]
  congr 1; ring

end U

end BstLean.Part151
