import BstLean.Part132Upper
import BstLean.Part132World

/-!
# Part 132, item 3: the upper bound of `b₁₁`

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §3 ("Upper bound of
b₁₁"), `onW2c-cx.md` (19). The paper uses the fixed-`F` identity (the uniform direction of
`A(x)`); the proof here does not: for a fixed output `y` of `A`, the output `y′ = A′(x′)` of the
independent network `A′` has `E⟨y, y′⟩ = 0` and `E⟨y, y′⟩² = (2/n)|y|²|x′|²`, and `κ∘κ` is below its
two chords from `0`.

* `KGood.chord`, `psi_chord`: `Ψ_G(y, y′) ≤ G(0)|y||y′| + β₁⟨y, y′⟩ + β₂|⟨y, y′⟩|`.
* `mlp_form_mean`, `mlp_form_sq`: the first two moments of a linear form of the output.
* `kern_cross_upper`: for unit `x, x′`:
  `E_{A,A′,F} kern F A A′ x x′ ≤ (4/n)·(q + β₂/√n + (√6 + 2√5·κ(0))/√m_F)`.
* **`b11_upper`**: the same bound for `b11`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131

/-! ## The chords of a convex kernel function -/

lemma neg_one_mem : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
lemma one_mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl _⟩

lemma KGood.chord {G : ℝ → ℝ} (hG : KGood G) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    G t ≤ G 0 + (1 - G (-1)) / 2 * t + (1 - 2 * G 0 + G (-1)) / 2 * |t| := by
  rcases le_total 0 t with h | h
  · have := hG.conv.2 KGood.zero_mem one_mem (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) h (by ring)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, hG.one] at this
    rw [abs_of_nonneg h]
    linarith
  · have := hG.conv.2 KGood.zero_mem neg_one_mem (by linarith [ht.1] : (0 : ℝ) ≤ 1 + t)
      (by linarith : (0 : ℝ) ≤ -t) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at this
    rw [show -t * -1 = t by ring] at this
    rw [abs_of_nonpos h]
    linarith

lemma KGood.chord_coef_nonneg {G : ℝ → ℝ} (hG : KGood G) : 0 ≤ (1 - 2 * G 0 + G (-1)) / 2 := by
  have := hG.conv.2 neg_one_mem one_mem (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, hG.one] at this
  rw [show (1 : ℝ) / 2 * -1 + 1 / 2 * 1 = 0 by norm_num] at this
  linarith

lemma psi_chord {ι : Type*} [Fintype ι] {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) :
    psi G y y' ≤ G 0 * (nrm y * nrm y') + (1 - G (-1)) / 2 * dotp y y' +
      (1 - 2 * G 0 + G (-1)) / 2 * |dotp y y'| := by
  have h := hG.chord (cosv_mem y y')
  have hp := nrm_mul_nonneg y y'
  have h2 := mul_le_mul_of_nonneg_left h hp
  have e1 := dotp_eq_cosv_mul y y'
  have e2 : |dotp y y'| = |cosv y y'| * (nrm y * nrm y') := by
    rw [e1, abs_mul, abs_of_nonneg hp]
  unfold psi
  rw [e2, e1]
  nlinarith

/-! ## Fubini helpers -/

lemma prod_step_assoc {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] {f : α × β × γ → ℝ} (hf : Measurable f)
    (h0 : ∀ p, 0 ≤ f p) (g : α × β → ℝ)
    (h1 : ∀ a b, Integrable (fun c => f (a, (b, c))) τ ∧ ∫ c, f (a, (b, c)) ∂τ = g (a, b))
    (hg : Integrable g (μ.prod ν)) :
    Integrable f (μ.prod (ν.prod τ)) ∧ ∫ ω, f ω ∂(μ.prod (ν.prod τ)) = ∫ z, g z ∂(μ.prod ν) := by
  have step := prod_step (μ := μ.prod ν) (ν := τ)
    (f := fun z => f (MeasurableEquiv.prodAssoc z))
    (hf.comp (MeasurableEquiv.measurable _)) (fun p => h0 _) g (fun z => h1 z.1 z.2) hg
  have hi : Integrable f (μ.prod (ν.prod τ)) := by
    rw [← Measure.prodAssoc_prod]
    exact (integrable_map_equiv _ f).mpr step.1
  refine ⟨hi, ?_⟩
  rw [← step.2, ← Measure.prodAssoc_prod, integral_map_equiv]

lemma integral_le_of_sections {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] {f : α × β × γ → ℝ}
    (hf : Integrable f (μ.prod (ν.prod τ))) {c : ℝ} (h : ∀ a b, ∫ z, f (a, (b, z)) ∂τ ≤ c) :
    ∫ ω, f ω ∂(μ.prod (ν.prod τ)) ≤ c := by
  rw [integral_prod _ hf]
  have hae : ∀ᵐ a ∂μ, ∫ y, f (a, y) ∂(ν.prod τ) ≤ c := by
    filter_upwards [hf.prod_right_ae] with a ha
    rw [integral_prod _ ha]
    have := integral_mono ha.integral_prod_left (integrable_const c) (h a)
    simpa using this
  have := integral_mono_ae hf.integral_prod_left (integrable_const c) hae
  simpa using this

/-! ## A linear form of the output of a random network -/

variable {k m q : ℕ}

/-- `E ⟨y, M h⟩² = v·|h|²·|y|²` for a Gaussian matrix `M`. -/
theorem lin_form_sq {v : ℝ} (hv : 0 ≤ v) (y : Fin q → ℝ) (h : Fin m → ℝ) :
    Integrable (fun M : Matrix (Fin q) (Fin m) ℝ => dotp y (M.mulVec h) ^ 2) (gaussMat q m v) ∧
    ∫ M : Matrix (Fin q) (Fin m) ℝ, dotp y (M.mulVec h) ^ 2 ∂gaussMat q m v =
      v * normSq h * normSq y := by
  classical
  have hij : ∀ i j : Fin q, Integrable (fun M : Matrix (Fin q) (Fin m) ℝ =>
      (y i * y j) * ((M.mulVec h) i * (M.mulVec h) j)) (gaussMat q m v) := by
    intro i j
    refine Integrable.const_mul ?_ _
    refine Integrable.mono' (layer_lin_sq hv h).1
      (((measurable_pi_apply i).comp (measurable_mulVec_right h)).mul
        ((measurable_pi_apply j).comp (measurable_mulVec_right h))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun M => ?_)
    have h1 : (M.mulVec h) i ^ 2 ≤ normSq (M.mulVec h) :=
      Finset.single_le_sum (f := fun i => (M.mulVec h) i ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h2 : (M.mulVec h) j ^ 2 ≤ normSq (M.mulVec h) :=
      Finset.single_le_sum (f := fun i => (M.mulVec h) i ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ j)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg ((M.mulVec h) i - (M.mulVec h) j),
      sq_nonneg ((M.mulVec h) i + (M.mulVec h) j)]
  have e : (fun M : Matrix (Fin q) (Fin m) ℝ => dotp y (M.mulVec h) ^ 2) =
      fun M => ∑ i, ∑ j, (y i * y j) * ((M.mulVec h) i * (M.mulVec h) j) := by
    funext M
    unfold dotp
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j]
  have inner : ∀ i : Fin q, ∫ M : Matrix (Fin q) (Fin m) ℝ,
      ∑ j, (y i * y j) * ((M.mulVec h) i * (M.mulVec h) j) ∂gaussMat q m v =
      ∑ j, (y i * y j) * (if i = j then v * ∑ l, h l * h l else 0) := by
    intro i
    rw [integral_finsetSum _ fun j _ => hij i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, gaussMat_cov hv h h]
  simp_rw [inner]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have e1 : ∑ l, h l * h l = normSq h := by
    unfold normSq; exact Finset.sum_congr rfl fun l _ => (sq _).symm
  have e2 : ∑ i, y i * y i = normSq y := by
    unfold normSq; exact Finset.sum_congr rfl fun l _ => (sq _).symm
  rw [e1, ← Finset.sum_mul, e2]; ring

lemma measurable_form (y : Fin q → ℝ) (z : Fin k → ℝ) :
    Measurable (fun θ : MlpParam k m q => dotp y (mlpEval θ z)) :=
  measurable_dotp_comp measurable_const (continuous_mlpEval_param z).measurable

/-- **The second moment of a linear form of the output**: `E ⟨y, N(z)⟩² = (2/k)·|z|²·|y|²`. -/
theorem mlp_form_sq (hm : 1 ≤ m) (y : Fin q → ℝ) (z : Fin k → ℝ) :
    Integrable (fun θ : MlpParam k m q => dotp y (mlpEval θ z) ^ 2) (mlpGauss k m q) ∧
    ∫ θ : MlpParam k m q, dotp y (mlpEval θ z) ^ 2 ∂mlpGauss k m q =
      2 / (k : ℝ) * normSq z * normSq y := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hi, he⟩ := hid2_sq (m₁ := m) (m₂ := m) (two_div_nonneg k) (two_div_nonneg m) z
  have step := prod_step_assoc (gaussMat m k (2 / (k : ℝ))) (gaussMat m m (2 / (m : ℝ)))
    (gaussMat q m (2 / (m : ℝ))) (f := fun θ : MlpParam k m q => dotp y (mlpEval θ z) ^ 2)
    ((measurable_form y z).pow_const 2) (fun p => sq_nonneg _)
    (fun p => 2 / (m : ℝ) * normSq (hid2 p.1 p.2 z) * normSq y)
    (fun M₁ M₂ => lin_form_sq (two_div_nonneg m) y (hid2 M₁ M₂ z))
    ((hi.const_mul _).mul_const _)
  refine ⟨step.1, ?_⟩
  have e : ∫ p : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
      2 / (m : ℝ) * normSq (hid2 p.1 p.2 z) * normSq y
      ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) =
      2 / (m : ℝ) * (∫ p : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ,
      normSq (hid2 p.1 p.2 z) ∂((gaussMat m k (2 / (k : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))) *
        normSq y := by
    rw [integral_mul_const, integral_const_mul]
  have h2 := step.2
  unfold mlpGauss
  rw [h2, e, he]
  field_simp

lemma mlpEval_neg_last (θ : MlpParam k m q) (z : Fin k → ℝ) :
    mlpEval ((θ.1, θ.2.1, -θ.2.2) : MlpParam k m q) z = -mlpEval θ z := by
  simp only [mlpEval, mlp2, Matrix.neg_mulVec]

lemma dotp_neg_right {ι : Type*} [Fintype ι] (y w : ι → ℝ) : dotp y (-w) = -dotp y w := by
  simp [dotp]

/-- **The mean of a linear form of the output is zero.** -/
theorem mlp_form_mean (hm : 1 ≤ m) (y : Fin q → ℝ) (z : Fin k → ℝ) :
    Integrable (fun θ : MlpParam k m q => dotp y (mlpEval θ z)) (mlpGauss k m q) ∧
    ∫ θ : MlpParam k m q, dotp y (mlpEval θ z) ∂mlpGauss k m q = 0 := by
  obtain ⟨i2, -⟩ := mlp_form_sq (q := q) hm y z
  have hint : Integrable (fun θ : MlpParam k m q => dotp y (mlpEval θ z)) (mlpGauss k m q) := by
    refine Integrable.mono' (((integrable_const (1 : ℝ)).add i2).div_const 2)
      (measurable_form y z).aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor <;> nlinarith [sq_nonneg (dotp y (mlpEval θ z) - 1),
      sq_nonneg (dotp y (mlpEval θ z) + 1)]
  refine ⟨hint, ?_⟩
  have hmeas : Measurable (fun θ : MlpParam k m q => ((θ.1, θ.2.1, -θ.2.2) : MlpParam k m q)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd).neg)
  have h1 : ∫ θ : MlpParam k m q, dotp y (mlpEval θ z) ∂mlpGauss k m q =
      ∫ θ : MlpParam k m q, dotp y (mlpEval ((θ.1, θ.2.1, -θ.2.2) : MlpParam k m q) z)
        ∂mlpGauss k m q := by
    conv_lhs => rw [← mlpGauss_neg_last (k := k) (m := m) (q := q)]
    rw [integral_map hmeas.aemeasurable]
    rw [mlpGauss_neg_last]
    exact hint.aestronglyMeasurable
  simp_rw [mlpEval_neg_last, dotp_neg_right] at h1
  rw [integral_neg] at h1
  linarith

/-- `E |N(z)| ≤ √(2q/k)·|z|`. -/
theorem mlp_nrm_single (hm : 1 ≤ m) (z : Fin k → ℝ) :
    Integrable (fun θ : MlpParam k m q => nrm (mlpEval θ z)) (mlpGauss k m q) ∧
    ∫ θ : MlpParam k m q, nrm (mlpEval θ z) ∂mlpGauss k m q ≤ √(2 * (q : ℝ) / k) * nrm z := by
  have hs : (0 : ℝ) ≤ 2 * (q : ℝ) / k := by positivity
  have hmeas : Measurable (fun θ : MlpParam k m q => normSq (mlpEval θ z)) :=
    (continuous_normSq.comp (continuous_mlpEval_param z)).measurable
  have key := sqrt_pair_le (μ := mlpGauss k m q) (X := fun θ => normSq (mlpEval θ z))
    (Y := fun _ => (1 : ℝ)) hmeas measurable_const (fun θ => normSq_nonneg _)
    (fun _ => zero_le_one) (mlp_normSq_integrable z) (integrable_const 1)
    (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg z)) zero_le_one
    (by rw [mlp_second_moment hm, mul_pow, Real.sq_sqrt hs, nrm_sq]) (by simp)
  simp only [Real.sqrt_one, mul_one] at key
  exact key

/-! ## The cross kernel -/

variable {N mW n mA mF : ℕ}

/-- The second chord coefficient of `κ∘κ`: `β₂ = (1 − 2q + κ(0))/2`, `q = κ(κ(0))`. -/
noncomputable def beta2 : ℝ := (1 - 2 * kappa (kappa 0) + kappa 0) / 2

/-- The error constant of the hidden layers of `F`: `(√6 + 2√5·κ(0))/√m_F`. -/
noncomputable def cF (mF : ℕ) : ℝ := (√6 + 2 * √5 * kappa 0) / √(mF : ℝ)

lemma cF_nonneg (mF : ℕ) : 0 ≤ cF mF := by
  have h2 : 0 ≤ kappa 0 := (kappa_mem (by norm_num) (by norm_num)).1
  unfold cF; positivity

lemma beta2_nonneg : 0 ≤ beta2 := by
  have := (kGood_kappa.comp_kappa).chord_coef_nonneg
  simp only [Function.comp, kappa_neg_one] at this
  exact this

/-- For a fixed vector `y`: the mean over the independent network `A′` of the chord bound. -/
theorem agentB_upper (hn : 1 ≤ n) (hmA : 1 ≤ mA) (y x' : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun a' : MlpParam n mA n => psi (kappa ∘ kappa) y (mlpEval a' x') +
      c * (nrm y * nrm (mlpEval a' x'))) (mlpGauss n mA n) ∧
    ∫ a' : MlpParam n mA n, (psi (kappa ∘ kappa) y (mlpEval a' x') +
      c * (nrm y * nrm (mlpEval a' x'))) ∂mlpGauss n mA n ≤
    nrm y * nrm x' * ((kappa (kappa 0) + c) * √2 + beta2 * √(2 / (n : ℝ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hq0 : 0 ≤ kappa (kappa 0) := hG.nonneg_on KGood.zero_mem
  obtain ⟨iN, uN⟩ := mlp_nrm_single (q := n) hmA x'
  obtain ⟨iM, eM⟩ := mlp_form_mean (q := n) hmA y x'
  obtain ⟨iS, eS⟩ := mlp_form_sq (q := n) hmA y x'
  obtain ⟨iA, uA⟩ := integral_abs_le_sqrt (μ := mlpGauss n mA n) (measurable_form y x') iS
  have hyN : Integrable (fun a' : MlpParam n mA n => nrm y * nrm (mlpEval a' x'))
      (mlpGauss n mA n) := iN.const_mul _
  have hmeas : Measurable (fun a' : MlpParam n mA n => psi (kappa ∘ kappa) y (mlpEval a' x')) :=
    Measurable.comp (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) => psi (kappa ∘ kappa) p.1 p.2)
      (f := fun a' : MlpParam n mA n => (y, mlpEval a' x')) (measurable_psi hG.cont)
      (measurable_const.prodMk (continuous_mlpEval_param x').measurable)
  have hpsi : Integrable (fun a' : MlpParam n mA n => psi (kappa ∘ kappa) y (mlpEval a' x'))
      (mlpGauss n mA n) := by
    refine Integrable.mono' hyN hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun a' => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg hG _ _)]
    exact psi_le_nrm hG _ _
  refine ⟨hpsi.add (hyN.const_mul c), ?_⟩
  -- the chord bound, as a linear combination
  obtain ⟨iR, eR⟩ := integral_lin4 (μ := mlpGauss n mA n) hyN iM iA iA 0
    (kappa (kappa 0) + c) (-((1 - kappa 0) / 2)) (-beta2) 0
  have hsum : Integrable (fun a' : MlpParam n mA n => psi (kappa ∘ kappa) y (mlpEval a' x') +
      c * (nrm y * nrm (mlpEval a' x'))) (mlpGauss n mA n) := hpsi.add (hyN.const_mul c)
  have hmono := integral_mono hsum iR (fun a' => by
    have h := psi_chord hG y (mlpEval a' x')
    simp only [Function.comp, kappa_neg_one] at h
    show psi (kappa ∘ kappa) y (mlpEval a' x') + c * (nrm y * nrm (mlpEval a' x')) ≤ _
    unfold beta2
    nlinarith)
  rw [eR, eM] at hmono
  refine hmono.trans ?_
  have hqc : 0 ≤ kappa (kappa 0) + c := by linarith
  have t1 : ∫ a' : MlpParam n mA n, nrm y * nrm (mlpEval a' x') ∂mlpGauss n mA n ≤
      nrm y * (√2 * nrm x') := by
    rw [integral_const_mul]
    have e : (2 : ℝ) * (n : ℝ) / n = 2 := by field_simp
    rw [e] at uN
    exact mul_le_mul_of_nonneg_left uN (nrm_nonneg y)
  have t2 : ∫ a' : MlpParam n mA n, |dotp y (mlpEval a' x')| ∂mlpGauss n mA n ≤
      √(2 / (n : ℝ)) * (nrm x' * nrm y) := by
    rw [eS] at uA
    have e : 2 / (n : ℝ) * normSq x' * normSq y = 2 / (n : ℝ) * (nrm x' * nrm y) ^ 2 := by
      rw [mul_pow, nrm_sq, nrm_sq]; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (nrm_mul_nonneg x' y)] at uA
    exact uA
  have t1' := mul_le_mul_of_nonneg_left t1 hqc
  have t2' := mul_le_mul_of_nonneg_left t2 beta2_nonneg
  nlinarith

lemma kern_abs_le_diag2 (F : MlpParam n mF 1) (a a' : MlpParam n mA n) (x x' : Fin n → ℝ) :
    |kern F a a' x x'| ≤ kern F a a x x + kern F a' a' x' x' := by
  unfold kern
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (mF : ℝ)), dotp_self, dotp_self,
    ← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_dotp_le _ _) (by positivity)

lemma kern_F_integrable (hmF : 1 ≤ mF) (a : MlpParam n mA n) (x : Fin n → ℝ) :
    Integrable (fun F : MlpParam n mF 1 => kern F a a x x) (mlpGauss n mF 1) := by
  have hk : ∀ F : MlpParam n mF 1,
      kern F a a x x = 2 / (mF : ℝ) * normSq (hid2 F.1 F.2.1 (mlpEval a x)) := by
    intro F; unfold kern hidF; rw [dotp_self]
  simp_rw [hk]
  exact (F_hid_sq (mF := mF) (mlpEval a x)).1.const_mul _

/-- `(a′, F) ↦ kern F a′ a′ x x` is integrable. -/
lemma kern_diag_AF (hn : 1 ≤ n) (hmF : 1 ≤ mF) (x : Fin n → ℝ) :
    Integrable (fun y : MlpParam n mA n × MlpParam n mF 1 => kern y.2 y.1 y.1 x x)
      ((mlpGauss n mA n).prod (mlpGauss n mF 1)) := by
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : ∀ (F : MlpParam n mF 1) (a : MlpParam n mA n),
      kern F a a x x = 2 / (mF : ℝ) * normSq (hid2 F.1 F.2.1 (mlpEval a x)) := by
    intro F a; unfold kern hidF; rw [dotp_self]
  have hmeas : Measurable (fun y : MlpParam n mA n × MlpParam n mF 1 => kern y.2 y.1 y.1 x x) :=
    measurable_kern_comp measurable_snd measurable_fst measurable_fst measurable_const
      measurable_const
  exact (prod_step (μ := mlpGauss n mA n) (ν := mlpGauss n mF 1) hmeas
    (fun p => by rw [hk]; exact mul_nonneg (by positivity) (normSq_nonneg _))
    (fun a => 2 / (mF : ℝ) * ((mF : ℝ) / 2 * (2 / (mF : ℝ)) * ((mF : ℝ) / 2 * (2 / (n : ℝ))) *
      normSq (mlpEval a x)))
    (fun a => by
      obtain ⟨hi, he⟩ := F_hid_sq (mF := mF) (mlpEval a x)
      simp_rw [hk]
      exact ⟨hi.const_mul _, by rw [integral_const_mul, he]⟩)
    (((mlp_normSq_integrable x).const_mul _).const_mul _)).1

lemma kern_cross_inner_integrable (hn : 1 ≤ n) (hmF : 1 ≤ mF) (a : MlpParam n mA n)
    (x x' : Fin n → ℝ) :
    Integrable (fun y : MlpParam n mA n × MlpParam n mF 1 => kern y.2 a y.1 x x')
      ((mlpGauss n mA n).prod (mlpGauss n mF 1)) := by
  have hmeas : Measurable (fun y : MlpParam n mA n × MlpParam n mF 1 => kern y.2 a y.1 x x') :=
    measurable_kern_comp measurable_snd measurable_const measurable_fst measurable_const
      measurable_const
  exact Integrable.mono' (((kern_F_integrable hmF a x).comp_snd _).add (kern_diag_AF hn hmF x'))
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => kern_abs_le_diag2 _ _ _ _ _)

lemma kern_cross_integrable (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) (x x' : Fin n → ℝ) :
    Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.2.1 x x')
      ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) := by
  have hmeas : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.2.1 x x') :=
    measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst
      (measurable_fst.comp measurable_snd) measurable_const measurable_const
  exact Integrable.mono' ((kern_diag_gen hn hmA hmF x).1.add ((kern_diag_AF hn hmF x').comp_snd _))
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => kern_abs_le_diag2 _ _ _ _ _)

/-- The inner bound, for a fixed first network `a`. -/
lemma kern_cross_inner (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) (a : MlpParam n mA n)
    {x x' : Fin n → ℝ} (hx' : normSq x' = 1) :
    ∫ y : MlpParam n mA n × MlpParam n mF 1, kern y.2 a y.1 x x'
      ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
    2 / (n : ℝ) * (nrm (mlpEval a x) *
      ((kappa (kappa 0) + cF mF) * √2 + beta2 * √(2 / (n : ℝ)))) := by
  obtain ⟨iB, uB⟩ := agentB_upper hn hmA (mlpEval a x) x' (cF mF) (cF_nonneg mF)
  have key := integral_prod_le (kern_cross_inner_integrable hn hmF a x x')
    (g := fun a' : MlpParam n mA n => 2 / (n : ℝ) *
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a' x') +
        cF mF * (nrm (mlpEval a x) * nrm (mlpEval a' x'))))
    (iB.const_mul _) (fun a' => KF_upper hn hmF (mlpEval a x) (mlpEval a' x'))
  refine key.trans ?_
  rw [integral_const_mul]
  rw [nrm_of_normSq_one hx', mul_one] at uB
  exact mul_le_mul_of_nonneg_left uB (by positivity)

/-- **The cross kernel**: for unit vectors `x, x′` and two independent Agent networks,
`E kern F A A′ x x′ ≤ (4/n)·(q + β₂/√n + (√6 + 2√5·κ(0))/√m_F)`. -/
theorem kern_cross_upper (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.2.1 x x'
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
    4 / (n : ℝ) * (kappa (kappa 0) + beta2 / √(n : ℝ) + cF mF) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨iN, uN⟩ := mlp_nrm_single (q := n) hmA x
  set K : ℝ := (kappa (kappa 0) + cF mF) * √2 + beta2 * √(2 / (n : ℝ)) with hK
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ kappa (kappa 0) := (kGood_kappa.comp_kappa).nonneg_on KGood.zero_mem
    have h2 := cF_nonneg mF
    have h3 := beta2_nonneg
    rw [hK]; positivity
  have key := integral_prod_le (kern_cross_integrable hn hmA hmF x x')
    (g := fun a : MlpParam n mA n => 2 / (n : ℝ) * (nrm (mlpEval a x) * K))
    ((iN.mul_const _).const_mul _) (fun a => kern_cross_inner hn hmA hmF a hx')
  refine key.trans ?_
  rw [integral_const_mul, integral_mul_const]
  have e : (2 : ℝ) * (n : ℝ) / n = 2 := by field_simp
  rw [e, nrm_of_normSq_one hx, mul_one] at uN
  have h1 := mul_le_mul_of_nonneg_right uN hK0
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ))
  refine h2.trans (le_of_eq ?_)
  have s2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have s3 : √(2 / (n : ℝ)) = √2 / √(n : ℝ) := Real.sqrt_div (by norm_num) _
  have hsn : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  rw [hK, s3]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

lemma kgen_ftf_eq (uu : (Fin N → ℝ) × (Fin N → ℝ)) (w : MlpParam N mW n)
    (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) :
    kgen false true false (uu, (w, p)) = kern p.2.2 p.1 p.2.1 (xW w uu.1) (xW w uu.2) := rfl

lemma kgen_ftf_section (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    (uu : (Fin N → ℝ) × (Fin N → ℝ)) (w : MlpParam N mW n) :
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kgen false true false (uu, (w, p))
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
    4 / (n : ℝ) * (kappa (kappa 0) + beta2 / √(n : ℝ) + cF mF) := by
  simp only [kgen_ftf_eq]
  exact kern_cross_upper hn hmA hmF (normSq_xW hn w uu.1) (normSq_xW hn w uu.2)

/-- **The upper bound of `b₁₁`** (paper: `b₁₁ ≤ S(q + 2.76/n + c₀/√m_F)`; here
`b11 ≤ (4/n)·(q + β₂/√n + (√6 + 2√5·κ(0))/√m_F)`, `β₂ = (1 − 2q + κ(0))/2`). -/
theorem b11_upper (hN : 1 ≤ N) (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) :
    b11 N mW n mA mF ≤ 4 / (n : ℝ) * (kappa (kappa 0) + beta2 / √(n : ℝ) + cF mF) := by
  have := uniformSphere_isProbability N hN
  have hprob : IsProbabilityMeasure (lawU2 N) := by unfold lawU2; infer_instance
  rw [b11_eq]
  exact integral_le_of_sections (lawU2 N) (mlpGauss N mW n)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
    (f := kgen false true false) (kgen_integrable hn hN false true false)
    (kgen_ftf_section hn hmA hmF)

end BstLean.Part132

open BstLean.Part132 in
#print axioms kern_cross_upper
open BstLean.Part132 in
#print axioms b11_upper
