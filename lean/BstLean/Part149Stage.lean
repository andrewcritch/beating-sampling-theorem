import BstLean.Part149StandIn
import BstLean.Part149LemmaC

/-!
# Part 149: the stage of the Agent network for a fixed input measure and fixed hidden weights

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, items 1 and 4 (the `A`-stage error). `(U, μ)` is the
probability space of the stand-in inputs, `h : U → ℝ^m` the bounded hidden map
(`h(u) = a₂(x(u))`), `b ≠ 0` a centre, `A₃` a Gaussian `n × m` matrix with entry variance `v`,
`F` a random network `ℝⁿ → ℝ` (independent of `A₃`). With `p = (A₃, F)`:

* `gT μ h p = E_u F(A₃ h(u))`: the true mean (no program computes it).
* `gM μ h v b p = E_u E_γ F(λ(u)·A₃b + σ(u)·γ)`: the mean over the stand-in.
* `gO b τ p = E_γ F(A₃ b + τ·γ)`: the mean over the stand-in with CONSTANT scalars `1` and `τ`:
  the output of the program (forward passes of `F` only).
* `stageU` (`standInA149` for the test function `F`): `E (gT − gM)² ≤ L·2v·E_u|r(u)|²`.
* `stageM` (Lemma C): `E (gM − gO)² ≤ 2·(v·E_u|b|²(λ(u) − 1)² + E_u(σ(u) − τ)²)`.
* `stageA`: `E (gT − gO)² ≤ (1 + η)·(…) + (1 + 1/η)·(…)`.
All three are in `ℝ≥0∞`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134

variable {n m mF : ℕ} {U : Type*} [MeasurableSpace U]

/-- The value of the network `F` at `y`. -/
noncomputable def evF (F : MlpParam n mF 1) (y : Fin n → ℝ) : ℝ := mlpEval F y 0

lemma measurable_evF_joint :
    Measurable (fun p : MlpParam n mF 1 × (Fin n → ℝ) => evF p.1 p.2) :=
  ((continuous_apply 0).comp continuous_mlpEval_joint).measurable

lemma measurable_evF_comp {α : Type*} [MeasurableSpace α] {f : α → MlpParam n mF 1}
    {g : α → Fin n → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => evF (f x) (g x)) :=
  measurable_evF_joint.comp (hf.prodMk hg)

lemma measurable_evF (F : MlpParam n mF 1) : Measurable (evF F) :=
  measurable_evF_joint.comp measurable_prodMk_left

lemma normSq_reluV_le {ι : Type*} [Fintype ι] (x : ι → ℝ) : normSq (reluV x) ≤ normSq x := by
  unfold normSq reluV
  refine Finset.sum_le_sum fun i _ => ?_
  have := abs_relu_le (x i)
  rw [← sq_abs (relu (x i)), ← sq_abs (x i)]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

/-- `F` has linear growth: `F(y)² ≤ C_F·(1 + |y|²)`. -/
lemma evF_growth (F : MlpParam n mF 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, evF F y ^ 2 ≤ C * (1 + normSq y) := by
  set f1 : ℝ := ∑ i, ∑ j, F.1 i j ^ 2 with hf1
  set f2 : ℝ := ∑ i, ∑ j, F.2.1 i j ^ 2 with hf2
  set f3 : ℝ := ∑ i, ∑ j, F.2.2 i j ^ 2 with hf3
  have h1 : 0 ≤ f1 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ f2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h3 : 0 ≤ f3 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨f3 * (f2 * f1), by positivity, fun y => ?_⟩
  have e0 : evF F y ^ 2 ≤ normSq (mlpEval F y) := by
    unfold evF normSq
    exact Finset.single_le_sum (f := fun i => mlpEval F y i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ 0)
  have e1 : normSq (mlpEval F y) ≤ f3 * normSq (reluV (F.2.1.mulVec (reluV (F.1.mulVec y)))) :=
    normSq_mulVec_le _ _
  have e2 : normSq (reluV (F.2.1.mulVec (reluV (F.1.mulVec y)))) ≤
      f2 * normSq (reluV (F.1.mulVec y)) :=
    (normSq_reluV_le _).trans (normSq_mulVec_le _ _)
  have e3 : normSq (reluV (F.1.mulVec y)) ≤ f1 * normSq y :=
    (normSq_reluV_le _).trans (normSq_mulVec_le _ _)
  have hy := normSq_nonneg y
  calc evF F y ^ 2 ≤ f3 * (f2 * (f1 * normSq y)) :=
        e0.trans (e1.trans (mul_le_mul_of_nonneg_left
          (e2.trans (mul_le_mul_of_nonneg_left e3 h2)) h3))
    _ ≤ f3 * (f2 * f1) * (1 + normSq y) := by
        have : 0 ≤ f3 * (f2 * f1) := by positivity
        nlinarith

/-- The true mean `E_u F(A₃ h(u))`, `p = (A₃, F)`. -/
noncomputable def gT (μ : Measure U) (h : U → Fin m → ℝ)
    (p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) : ℝ :=
  outTrue μ h (evF p.2) p.1

/-- The mean over the stand-in of `A`: `E_u E_γ F(λ(u)·A₃b + σ(u)·γ)`. -/
noncomputable def gM (μ : Measure U) (h : U → Fin m → ℝ) (v : ℝ) (b : Fin m → ℝ)
    (p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) : ℝ :=
  outStand μ h v b (evF p.2) (p.1.mulVec b)

/-- The output: the mean over the stand-in with constant scalars, `E_γ F(A₃b + τ·γ)`. -/
noncomputable def gO (b : Fin m → ℝ) (τ : ℝ)
    (p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) : ℝ :=
  ∫ γ, evF p.2 (p.1.mulVec b + τ • γ) ∂stdGauss (Fin n)

section meas

variable (μ : Measure U) [IsProbabilityMeasure μ]

lemma measurable_gT {h : U → Fin m → ℝ} (hh : Measurable h) :
    Measurable (gT (n := n) (mF := mF) μ h) := by
  have h1 : Measurable (fun q : (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × U =>
      evF q.1.2 (q.1.1.mulVec (h q.2))) :=
    measurable_evF_joint.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_mulVec_joint.comp ((measurable_fst.comp measurable_fst).prodMk
        (hh.comp measurable_snd))))
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma measurable_gM {h : U → Fin m → ℝ} (hh : Measurable h) (v : ℝ) (b : Fin m → ℝ) :
    Measurable (gM (n := n) (mF := mF) μ h v b) := by
  have h1 : Measurable (fun q : ((Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × U) ×
      (Fin n → ℝ) =>
      evF q.1.1.2 (lam b (h q.1.2) • q.1.1.1.mulVec b + sig v b (h q.1.2) • q.2)) := by
    refine measurable_evF_joint.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      ?_)
    exact (((measurable_lam b).comp (hh.comp (measurable_snd.comp measurable_fst))).smul
      ((measurable_mulVec_right b).comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))).add
      (((measurable_sig v b).comp (hh.comp (measurable_snd.comp measurable_fst))).smul measurable_snd)
  have h2 := (h1.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n)))
  exact (h2.integral_prod_right' (ν := μ)).measurable

omit [MeasurableSpace U] in
lemma measurable_gO (b : Fin m → ℝ) (τ : ℝ) : Measurable (gO (n := n) (mF := mF) b τ) := by
  have h1 : Measurable (fun q : (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × (Fin n → ℝ) =>
      evF q.1.2 (q.1.1.mulVec b + τ • q.2)) :=
    measurable_evF_joint.comp ((measurable_snd.comp measurable_fst).prodMk
      (((measurable_mulVec_right b).comp (measurable_fst.comp measurable_fst)).add
        (measurable_snd.const_smul τ)))
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

end meas

lemma bm_of_sq_le {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ x, f x ^ 2 ≤ K) : BM f := by
  refine ⟨hf, 1 + K, fun x => ?_⟩
  have := hK x
  nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x), abs_nonneg (f x)]

/-- `E_γ |a + s·γ|² = |a|² + s²·n`. -/
lemma gauss_shift_normSq (a : Fin n → ℝ) (s : ℝ) :
    Integrable (fun γ : Fin n → ℝ => normSq (a + s • γ)) (stdGauss (Fin n)) ∧
    ∫ γ, normSq (a + s • γ) ∂stdGauss (Fin n) = normSq a + s ^ 2 * n := by
  have e : (fun γ : Fin n → ℝ => normSq (a + s • γ)) =
      fun γ => (normSq a + ∑ i, (2 * s * a i) * γ i) + s ^ 2 * normSq γ := by
    funext γ
    simp only [normSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have ic : ∀ i : Fin n, Integrable (fun γ : Fin n → ℝ => γ i) (stdGauss (Fin n)) := by
    intro i
    have := integrable_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := i)
      (f := fun x : ℝ => x) (by simpa using integrable_pow_gauss 1)
    exact this
  have i1 : Integrable (fun γ : Fin n → ℝ => ∑ i, (2 * s * a i) * γ i) (stdGauss (Fin n)) :=
    integrable_finsetSum _ fun i _ => (ic i).const_mul _
  have i2 := (stdGauss_normSq n).1.const_mul (s ^ 2)
  have i0 : Integrable (fun _ : Fin n → ℝ => normSq a) (stdGauss (Fin n)) := integrable_const _
  rw [e]
  refine ⟨(i0.add i1).add i2, ?_⟩
  rw [integral_add (f := fun γ : Fin n → ℝ => normSq a + ∑ i, (2 * s * a i) * γ i)
      (g := fun γ => s ^ 2 * normSq γ) (i0.add i1) i2,
    integral_add (f := fun _ : Fin n → ℝ => normSq a)
      (g := fun γ => ∑ i, (2 * s * a i) * γ i) i0 i1,
    integral_finsetSum _ fun i _ => (ic i).const_mul _, integral_const_mul, (stdGauss_normSq n).2]
  simp only [integral_const_mul, BstLean.Part112.integral_coord, mul_zero, Finset.sum_const_zero,
    integral_const, probReal_univ, smul_eq_mul, one_mul, add_zero]

section stage

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- A test function of linear growth, composed with a map `q` of quadratic growth in the
Gaussian coordinate, is integrable. -/
lemma growth_integrable {ψ : (Fin n → ℝ) → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, ψ y ^ 2 ≤ C * (1 + normSq y)) {q : U × (Fin n → ℝ) → Fin n → ℝ}
    (mq : Measurable q) {A B : ℝ} (hq : ∀ p, normSq (q p) ≤ A + B * normSq p.2) :
    Integrable (fun p => ψ (q p)) (μ.prod (stdGauss (Fin n))) := by
  have i1 : Integrable (fun p : U × (Fin n → ℝ) => normSq p.2) (μ.prod (stdGauss (Fin n))) :=
    (stdGauss_normSq n).1.comp_snd μ
  have iG : Integrable (fun p : U × (Fin n → ℝ) => (1 + C * (1 + A)) + (C * B) * normSq p.2)
      (μ.prod (stdGauss (Fin n))) := (integrable_const _).add (i1.const_mul _)
  refine Integrable.mono' iG (hψ.comp mq).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hC (q p)
  have h2 : |ψ (q p)| ≤ 1 + ψ (q p) ^ 2 := by
    nlinarith [sq_nonneg (|ψ (q p)| - 1), abs_nonneg (ψ (q p)), sq_abs (ψ (q p))]
  have h3 : C * (1 + normSq (q p)) ≤ C * (1 + (A + B * normSq p.2)) :=
    mul_le_mul_of_nonneg_left (by linarith [hq p]) hC0
  nlinarith

/-- **The stand-in error of `A` for the test function `F`** (Theorem S1-A with Lemma C for the
variance): `E_{A₃, F} (E_u F(A₃h(u)) − E_u E_γ F(λ(u)A₃b + σ(u)γ))² ≤ L·2v·R`, if
`E_u |r(u)|² ≤ R`. -/
theorem stageU {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {H : ℝ} (hH : ∀ u, normSq (h u) ≤ H) (hn : 1 ≤ n) (hmF : 1 ≤ mF)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2)
    {R : ℝ} (hR : ∫ u, normSq (res b (h u)) ∂μ ≤ R) :
    ∫⁻ p, ENNReal.ofReal ((gT μ h p - gM μ h v b p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1)) ≤ ENNReal.ofReal (L * (2 * v * R)) := by
  have mTM : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gT μ h p - gM μ h v b p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_gT μ hh).sub (measurable_gM μ hh v b)).pow_const 2)
  rw [lintegral_prod_symm' _ mTM]
  -- the integrand of the right side, jointly measurable
  set Q4 : ((MlpParam n mF 1 × (Fin n → ℝ)) × U) × (Fin n → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((evF x.1.1.1 (lam b (h x.1.2) • x.1.1.2 + sig v b (h x.1.2) • x.2) -
      evF x.1.1.1 (lam b (h x.1.2) • x.1.1.2)) ^ 2) with hQ4
  have mf1 : Measurable (fun x : ((MlpParam n mF 1 × (Fin n → ℝ)) × U) × (Fin n → ℝ) =>
      x.1.1.1) := measurable_fst.comp (measurable_fst.comp measurable_fst)
  have mc1 : Measurable (fun x : ((MlpParam n mF 1 × (Fin n → ℝ)) × U) × (Fin n → ℝ) =>
      x.1.1.2) := measurable_snd.comp (measurable_fst.comp measurable_fst)
  have mu1 : Measurable (fun x : ((MlpParam n mF 1 × (Fin n → ℝ)) × U) × (Fin n → ℝ) =>
      h x.1.2) := hh.comp (measurable_snd.comp measurable_fst)
  have ma1 : Measurable (fun x : ((MlpParam n mF 1 × (Fin n → ℝ)) × U) × (Fin n → ℝ) =>
      lam b (h x.1.2) • x.1.1.2) := ((measurable_lam b).comp mu1).smul mc1
  have ma2 : Measurable (fun x : ((MlpParam n mF 1 × (Fin n → ℝ)) × U) × (Fin n → ℝ) =>
      lam b (h x.1.2) • x.1.1.2 + sig v b (h x.1.2) • x.2) :=
    ma1.add (((measurable_sig v b).comp mu1).smul measurable_snd)
  have mQ4 : Measurable Q4 :=
    ENNReal.measurable_ofReal.comp
      (((measurable_evF_comp mf1 ma2).sub (measurable_evF_comp mf1 ma1)).pow_const 2)
  set g2 : (MlpParam n mF 1 × (Fin n → ℝ)) × U → ℝ≥0∞ := fun x =>
    ∫⁻ γ, Q4 (x, γ) ∂stdGauss (Fin n) with hg2
  have mg2 : Measurable g2 := mQ4.lintegral_prod_right'
  set g1 : MlpParam n mF 1 × (Fin n → ℝ) → ℝ≥0∞ := fun x => ∫⁻ u, g2 (x, u) ∂μ with hg1
  have mg1 : Measurable g1 := mg2.lintegral_prod_right'
  have step : ∀ F : MlpParam n mF 1,
      ∫⁻ M, ENNReal.ofReal ((gT μ h (M, F) - gM μ h v b (M, F)) ^ 2) ∂gaussMat n m v ≤
        ENNReal.ofReal L * ∫⁻ c, g1 (F, c) ∂cDist n v b := by
    intro F
    obtain ⟨C, _, hC⟩ := evF_growth F
    exact standIn_lint μ hv hb hh hH (measurable_evF F) hC hL0 hL
  -- the inner bound from Lemma C
  have inner : ∀ (c : Fin n → ℝ) (u : U),
      ∫⁻ F, g2 ((F, c), u) ∂mlpGauss n mF 1 ≤ ENNReal.ofReal (2 * sig v b (h u) ^ 2) := by
    intro c u
    obtain ⟨hi, hle⟩ := lemmaC_gauss (m := mF) hn hmF (lam b (h u) • c) (sig v b (h u))
    have mf : Measurable (fun p : MlpParam n mF 1 × (Fin n → ℝ) =>
        ENNReal.ofReal ((mlpEval p.1 (lam b (h u) • c + sig v b (h u) • p.2) 0 -
          mlpEval p.1 (lam b (h u) • c) 0) ^ 2)) := by
      have : (fun p : MlpParam n mF 1 × (Fin n → ℝ) =>
          ENNReal.ofReal ((mlpEval p.1 (lam b (h u) • c + sig v b (h u) • p.2) 0 -
            mlpEval p.1 (lam b (h u) • c) 0) ^ 2)) = fun p => Q4 (((p.1, c), u), p.2) := rfl
      rw [this]
      exact mQ4.comp (((measurable_fst.prodMk measurable_const).prodMk measurable_const).prodMk
        measurable_snd)
    have e1 : ∫⁻ F, g2 ((F, c), u) ∂mlpGauss n mF 1 =
        ∫⁻ p, ENNReal.ofReal ((mlpEval p.1 (lam b (h u) • c + sig v b (h u) • p.2) 0 -
          mlpEval p.1 (lam b (h u) • c) 0) ^ 2) ∂((mlpGauss n mF 1).prod (stdGauss (Fin n))) := by
      rw [lintegral_prod _ mf.aemeasurable]
      rfl
    rw [e1, ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  -- `σ²` is bounded
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  obtain ⟨u0⟩ := μ.nonempty_of_neZero
  have hH0 : 0 ≤ H := (normSq_nonneg _).trans (hH u0)
  have esig : ∀ u, sig v b (h u) ^ 2 = v * normSq (res b (h u)) := by
    intro u
    unfold sig
    rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (normSq_nonneg _)]
  have bres : BM (fun u => normSq (res b (h u))) := by
    refine ⟨measurable_normSq.comp ((measurable_res b).comp hh), H, fun u => ?_⟩
    rw [abs_of_nonneg (normSq_nonneg _)]
    exact (normSq_res_le hb _).trans (hH u)
  calc ∫⁻ F, ∫⁻ M, ENNReal.ofReal ((gT μ h (M, F) - gM μ h v b (M, F)) ^ 2) ∂gaussMat n m v
        ∂mlpGauss n mF 1
      ≤ ∫⁻ F, ENNReal.ofReal L * ∫⁻ c, g1 (F, c) ∂cDist n v b ∂mlpGauss n mF 1 :=
        lintegral_mono step
    _ = ENNReal.ofReal L * ∫⁻ F, ∫⁻ c, g1 (F, c) ∂cDist n v b ∂mlpGauss n mF 1 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal L * ∫⁻ c, ∫⁻ F, g1 (F, c) ∂mlpGauss n mF 1 ∂cDist n v b := by
        rw [lintegral_lintegral_swap (f := fun F c => g1 (F, c)) mg1.aemeasurable]
    _ ≤ ENNReal.ofReal L * ∫⁻ c, ENNReal.ofReal (2 * v * R) ∂cDist n v b := by
        refine mul_le_mul' le_rfl (lintegral_mono fun c => ?_)
        have mg2c : Measurable (fun x : MlpParam n mF 1 × U => g2 ((x.1, c), x.2)) :=
          mg2.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
        calc ∫⁻ F, g1 (F, c) ∂mlpGauss n mF 1
            = ∫⁻ u, ∫⁻ F, g2 ((F, c), u) ∂mlpGauss n mF 1 ∂μ :=
              lintegral_lintegral_swap (f := fun F u => g2 ((F, c), u)) mg2c.aemeasurable
          _ ≤ ∫⁻ u, ENNReal.ofReal (2 * sig v b (h u) ^ 2) ∂μ := lintegral_mono fun u => inner c u
          _ = ENNReal.ofReal (∫ u, 2 * sig v b (h u) ^ 2 ∂μ) := by
              simp_rw [esig]
              exact (ofReal_integral_eq_lintegral_ofReal
                (((BM.const (2 : ℝ)).mul ((BM.const v).mul bres)).integrable μ)
                (Filter.Eventually.of_forall fun u =>
                  mul_nonneg (by norm_num) (mul_nonneg hv (normSq_nonneg _)))).symm
          _ ≤ ENNReal.ofReal (2 * v * R) := by
              refine ENNReal.ofReal_le_ofReal ?_
              simp_rw [esig]
              rw [integral_const_mul, integral_const_mul]
              have := mul_le_mul_of_nonneg_left hR hv
              linarith
    _ = ENNReal.ofReal (L * (2 * v * R)) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_mul hL0]

/-- **The price of constant scalars for the test function `F`** (Lemma C, the coupling through
the same Gaussian vector): `E_{A₃, F} (E_u E_γ F(λ(u)A₃b + σ(u)γ) − E_γ F(A₃b + τγ))² ≤
2·(v·E_u|b|²(λ(u) − 1)² + E_u(σ(u) − τ)²)`. -/
theorem stageM {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {H : ℝ} (hH : ∀ u, normSq (h u) ≤ H) (hn : 1 ≤ n) (hmF : 1 ≤ mF)
    (τ : ℝ) {Yl S : ℝ}
    (hYl : ∫ u, normSq b * (lam b (h u) - 1) ^ 2 ∂μ ≤ Yl)
    (hS : ∫ u, (sig v b (h u) - τ) ^ 2 ∂μ ≤ S) :
    ∫⁻ p, ENNReal.ofReal ((gM μ h v b p - gO b τ p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1)) ≤ ENNReal.ofReal (2 * (v * Yl + S)) := by
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  obtain ⟨u0⟩ := μ.nonempty_of_neZero
  have hH0 : 0 ≤ H := (normSq_nonneg _).trans (hH u0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have mMO : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gM μ h v b p - gO b τ p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_gM μ hh v b).sub (measurable_gO b τ)).pow_const 2)
  rw [lintegral_prod _ mMO.aemeasurable]
  have hlam2 : ∀ u, lam b (h u) ^ 2 ≤ H / normSq b := fun u =>
    (lam_sq_le hb _).trans (div_le_div_of_nonneg_right (hH u) hb0.le)
  have hsig2 : ∀ u, sig v b (h u) ^ 2 ≤ v * H := by
    intro u
    unfold sig
    rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (normSq_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((normSq_res_le hb _).trans (hH u)) hv
  have blam : BM (fun u => lam b (h u)) :=
    bm_of_sq_le ((measurable_lam b).comp hh) hlam2
  have bsig : BM (fun u => sig v b (h u)) :=
    bm_of_sq_le ((measurable_sig v b).comp hh) hsig2
  set Λ2 : ℝ := ∫ u, (lam b (h u) - 1) ^ 2 ∂μ with hΛ2
  set S2 : ℝ := ∫ u, (sig v b (h u) - τ) ^ 2 ∂μ with hS2
  have hΛ20 : 0 ≤ Λ2 := integral_nonneg fun _ => sq_nonneg _
  have hS20 : 0 ≤ S2 := integral_nonneg fun _ => sq_nonneg _
  -- fixed `A₃`
  have key : ∀ M : Matrix (Fin n) (Fin m) ℝ,
      ∫⁻ F, ENNReal.ofReal ((gM μ h v b (M, F) - gO b τ (M, F)) ^ 2) ∂mlpGauss n mF 1 ≤
        ENNReal.ofReal (2 / (n : ℝ) * (normSq (M.mulVec b) * Λ2 + (n : ℝ) * S2)) := by
    intro M
    set c := M.mulVec b with hc
    set X : U × (Fin n → ℝ) → Fin n → ℝ := fun ω => c + τ • ω.2 with hX
    set Y : U × (Fin n → ℝ) → Fin n → ℝ :=
      fun ω => lam b (h ω.1) • c + sig v b (h ω.1) • ω.2 with hY
    have mX : Measurable X := measurable_const.add (measurable_snd.const_smul τ)
    have mY : Measurable Y := measurable_standOut hh v b c
    -- `E |X − Y|²`
    have eXY : ∀ ω, X ω - Y ω = (1 - lam b (h ω.1)) • c + (τ - sig v b (h ω.1)) • ω.2 := by
      intro ω
      simp only [hX, hY]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have mXY : Measurable (fun ω => normSq (X ω - Y ω)) :=
      measurable_normSq.comp (mX.sub mY)
    have bg : BM (fun u : U => (1 - lam b (h u)) ^ 2 * normSq c +
        (τ - sig v b (h u)) ^ 2 * (n : ℝ)) :=
      ((((BM.const 1).sub blam).sq).mul (BM.const _)).add
        ((((BM.const τ).sub bsig).sq).mul (BM.const _))
    obtain ⟨iXY, eI⟩ := prod_step (μ := μ) (ν := stdGauss (Fin n)) mXY
      (fun _ => normSq_nonneg _)
      (fun u => (1 - lam b (h u)) ^ 2 * normSq c + (τ - sig v b (h u)) ^ 2 * (n : ℝ))
      (fun u => by
        have hg := gauss_shift_normSq ((1 - lam b (h u)) • c) (τ - sig v b (h u))
        simp_rw [eXY]
        refine ⟨hg.1, ?_⟩
        rw [hg.2, normSq_smul])
      (bg.integrable μ)
    have eI2 : ∫ ω, normSq (X ω - Y ω) ∂(μ.prod (stdGauss (Fin n))) =
        normSq c * Λ2 + (n : ℝ) * S2 := by
      rw [eI, integral_add (((((BM.const 1).sub blam).sq).mul (BM.const _)).integrable μ)
        (((((BM.const τ).sub bsig).sq).mul (BM.const _)).integrable μ), integral_mul_const,
        integral_mul_const, hΛ2, hS2]
      have e1 : ∀ u, (1 - lam b (h u)) ^ 2 = (lam b (h u) - 1) ^ 2 := fun u => by ring
      have e2 : ∀ u, (τ - sig v b (h u)) ^ 2 = (sig v b (h u) - τ) ^ 2 := fun u => by ring
      simp_rw [e1, e2]
      ring
    obtain ⟨hint, hle⟩ := lemmaC149 (μ.prod (stdGauss (Fin n))) (m := mF) hn hmF mX mY iXY
    rw [eI2] at hle
    -- the integral of the difference
    have ediff : ∀ F : MlpParam n mF 1,
        ∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂(μ.prod (stdGauss (Fin n))) =
          gO b τ (M, F) - gM μ h v b (M, F) := by
      intro F
      obtain ⟨C, hC0, hC⟩ := evF_growth F
      have iX : Integrable (fun ω => evF F (X ω)) (μ.prod (stdGauss (Fin n))) := by
        refine growth_integrable μ (measurable_evF F) hC0 hC mX (A := 2 * normSq c)
          (B := 2 * τ ^ 2) fun p => ?_
        have := normSq_add_le c (τ • p.2)
        rw [normSq_smul] at this
        simp only [hX]
        linarith
      have iY : Integrable (fun ω => evF F (Y ω)) (μ.prod (stdGauss (Fin n))) := by
        refine growth_integrable μ (measurable_evF F) hC0 hC mY
          (A := 2 * (H / normSq b * normSq c)) (B := 2 * (v * H)) fun p => ?_
        have h1 := normSq_add_le (lam b (h p.1) • c) (sig v b (h p.1) • p.2)
        rw [normSq_smul, normSq_smul] at h1
        have h4 : lam b (h p.1) ^ 2 * normSq c ≤ H / normSq b * normSq c :=
          mul_le_mul_of_nonneg_right (hlam2 p.1) (normSq_nonneg _)
        have h5 : sig v b (h p.1) ^ 2 * normSq p.2 ≤ v * H * normSq p.2 :=
          mul_le_mul_of_nonneg_right (hsig2 p.1) (normSq_nonneg _)
        simp only [hY]
        linarith
      have e1 : ∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂(μ.prod (stdGauss (Fin n))) =
          ∫ ω, evF F (X ω) ∂(μ.prod (stdGauss (Fin n))) -
            ∫ ω, evF F (Y ω) ∂(μ.prod (stdGauss (Fin n))) := integral_sub iX iY
      rw [e1, integral_prod _ iX, integral_prod _ iY]
      simp only [hX, hY, integral_const, probReal_univ, smul_eq_mul, one_mul]
      rfl
    have e2 : ∀ F : MlpParam n mF 1, (gM μ h v b (M, F) - gO b τ (M, F)) ^ 2 =
        (∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂(μ.prod (stdGauss (Fin n)))) ^ 2 := by
      intro F
      rw [ediff]
      ring
    simp_rw [e2]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  -- integrate over `A₃`
  have iM := (layer_lin_sq (m := n) (k := m) hv b).1
  have eM := (layer_lin_sq (m := n) (k := m) hv b).2
  have iR : Integrable (fun M : Matrix (Fin n) (Fin m) ℝ =>
      2 / (n : ℝ) * (normSq (M.mulVec b) * Λ2 + (n : ℝ) * S2)) (gaussMat n m v) :=
    ((iM.mul_const _).add (integrable_const _)).const_mul _
  calc ∫⁻ M, ∫⁻ F, ENNReal.ofReal ((gM μ h v b (M, F) - gO b τ (M, F)) ^ 2) ∂mlpGauss n mF 1
        ∂gaussMat n m v
      ≤ ∫⁻ M, ENNReal.ofReal (2 / (n : ℝ) * (normSq (M.mulVec b) * Λ2 + (n : ℝ) * S2))
          ∂gaussMat n m v := lintegral_mono key
    _ = ENNReal.ofReal (∫ M, 2 / (n : ℝ) * (normSq (M.mulVec b) * Λ2 + (n : ℝ) * S2)
          ∂gaussMat n m v) :=
        (ofReal_integral_eq_lintegral_ofReal iR (Filter.Eventually.of_forall fun M => by
          have := normSq_nonneg (M.mulVec b)
          positivity)).symm
    _ ≤ ENNReal.ofReal (2 * (v * Yl + S)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add (iM.mul_const _) (integrable_const _),
          integral_mul_const, eM]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        have h1 : normSq b * Λ2 ≤ Yl := by
          rw [hΛ2, ← integral_const_mul]
          exact hYl
        have h2 : 2 / (n : ℝ) * ((n : ℝ) * (v * normSq b) * Λ2 + (n : ℝ) * S2) =
            2 * (v * (normSq b * Λ2) + S2) := by
          field_simp
        rw [h2]
        have := mul_le_mul_of_nonneg_left h1 hv
        linarith

/-- **The error of the stage of `A`**, for a fixed input measure and fixed hidden weights of `A`:
`E_{A₃, F} (E_u F(A₃h(u)) − E_γ F(A₃b + τγ))² ≤
(1 + η)·L·2v·R + (1 + 1/η)·2·(v·Yl + S)`. -/
theorem stageA {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {H : ℝ} (hH : ∀ u, normSq (h u) ≤ H) (hn : 1 ≤ n) (hmF : 1 ≤ mF)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2)
    {R : ℝ} (hR : ∫ u, normSq (res b (h u)) ∂μ ≤ R) (τ : ℝ) {Yl S : ℝ}
    (hYl : ∫ u, normSq b * (lam b (h u) - 1) ^ 2 ∂μ ≤ Yl)
    (hS : ∫ u, (sig v b (h u) - τ) ^ 2 ∂μ ≤ S) {η : ℝ} (hη : 0 < η) :
    ∫⁻ p, ENNReal.ofReal ((gT μ h p - gO b τ p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal ((1 + η) * (L * (2 * v * R)) + (1 + 1 / η) * (2 * (v * Yl + S))) := by
  have hR0 : 0 ≤ R := (integral_nonneg fun _ => normSq_nonneg _).trans hR
  have hYl0 : 0 ≤ Yl :=
    (integral_nonneg fun _ => mul_nonneg (normSq_nonneg _) (sq_nonneg _)).trans hYl
  have hS0 : 0 ≤ S := (integral_nonneg fun _ => sq_nonneg _).trans hS
  have m1 : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gT μ h p - gM μ h v b p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_gT μ hh).sub (measurable_gM μ hh v b)).pow_const 2)
  have m2 : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gM μ h v b p - gO b τ p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_gM μ hh v b).sub (measurable_gO b τ)).pow_const 2)
  have pt : ∀ p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1,
      ENNReal.ofReal ((gT μ h p - gO b τ p) ^ 2) ≤
        ENNReal.ofReal (1 + η) * ENNReal.ofReal ((gT μ h p - gM μ h v b p) ^ 2) +
          ENNReal.ofReal (1 + 1 / η) * ENNReal.ofReal ((gM μ h v b p - gO b τ p) ^ 2) := by
    intro p
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (1 + η) * (gT μ h p - gM μ h v b p) ^ 2 +
        (1 + 1 / η) * (gM μ h v b p - gO b τ p) ^ 2 - (gT μ h p - gO b τ p) ^ 2 =
        (η * (gT μ h p - gM μ h v b p) - (gM μ h v b p - gO b τ p)) ^ 2 / η := by
      field_simp
      ring
    have : 0 ≤ (η * (gT μ h p - gM μ h v b p) - (gM μ h v b p - gO b τ p)) ^ 2 / η := by
      positivity
    linarith
  calc ∫⁻ p, ENNReal.ofReal ((gT μ h p - gO b τ p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1))
      ≤ ∫⁻ p, (ENNReal.ofReal (1 + η) * ENNReal.ofReal ((gT μ h p - gM μ h v b p) ^ 2) +
          ENNReal.ofReal (1 + 1 / η) * ENNReal.ofReal ((gM μ h v b p - gO b τ p) ^ 2))
          ∂((gaussMat n m v).prod (mlpGauss n mF 1)) := lintegral_mono pt
    _ = ENNReal.ofReal (1 + η) * ∫⁻ p, ENNReal.ofReal ((gT μ h p - gM μ h v b p) ^ 2)
          ∂((gaussMat n m v).prod (mlpGauss n mF 1)) +
        ENNReal.ofReal (1 + 1 / η) * ∫⁻ p, ENNReal.ofReal ((gM μ h v b p - gO b τ p) ^ 2)
          ∂((gaussMat n m v).prod (mlpGauss n mF 1)) := by
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]
    _ ≤ ENNReal.ofReal (1 + η) * ENNReal.ofReal (L * (2 * v * R)) +
        ENNReal.ofReal (1 + 1 / η) * ENNReal.ofReal (2 * (v * Yl + S)) :=
        add_le_add (mul_le_mul' le_rfl (stageU μ hv hb hh hH hn hmF hL0 hL hR))
          (mul_le_mul' le_rfl (stageM μ hv hb hh hH hn hmF τ hYl hS))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end stage

end BstLean.Part149

open BstLean.Part149 in
#print axioms stageU
open BstLean.Part149 in
#print axioms stageM
open BstLean.Part149 in
#print axioms stageA
