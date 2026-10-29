import BstLean.Part149Stage
import BstLean.Part149Var

/-!
# Part 149: the stage of the Agent network, second route (constant scalars first)

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, items 1, 3 and 4. The first route (`Part149Stage`)
bounds the stand-in error with the frame constant of the unit residual directions (an operator
norm, Hilbert–Schmidt rate `n^{-1/2}`). Here the scalars are made constant FIRST (Lemma C, the
coupling through the same last matrix), so that the test function does not depend on the input;
then the variance bound `var_const` has the TWO-POINT quantity
`|E_u e(u)|² + E_{u,u'}⟨e(u), e(u')⟩²` in the place of the frame constant.

`(U, μ)`, `h`, `b ≠ 0`, `A₃` Gaussian with entry variance `v`, `F` a random network, `p = (A₃, F)`,
`e(u) = eDir b (h u)`, `σ₀ ≥ 0`, `τ = √v·σ₀`:

* `gT2 μ h b σ₀ p = E_u F(A₃(b + σ₀·e(u)))`.
* `stageM2`: `E (gT − gT2)² ≤ 2v·(E_u|b|²(λ(u) − 1)² + E_u(|r(u)| − σ₀)²)`.
* `standIn2_lint`, `stageU2`: `E (gT2 − gO)² ≤ Lt·2τ²` if
  `|E_u e|² + E_{u,u'}⟨e, e'⟩² + μ{e = 0}² ≤ Lt`.
* `stageA2`: both.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134

variable {n m mF : ℕ} {U : Type*} [MeasurableSpace U]

/-- `E_u F(A₃(b + σ₀·e(u)))`: the output of `A` with the scalars replaced by `1` and `σ₀`. -/
noncomputable def gT2 (μ : Measure U) (h : U → Fin m → ℝ) (b : Fin m → ℝ) (σ₀ : ℝ)
    (p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) : ℝ :=
  ∫ u, evF p.2 (p.1.mulVec (b + σ₀ • eDir b (h u))) ∂μ

lemma eDir_normSq_le (b h : Fin m → ℝ) : normSq (eDir b h) ≤ 1 := by
  rcases eDir_unit_or_zero b h with h1 | h1
  · exact h1.le
  · rw [h1]; simp [normSq]

lemma eDir_orth {b : Fin m → ℝ} (hb : b ≠ 0) (h : Fin m → ℝ) : ∑ j, eDir b h j * b j = 0 := by
  unfold eDir
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum, res_orth hb, mul_zero]

lemma normSq_add_smul {b e : Fin m → ℝ} (hbe : ∑ j, e j * b j = 0) (x y : ℝ) :
    normSq (x • b + y • e) = x ^ 2 * normSq b + y ^ 2 * normSq e := by
  have e1 : normSq (x • b + y • e) =
      x ^ 2 * normSq b + y ^ 2 * normSq e + 2 * x * y * ∑ j, e j * b j := by
    simp only [normSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, hbe]
  ring

/-- `h − (b + σ₀·e) = (λ − 1)·b + (|r| − σ₀)·e`. -/
lemma sub_centre_eq (b h : Fin m → ℝ) (σ₀ : ℝ) :
    h - (b + σ₀ • eDir b h) =
      (lam b h - 1) • b + (√(normSq (res b h)) - σ₀) • eDir b h := by
  have e1 := res_eq_smul_eDir b h
  ext j
  have e1j : res b h j = √(normSq (res b h)) * eDir b h j := by
    have := congrFun e1 j
    simpa using this
  have e2j : res b h j = h j - lam b h * b j := by simp [res]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination e1j - e2j

lemma lam_centre {b : Fin m → ℝ} (hb : b ≠ 0) (h : Fin m → ℝ) (σ₀ : ℝ) :
    lam b (b + σ₀ • eDir b h) = 1 := by
  have hb0 := normSq_ne_zero hb
  unfold lam
  have e1 : ∑ j, (b + σ₀ • eDir b h) j * b j = normSq b + σ₀ * ∑ j, eDir b h j * b j := by
    simp only [normSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, eDir_orth hb, mul_zero, add_zero, div_self hb0]

lemma res_centre {b : Fin m → ℝ} (hb : b ≠ 0) (h : Fin m → ℝ) (σ₀ : ℝ) :
    res b (b + σ₀ • eDir b h) = σ₀ • eDir b h := by
  unfold res
  rw [lam_centre hb, one_smul, add_sub_cancel_left]

lemma evF_abs_le (F : MlpParam n mF 1) {C : ℝ} (hC : ∀ y, evF F y ^ 2 ≤ C * (1 + normSq y))
    (y : Fin n → ℝ) : |evF F y| ≤ 1 + C * (1 + normSq y) := by
  have h1 := hC y
  nlinarith [sq_nonneg (|evF F y| - 1), abs_nonneg (evF F y), sq_abs (evF F y)]

section stage2

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- `F ∘ q` is integrable if `q` is bounded. -/
lemma integrable_evF_bdd (F : MlpParam n mF 1) {q : U → Fin n → ℝ} (hq : Measurable q) {K : ℝ}
    (hK : ∀ u, normSq (q u) ≤ K) : Integrable (fun u => evF F (q u)) μ := by
  obtain ⟨C, hC0, hC⟩ := evF_growth F
  refine Integrable.of_bound ((measurable_evF F).comp hq).aestronglyMeasurable (1 + C * (1 + K))
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs]
  refine (evF_abs_le F hC (q u)).trans ?_
  have := mul_le_mul_of_nonneg_left (hK u) hC0
  nlinarith

lemma measurable_gT2 {h : U → Fin m → ℝ} (hh : Measurable h) (b : Fin m → ℝ) (σ₀ : ℝ) :
    Measurable (gT2 (n := n) (mF := mF) μ h b σ₀) := by
  have hc : Measurable (fun q : (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × U =>
      b + σ₀ • eDir b (h q.2)) :=
    measurable_const.add (((measurable_eDir b).comp (hh.comp measurable_snd)).const_smul σ₀)
  have h1 : Measurable (fun q : (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) × U =>
      evF q.1.2 (q.1.1.mulVec (b + σ₀ • eDir b (h q.2)))) :=
    measurable_evF_comp (measurable_snd.comp measurable_fst)
      (measurable_mulVec_joint.comp ((measurable_fst.comp measurable_fst).prodMk hc))
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- **The price of constant scalars, with the same last matrix** (Lemma C):
`E_{A₃, F}(E_u F(A₃h(u)) − E_u F(A₃(b + σ₀e(u))))² ≤
2v·(E_u|b|²(λ(u) − 1)² + E_u(|r(u)| − σ₀)²)`. -/
theorem stageM2 {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {H : ℝ} (hH : ∀ u, normSq (h u) ≤ H) (hn : 1 ≤ n) (hmF : 1 ≤ mF)
    (σ₀ : ℝ) {Yl S : ℝ}
    (hYl : ∫ u, normSq b * (lam b (h u) - 1) ^ 2 ∂μ ≤ Yl)
    (hS : ∫ u, (√(normSq (res b (h u))) - σ₀) ^ 2 ∂μ ≤ S) :
    ∫⁻ p, ENNReal.ofReal ((gT μ h p - gT2 μ h b σ₀ p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1)) ≤ ENNReal.ofReal (2 * v * (Yl + S)) := by
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  obtain ⟨u0⟩ := μ.nonempty_of_neZero
  have hH0 : 0 ≤ H := (normSq_nonneg _).trans (hH u0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have mD : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gT μ h p - gT2 μ h b σ₀ p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_gT μ hh).sub (measurable_gT2 μ hh b σ₀)).pow_const 2)
  rw [lintegral_prod _ mD.aemeasurable]
  -- the vector `w(u) = h(u) − (b + σ₀ e(u))`
  set w : U → Fin m → ℝ := fun u => h u - (b + σ₀ • eDir b (h u)) with hw
  have mw : Measurable w :=
    hh.sub (measurable_const.add (((measurable_eDir b).comp hh).const_smul σ₀))
  have hlam2 : ∀ u, lam b (h u) ^ 2 ≤ H / normSq b := fun u =>
    (lam_sq_le hb _).trans (div_le_div_of_nonneg_right (hH u) hb0.le)
  have blam : BM (fun u => lam b (h u)) := bm_of_sq_le ((measurable_lam b).comp hh) hlam2
  have bN : BM (fun u => √(normSq (res b (h u)))) := by
    refine bm_of_sq_le (measurable_normSq.comp ((measurable_res b).comp hh)).sqrt (K := H)
      fun u => ?_
    rw [Real.sq_sqrt (normSq_nonneg _)]
    exact (normSq_res_le hb _).trans (hH u)
  set gg : U → ℝ := fun u =>
    normSq b * (lam b (h u) - 1) ^ 2 + (√(normSq (res b (h u))) - σ₀) ^ 2 with hgg
  have bgg : BM gg :=
    ((BM.const _).mul ((blam.sub (BM.const 1)).sq)).add ((bN.sub (BM.const σ₀)).sq)
  have hwle : ∀ u, normSq (w u) ≤ gg u := by
    intro u
    simp only [hw, hgg]
    rw [sub_centre_eq, normSq_add_smul (eDir_orth hb (h u))]
    have h1 := eDir_normSq_le b (h u)
    have h2 := normSq_nonneg (eDir b (h u))
    nlinarith [sq_nonneg (√(normSq (res b (h u))) - σ₀)]
  -- the joint integral of `|A₃ w(u)|²`
  set f : U × Matrix (Fin n) (Fin m) ℝ → ℝ := fun z => normSq (z.2.mulVec (w z.1)) with hf
  have mf : Measurable f :=
    measurable_normSq.comp (measurable_mulVec_joint.comp
      (measurable_snd.prodMk (mw.comp measurable_fst)))
  have bnw : BM (fun u => (n : ℝ) * (v * normSq (w u))) := by
    refine ⟨measurable_const.mul (measurable_const.mul (measurable_normSq.comp mw)),
      (n : ℝ) * (v * (bgg.bdd.choose)), fun u => ?_⟩
    have h1 := hwle u
    have h2 := (le_abs_self _).trans (bgg.bdd.choose_spec u)
    have h3 := normSq_nonneg (w u)
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans h2) hv) hnR.le
  obtain ⟨iF, eF⟩ := prod_step (μ := μ) (ν := gaussMat n m v) mf (fun _ => normSq_nonneg _)
    (fun u => (n : ℝ) * (v * normSq (w u)))
    (fun u => layer_lin_sq (m := n) (k := m) hv (w u)) (bnw.integrable μ)
  -- fixed `A₃`
  have key : ∀ M : Matrix (Fin n) (Fin m) ℝ,
      ∫⁻ F, ENNReal.ofReal ((gT μ h (M, F) - gT2 μ h b σ₀ (M, F)) ^ 2) ∂mlpGauss n mF 1 ≤
        ENNReal.ofReal (2 / (n : ℝ) * ∫ u, f (u, M) ∂μ) := by
    intro M
    set X : U → Fin n → ℝ := fun u => M.mulVec (h u) with hX
    set Y : U → Fin n → ℝ := fun u => M.mulVec (b + σ₀ • eDir b (h u)) with hY
    have mX : Measurable X := (measurable_mulVec_left M).comp hh
    have mY : Measurable Y := (measurable_mulVec_left M).comp
      (measurable_const.add (((measurable_eDir b).comp hh).const_smul σ₀))
    have eXY : ∀ u, normSq (X u - Y u) = f (u, M) := by
      intro u
      simp only [hX, hY, hf, hw]
      rw [← Matrix.mulVec_sub]
    have fr0 : 0 ≤ ∑ i, ∑ j, M i j ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hbdw : ∀ u, f (u, M) ≤ (∑ i, ∑ j, M i j ^ 2) * bgg.bdd.choose := by
      intro u
      refine (normSq_mulVec_le M (w u)).trans (mul_le_mul_of_nonneg_left ?_ fr0)
      exact (hwle u).trans ((le_abs_self _).trans (bgg.bdd.choose_spec u))
    have iXY : Integrable (fun u => normSq (X u - Y u)) μ := by
      simp_rw [eXY]
      refine Integrable.of_bound (mf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        ((∑ i, ∑ j, M i j ^ 2) * bgg.bdd.choose) (Filter.Eventually.of_forall fun u => ?_)
      rw [Real.norm_of_nonneg (normSq_nonneg _)]
      exact hbdw u
    obtain ⟨hint, hle⟩ := lemmaC149 μ (m := mF) hn hmF mX mY iXY
    have ediff : ∀ F : MlpParam n mF 1,
        ∫ u, (mlpEval F (X u) 0 - mlpEval F (Y u) 0) ∂μ =
          gT μ h (M, F) - gT2 μ h b σ₀ (M, F) := by
      intro F
      have iX : Integrable (fun u => evF F (X u)) μ :=
        integrable_evF_bdd μ F mX (K := (∑ i, ∑ j, M i j ^ 2) * H) fun u =>
          (normSq_mulVec_le M (h u)).trans (mul_le_mul_of_nonneg_left (hH u) fr0)
      have iY : Integrable (fun u => evF F (Y u)) μ := by
        refine integrable_evF_bdd μ F mY (K := (∑ i, ∑ j, M i j ^ 2) *
          (2 * normSq b + 2 * σ₀ ^ 2)) fun u => ?_
        refine (normSq_mulVec_le M _).trans (mul_le_mul_of_nonneg_left ?_ fr0)
        have h1 := normSq_add_le b (σ₀ • eDir b (h u))
        rw [normSq_smul] at h1
        have h2 := eDir_normSq_le b (h u)
        nlinarith [sq_nonneg σ₀]
      exact integral_sub iX iY
    simp_rw [← ediff]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp_rw [eXY] at hle
    exact hle
  have iM : Integrable (fun M : Matrix (Fin n) (Fin m) ℝ => ∫ u, f (u, M) ∂μ) (gaussMat n m v) :=
    iF.integral_prod_right
  calc ∫⁻ M, ∫⁻ F, ENNReal.ofReal ((gT μ h (M, F) - gT2 μ h b σ₀ (M, F)) ^ 2) ∂mlpGauss n mF 1
        ∂gaussMat n m v
      ≤ ∫⁻ M, ENNReal.ofReal (2 / (n : ℝ) * ∫ u, f (u, M) ∂μ) ∂gaussMat n m v :=
        lintegral_mono key
    _ = ENNReal.ofReal (∫ M, 2 / (n : ℝ) * ∫ u, f (u, M) ∂μ ∂gaussMat n m v) :=
        (ofReal_integral_eq_lintegral_ofReal (iM.const_mul _)
          (Filter.Eventually.of_forall fun M =>
            mul_nonneg (by positivity) (integral_nonneg fun _ => normSq_nonneg _))).symm
    _ ≤ ENNReal.ofReal (2 * v * (Yl + S)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, ← integral_prod_symm f iF, eF, integral_const_mul,
          integral_const_mul]
        have h1 : ∫ u, normSq (w u) ∂μ ≤ Yl + S := by
          calc ∫ u, normSq (w u) ∂μ ≤ ∫ u, gg u ∂μ :=
                integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => normSq_nonneg _)
                  (bgg.integrable μ) (Filter.Eventually.of_forall hwle)
            _ = ∫ u, normSq b * (lam b (h u) - 1) ^ 2 ∂μ +
                ∫ u, (√(normSq (res b (h u))) - σ₀) ^ 2 ∂μ :=
                integral_add (((BM.const _).mul ((blam.sub (BM.const 1)).sq)).integrable μ)
                  ((bN.sub (BM.const σ₀)).sq.integrable μ)
            _ ≤ Yl + S := add_le_add hYl hS
        have h2 : 2 / (n : ℝ) * ((n : ℝ) * (v * ∫ u, normSq (w u) ∂μ)) =
            2 * v * ∫ u, normSq (w u) ∂μ := by
          field_simp
        rw [h2]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The stand-in bound for an input-independent bounded test function, given `c = M b`. -/
lemma standIn2_fixed {v : ℝ} {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) (σ₀ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {Lt : ℝ}
    (hLt : ∑ j, (∫ u, eDir b (h u) j ∂μ) ^ 2 +
      ∫ p, (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ∂(μ.prod μ) +
      (μ.real {u | eDir b (h u) = 0}) ^ 2 ≤ Lt) (c : Fin n → ℝ) :
    ∫ M' : Matrix (Fin n) (Fin m) ℝ,
        ((∫ u, φ ((glue b c (M' * projPerp b)).mulVec (b + σ₀ • eDir b (h u))) ∂μ) -
          ∫ γ, φ (c + (√v * σ₀) • γ) ∂stdGauss (Fin n)) ^ 2 ∂gaussMat n m v ≤
      Lt * ∫ γ, (φ (c + (√v * σ₀) • γ) - φ c) ^ 2 ∂stdGauss (Fin n) := by
  set τ : ℝ := √v * σ₀ with hτ
  set e : U → Fin m → ℝ := fun u => eDir b (h u) with he
  have hem : Measurable e := (measurable_eDir b).comp hh
  have heu : ∀ u, normSq (e u) = 1 ∨ e u = 0 := fun u => eDir_unit_or_zero b (h u)
  have hM1 : 0 ≤ ∑ j, (∫ u, e u j ∂μ) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hΛ0 : 0 ≤ ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ) :=
    integral_nonneg fun _ => sq_nonneg _
  have hLt0 : 0 ≤ Lt := by
    have : 0 ≤ (μ.real {u | e u = 0}) ^ 2 := sq_nonneg _
    linarith
  -- the two means as bounded measurable functions
  have bI : BM (fun M : Matrix (Fin n) (Fin m) ℝ =>
      ∫ u, φ (M.mulVec (b + σ₀ • e u)) ∂μ) := by
    have hq : Measurable (fun q : Matrix (Fin n) (Fin m) ℝ × U => q.1.mulVec (b + σ₀ • e q.2)) :=
      measurable_mulVec_joint.comp (measurable_fst.prodMk
        (measurable_const.add ((hem.comp measurable_snd).const_smul σ₀)))
    exact BM.integral_right (H := fun q : Matrix (Fin n) (Fin m) ℝ × U =>
      φ (q.1.mulVec (b + σ₀ • e q.2))) (hφ.comp hq) μ
  have bO : BM (fun c : Fin n → ℝ => ∫ γ, φ (c + τ • γ) ∂stdGauss (Fin n)) :=
    BM.integral_right (H := fun q : (Fin n → ℝ) × (Fin n → ℝ) => φ (q.1 + τ • q.2))
      (hφ.comp (measurable_fst.add (measurable_snd.const_smul τ))) (stdGauss (Fin n))
  have bΘ : BM (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      ((∫ u, φ (p.2.mulVec (b + σ₀ • e u)) ∂μ) -
        ∫ γ, φ (p.1 + τ • γ) ∂stdGauss (Fin n)) ^ 2) :=
    ((bI.comp measurable_snd).sub (bO.comp measurable_fst)).sq
  have hm1 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  have hm2 : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  -- fixed `c`
  set g : (Fin n → ℝ) → ℝ := fun z => φ (c + τ • z) with hg
  have bg : BM g := hφ.comp (measurable_const.add (measurable_id.const_smul τ))
  have eI : ∀ ξ : Fin n × Fin m → ℝ,
      ∫ u, φ ((glue b c ((Matrix.of fun i j => Real.sqrt v * ξ (i, j) :
        Matrix (Fin n) (Fin m) ℝ) * projPerp b)).mulVec (b + σ₀ • e u)) ∂μ =
      ∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ := by
    intro ξ
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hg, he]
    rw [glue_res, lam_centre hb, res_centre hb, one_smul, Matrix.mulVec_smul]
    have e2 : (Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin n) (Fin m) ℝ) =
        Real.sqrt v • unflat ξ := by
      ext i j; simp [unflat]
    rw [e2, Matrix.smul_mulVec, ← rowMat_mulVec', smul_smul, mul_comm σ₀]
  have bJ := bm_field (n := n) hem bg
  have bJ1 : BM (fun ξ : Fin n × Fin m → ℝ => ∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) := by
    have h0 := bJ.comp (measurable_swap (α := Fin n × Fin m → ℝ) (β := U))
    simp only [Prod.fst_swap, Prod.snd_swap] at h0
    exact h0.integral_right μ
  have hvar := var_const (n := n) μ hem heu bg
  have hmean := mean_const (n := n) μ hem heu bg
  set I1 : ℝ := ∫ ξ, (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ^ 2 ∂stdGauss (Fin n × Fin m)
    with hI1
  set I0 : ℝ := ∫ ξ, (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ∂stdGauss (Fin n × Fin m)
    with hI0
  set Eg : ℝ := ∫ z, g z ∂stdGauss (Fin n) with hEg
  set Vg : ℝ := ∫ z, (g z - Eg) ^ 2 ∂stdGauss (Fin n) with hVg
  set V0 : ℝ := ∫ z, (g z - g 0) ^ 2 ∂stdGauss (Fin n) with hV0
  have hVV : Vg ≤ V0 := by
    have h1 := var_le_sq_sub (stdGauss (Fin n)) bg (g 0)
    rw [var_bm' (stdGauss (Fin n)) bg] at h1
    exact h1
  have hV00 : 0 ≤ V0 := integral_nonneg fun _ => sq_nonneg _
  have hVg0 : 0 ≤ Vg := integral_nonneg fun _ => sq_nonneg _
  have hEV : (g 0 - Eg) ^ 2 ≤ V0 := by
    have cs := BstLean.Part105.bm_cauchy_schwarz (stdGauss (Fin n)) (bg.sub (BM.const (g 0)))
      (BM.const 1)
    simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at cs
    rw [integral_sub (bg.integrable _) (integrable_const _)] at cs
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at cs
    have : (g 0 - Eg) ^ 2 = (Eg - g 0) ^ 2 := by ring
    rw [this]
    exact cs
  -- the measures of `{e ≠ 0}` and `{e = 0}`
  set μ0 : ℝ := μ.real {u | e u = 0} with hμ0
  have mE0 : MeasurableSet {u | e u = 0} := hem (measurableSet_singleton 0)
  have hμ1 : μ.real {u | e u ≠ 0} = 1 - μ0 := by
    have : {u | e u ≠ 0} = {u | e u = 0}ᶜ := rfl
    rw [this, measureReal_compl mE0, probReal_univ]
  have hμ00 : 0 ≤ μ0 := measureReal_nonneg
  rw [hμ1] at hmean
  -- the mean squared error
  have eL : ∫ M' : Matrix (Fin n) (Fin m) ℝ,
      ((∫ u, φ ((glue b c (M' * projPerp b)).mulVec (b + σ₀ • e u)) ∂μ) -
        ∫ γ, φ (c + τ • γ) ∂stdGauss (Fin n)) ^ 2 ∂gaussMat n m v =
      I1 - 2 * Eg * I0 + Eg ^ 2 := by
    have bq : BM (fun M' : Matrix (Fin n) (Fin m) ℝ =>
        ((∫ u, φ ((glue b c (M' * projPerp b)).mulVec (b + σ₀ • e u)) ∂μ) -
          ∫ γ, φ (c + τ • γ) ∂stdGauss (Fin n)) ^ 2) :=
      bΘ.comp (hm2.comp measurable_prodMk_left)
    rw [integral_gaussMat v bq.meas]
    simp_rw [eI]
    have e3 : (fun ξ : Fin n × Fin m → ℝ =>
        ((∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) - Eg) ^ 2) = fun ξ =>
        ((∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ^ 2 -
          2 * Eg * ∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) + Eg ^ 2 := by
      funext ξ; ring
    have e4 : (fun ξ : Fin n × Fin m → ℝ =>
        ((∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) -
          ∫ γ, φ (c + τ • γ) ∂stdGauss (Fin n)) ^ 2) = fun ξ =>
        ((∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) - Eg) ^ 2 := rfl
    rw [e4, e3, integral_add (f := fun ξ : Fin n × Fin m → ℝ =>
        (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ^ 2 -
          2 * Eg * ∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) (g := fun _ => Eg ^ 2)
        ((bJ1.sq.integrable _).sub ((bJ1.integrable _).const_mul _)) (integrable_const _),
      integral_sub (f := fun ξ : Fin n × Fin m → ℝ =>
        (∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ) ^ 2)
        (g := fun ξ => 2 * Eg * ∫ u, g ((rowMat n (e u)).mulVec ξ) ∂μ)
        (bJ1.sq.integrable _) ((bJ1.integrable _).const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hI1, hI0]
  rw [eL]
  have hsum : ∑ j, (∫ u, e u j ∂μ) ^ 2 + ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ) +
      μ0 ^ 2 ≤ Lt := hLt
  have h5 : I1 - I0 ^ 2 ≤ (∑ j, (∫ u, e u j ∂μ) ^ 2 +
      ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ)) * Vg := hvar
  have h6 : I0 - Eg = μ0 * (g 0 - Eg) := by rw [hmean]; ring
  have h7 : I1 - 2 * Eg * I0 + Eg ^ 2 = (I1 - I0 ^ 2) + (I0 - Eg) ^ 2 := by ring
  rw [h7, h6, mul_pow]
  have h8 : (∑ j, (∫ u, e u j ∂μ) ^ 2 +
      ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ)) * Vg ≤
      (∑ j, (∫ u, e u j ∂μ) ^ 2 +
        ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ)) * V0 :=
    mul_le_mul_of_nonneg_left hVV (by linarith)
  have h9 : μ0 ^ 2 * (g 0 - Eg) ^ 2 ≤ μ0 ^ 2 * V0 :=
    mul_le_mul_of_nonneg_left hEV (sq_nonneg _)
  have h10 : (∑ j, (∫ u, e u j ∂μ) ^ 2 +
      ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ) + μ0 ^ 2) * V0 ≤ Lt * V0 :=
    mul_le_mul_of_nonneg_right hsum hV00
  have h11 : Lt * V0 = Lt * ∫ γ, (φ (c + τ • γ) - φ c) ^ 2 ∂stdGauss (Fin n) := by
    rw [hV0]
    simp only [hg, smul_zero, add_zero]
  rw [← h11]
  nlinarith

/-- The stand-in bound for an input-independent bounded test function. -/
lemma standIn2_bdd {v : ℝ} {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) (σ₀ : ℝ) {φ ψ : (Fin n → ℝ) → ℝ} (hφ : BM φ)
    (hlip : ∀ y y', (φ y - φ y') ^ 2 ≤ (ψ y - ψ y') ^ 2) {Lt : ℝ}
    (hLt : ∑ j, (∫ u, eDir b (h u) j ∂μ) ^ 2 +
      ∫ p, (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ∂(μ.prod μ) +
      (μ.real {u | eDir b (h u) = 0}) ^ 2 ≤ Lt) :
    ∫⁻ M, ENNReal.ofReal (((∫ u, φ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ) -
        ∫ γ, φ (M.mulVec b + (√v * σ₀) • γ) ∂stdGauss (Fin n)) ^ 2) ∂gaussMat n m v ≤
      ENNReal.ofReal Lt * ∫⁻ c, (∫⁻ γ, ENNReal.ofReal
        ((ψ (c + (√v * σ₀) • γ) - ψ c) ^ 2) ∂stdGauss (Fin n)) ∂cDist n v b := by
  set τ : ℝ := √v * σ₀ with hτ
  set e : U → Fin m → ℝ := fun u => eDir b (h u) with he
  have hem : Measurable e := (measurable_eDir b).comp hh
  have heu : ∀ u, normSq (e u) = 1 ∨ e u = 0 := fun u => eDir_unit_or_zero b (h u)
  have hM1 : 0 ≤ ∑ j, (∫ u, e u j ∂μ) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hΛ0 : 0 ≤ ∫ p, (∑ j, e p.1 j * e p.2 j) ^ 2 ∂(μ.prod μ) :=
    integral_nonneg fun _ => sq_nonneg _
  have hLt0 : 0 ≤ Lt := by
    have : 0 ≤ (μ.real {u | e u = 0}) ^ 2 := sq_nonneg _
    linarith
  -- the two means as bounded measurable functions
  have bI : BM (fun M : Matrix (Fin n) (Fin m) ℝ =>
      ∫ u, φ (M.mulVec (b + σ₀ • e u)) ∂μ) := by
    have hq : Measurable (fun q : Matrix (Fin n) (Fin m) ℝ × U => q.1.mulVec (b + σ₀ • e q.2)) :=
      measurable_mulVec_joint.comp (measurable_fst.prodMk
        (measurable_const.add ((hem.comp measurable_snd).const_smul σ₀)))
    exact BM.integral_right (H := fun q : Matrix (Fin n) (Fin m) ℝ × U =>
      φ (q.1.mulVec (b + σ₀ • e q.2))) (hφ.comp hq) μ
  have bO : BM (fun c : Fin n → ℝ => ∫ γ, φ (c + τ • γ) ∂stdGauss (Fin n)) :=
    BM.integral_right (H := fun q : (Fin n → ℝ) × (Fin n → ℝ) => φ (q.1 + τ • q.2))
      (hφ.comp (measurable_fst.add (measurable_snd.const_smul τ))) (stdGauss (Fin n))
  have bΘ : BM (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      ((∫ u, φ (p.2.mulVec (b + σ₀ • e u)) ∂μ) -
        ∫ γ, φ (p.1 + τ • γ) ∂stdGauss (Fin n)) ^ 2) :=
    ((bI.comp measurable_snd).sub (bO.comp measurable_fst)).sq
  have hm1 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  have hm2 : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  -- the bounded right side
  have bD : BM (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (φ (q.1 + τ • q.2) - φ q.1) ^ 2) :=
    ((hφ.comp (measurable_fst.add (measurable_snd.const_smul τ))).sub
      (hφ.comp measurable_fst)).sq
  have bD1 := bD.integral_right (stdGauss (Fin n))
  have hreal : ∫ M, ((∫ u, φ (M.mulVec (b + σ₀ • e u)) ∂μ) -
      ∫ γ, φ (M.mulVec b + τ • γ) ∂stdGauss (Fin n)) ^ 2 ∂gaussMat n m v ≤
      Lt * ∫ c, (∫ γ, (φ (c + τ • γ) - φ c) ^ 2 ∂stdGauss (Fin n)) ∂cDist n v b := by
    have e1 : ∫ M, ((∫ u, φ (M.mulVec (b + σ₀ • e u)) ∂μ) -
        ∫ γ, φ (M.mulVec b + τ • γ) ∂stdGauss (Fin n)) ^ 2 ∂gaussMat n m v =
        ∫ p, ((∫ u, φ (p.2.mulVec (b + σ₀ • e u)) ∂μ) -
          ∫ γ, φ (p.1 + τ • γ) ∂stdGauss (Fin n)) ^ 2
          ∂(gaussMat n m v).map (fun M => (M.mulVec b, M)) :=
      (integral_map hm1.aemeasurable bΘ.meas.aestronglyMeasurable).symm
    rw [e1, s1_disint v hb, integral_map hm2.aemeasurable bΘ.meas.aestronglyMeasurable,
      integral_prod _ ((bΘ.comp hm2).integrable _), ← integral_const_mul]
    refine integral_mono ((bΘ.comp hm2).integral_right _ |>.integrable _)
      ((bD1.integrable _).const_mul _) fun c => ?_
    simp only []
    exact standIn2_fixed μ hb hh σ₀ hφ hLt c
  -- to `ℝ≥0∞`
  have bΘ' : BM (fun M : Matrix (Fin n) (Fin m) ℝ =>
      ((∫ u, φ (M.mulVec (b + σ₀ • e u)) ∂μ) -
        ∫ γ, φ (M.mulVec b + τ • γ) ∂stdGauss (Fin n)) ^ 2) :=
    (bI.sub (bO.comp (measurable_mulVec_right b))).sq
  rw [← ofReal_integral_eq_lintegral_ofReal (bΘ'.integrable _)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_mul hLt0]
  refine mul_le_mul' le_rfl ?_
  rw [ofReal_integral_eq_lintegral_ofReal (bD1.integrable _)
    (Filter.Eventually.of_forall fun c => integral_nonneg fun γ => sq_nonneg _)]
  refine lintegral_mono fun c => ?_
  rw [ofReal_integral_eq_lintegral_ofReal
    ((bD.comp (measurable_prodMk_left (x := c))).integrable _)
    (Filter.Eventually.of_forall fun γ => sq_nonneg _)]
  exact lintegral_mono fun γ => ENNReal.ofReal_le_ofReal (hlip _ _)

/-- **The stand-in bound for an input-independent unbounded test function** (`ψ(y)² ≤
C(1 + |y|²)`): `E_M (E_u ψ(M(b + σ₀e(u))) − E_γ ψ(M b + τγ))² ≤ Lt·E_c E_γ (ψ(c + τγ) − ψ(c))²`,
`τ = √v·σ₀`, in `ℝ≥0∞`. -/
theorem standIn2_lint {v : ℝ} {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) (σ₀ : ℝ) {ψ : (Fin n → ℝ) → ℝ} (hψ : Measurable ψ) {C : ℝ}
    (hC : ∀ y, ψ y ^ 2 ≤ C * (1 + normSq y)) {Lt : ℝ}
    (hLt : ∑ j, (∫ u, eDir b (h u) j ∂μ) ^ 2 +
      ∫ p, (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ∂(μ.prod μ) +
      (μ.real {u | eDir b (h u) = 0}) ^ 2 ≤ Lt) :
    ∫⁻ M, ENNReal.ofReal (((∫ u, ψ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ) -
        ∫ γ, ψ (M.mulVec b + (√v * σ₀) • γ) ∂stdGauss (Fin n)) ^ 2) ∂gaussMat n m v ≤
      ENNReal.ofReal Lt * ∫⁻ c, (∫⁻ γ, ENNReal.ofReal
        ((ψ (c + (√v * σ₀) • γ) - ψ c) ^ 2) ∂stdGauss (Fin n)) ∂cDist n v b := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    have h1 : (0 : ℝ) ≤ ψ 0 ^ 2 := sq_nonneg _
    have h2 : normSq (0 : Fin n → ℝ) = 0 := by simp [normSq]
    rw [h2] at this
    nlinarith
  have habs : ∀ y : Fin n → ℝ, |ψ y| ≤ 1 + C * (1 + normSq y) := by
    intro y
    have h1 := hC y
    nlinarith [sq_nonneg (|ψ y| - 1), abs_nonneg (ψ y), sq_abs (ψ y)]
  set τ : ℝ := √v * σ₀ with hτ
  set f : ℕ → Matrix (Fin n) (Fin m) ℝ → ℝ≥0∞ := fun K M =>
    ENNReal.ofReal (((∫ u, clampF (K : ℝ) ψ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ) -
      ∫ γ, clampF (K : ℝ) ψ (M.mulVec b + τ • γ) ∂stdGauss (Fin n)) ^ 2) with hf
  have bK : ∀ K : ℕ, BM (clampF (K : ℝ) ψ) := fun K => bm_clampF (Nat.cast_nonneg K) hψ
  have hem : Measurable (fun u => eDir b (h u)) := (measurable_eDir b).comp hh
  have mf : ∀ K, Measurable (f K) := by
    intro K
    have hq : Measurable (fun q : Matrix (Fin n) (Fin m) ℝ × U =>
        q.1.mulVec (b + σ₀ • eDir b (h q.2))) :=
      measurable_mulVec_joint.comp (measurable_fst.prodMk
        (measurable_const.add ((hem.comp measurable_snd).const_smul σ₀)))
    have bI : BM (fun M : Matrix (Fin n) (Fin m) ℝ =>
        ∫ u, clampF (K : ℝ) ψ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ) :=
      BM.integral_right (H := fun q : Matrix (Fin n) (Fin m) ℝ × U =>
        clampF (K : ℝ) ψ (q.1.mulVec (b + σ₀ • eDir b (h q.2)))) ((bK K).comp hq) μ
    have bO : BM (fun c : Fin n → ℝ => ∫ γ, clampF (K : ℝ) ψ (c + τ • γ) ∂stdGauss (Fin n)) :=
      BM.integral_right (H := fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        clampF (K : ℝ) ψ (q.1 + τ • q.2))
        ((bK K).comp (measurable_fst.add (measurable_snd.const_smul τ))) (stdGauss (Fin n))
    exact ENNReal.measurable_ofReal.comp
      ((bI.sub (bO.comp (measurable_mulVec_right b))).sq).meas
  have step1 : ∀ K : ℕ, ∫⁻ M, f K M ∂gaussMat n m v ≤
      ENNReal.ofReal Lt * ∫⁻ c, (∫⁻ γ, ENNReal.ofReal
        ((ψ (c + τ • γ) - ψ c) ^ 2) ∂stdGauss (Fin n)) ∂cDist n v b := fun K =>
    standIn2_bdd μ hb hh σ₀ (bK K) (clampF_lip _ _) hLt
  have step2 : ∀ M : Matrix (Fin n) (Fin m) ℝ, Tendsto (fun K => f K M) atTop
      (𝓝 (ENNReal.ofReal (((∫ u, ψ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ) -
        ∫ γ, ψ (M.mulVec b + τ • γ) ∂stdGauss (Fin n)) ^ 2))) := by
    intro M
    have fr0 : 0 ≤ ∑ i, ∑ j, M i j ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have t1 : Tendsto (fun K : ℕ => ∫ u, clampF (K : ℝ) ψ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ)
        atTop (𝓝 (∫ u, ψ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ)) := by
      refine tendsto_clamp_integral μ hψ ((measurable_mulVec_left M).comp
        (measurable_const.add (hem.const_smul σ₀)))
        (G := fun _ => 1 + C * (1 + (∑ i, ∑ j, M i j ^ 2) * (2 * normSq b + 2 * σ₀ ^ 2)))
        (integrable_const _) fun u => ?_
      refine (habs _).trans ?_
      have h1 := normSq_mulVec_le M (b + σ₀ • eDir b (h u))
      have h2 := normSq_add_le b (σ₀ • eDir b (h u))
      rw [normSq_smul] at h2
      have h3 := eDir_normSq_le b (h u)
      have h4 : normSq (b + σ₀ • eDir b (h u)) ≤ 2 * normSq b + 2 * σ₀ ^ 2 := by
        nlinarith [sq_nonneg σ₀]
      have h5 := mul_le_mul_of_nonneg_left h4 fr0
      have h6 : C * (1 + normSq (M.mulVec (b + σ₀ • eDir b (h u)))) ≤
          C * (1 + (∑ i, ∑ j, M i j ^ 2) * (2 * normSq b + 2 * σ₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0
      linarith
    have t2 : Tendsto (fun K : ℕ => ∫ γ, clampF (K : ℝ) ψ (M.mulVec b + τ • γ) ∂stdGauss (Fin n))
        atTop (𝓝 (∫ γ, ψ (M.mulVec b + τ • γ) ∂stdGauss (Fin n))) := by
      have iG : Integrable (fun γ : Fin n → ℝ =>
          (1 + C * (1 + 2 * normSq (M.mulVec b))) + (C * (2 * τ ^ 2)) * normSq γ)
          (stdGauss (Fin n)) :=
        (integrable_const _).add ((stdGauss_normSq n).1.const_mul _)
      refine tendsto_clamp_integral (stdGauss (Fin n)) hψ
        (measurable_const.add (measurable_id.const_smul τ)) iG fun γ => ?_
      refine (habs _).trans ?_
      have h2 := normSq_add_le (M.mulVec b) (τ • γ)
      rw [normSq_smul] at h2
      have h6 : C * (1 + normSq (M.mulVec b + τ • γ)) ≤
          C * (1 + (2 * normSq (M.mulVec b) + 2 * (τ ^ 2 * normSq γ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0
      linarith
    have t3 := ((t1.sub t2).pow 2)
    exact (ENNReal.continuous_ofReal.tendsto _).comp t3
  calc ∫⁻ M, ENNReal.ofReal (((∫ u, ψ (M.mulVec (b + σ₀ • eDir b (h u))) ∂μ) -
        ∫ γ, ψ (M.mulVec b + τ • γ) ∂stdGauss (Fin n)) ^ 2) ∂gaussMat n m v
      = ∫⁻ M, liminf (fun K => f K M) atTop ∂gaussMat n m v :=
        lintegral_congr fun M => ((step2 M).liminf_eq).symm
    _ ≤ liminf (fun K => ∫⁻ M, f K M ∂gaussMat n m v) atTop := lintegral_liminf_le mf
    _ ≤ _ := liminf_le_of_frequently_le' (Filter.Frequently.of_forall step1)

/-- **The stand-in error of `A` with constant scalars, for the test function `F`**:
`E_{A₃, F}(E_u F(A₃(b + σ₀e(u))) − E_γ F(A₃b + τγ))² ≤ Lt·2τ²`, `τ = √v·σ₀`. -/
theorem stageU2 {v : ℝ} {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) (hn : 1 ≤ n) (hmF : 1 ≤ mF) (σ₀ : ℝ) {Lt : ℝ} (hLt0 : 0 ≤ Lt)
    (hLt : ∑ j, (∫ u, eDir b (h u) j ∂μ) ^ 2 +
      ∫ p, (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ∂(μ.prod μ) +
      (μ.real {u | eDir b (h u) = 0}) ^ 2 ≤ Lt) :
    ∫⁻ p, ENNReal.ofReal ((gT2 μ h b σ₀ p - gO b (√v * σ₀) p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal (Lt * (2 * (√v * σ₀) ^ 2)) := by
  set τ : ℝ := √v * σ₀ with hτ
  have mTO : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gT2 μ h b σ₀ p - gO b τ p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_gT2 μ hh b σ₀).sub (measurable_gO b τ)).pow_const 2)
  rw [lintegral_prod_symm' _ mTO]
  set Q3 : (MlpParam n mF 1 × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((evF x.1.1 (x.1.2 + τ • x.2) - evF x.1.1 x.1.2) ^ 2) with hQ3
  have mf1 : Measurable (fun x : (MlpParam n mF 1 × (Fin n → ℝ)) × (Fin n → ℝ) => x.1.1) :=
    measurable_fst.comp measurable_fst
  have mc1 : Measurable (fun x : (MlpParam n mF 1 × (Fin n → ℝ)) × (Fin n → ℝ) => x.1.2) :=
    measurable_snd.comp measurable_fst
  have mQ3 : Measurable Q3 :=
    ENNReal.measurable_ofReal.comp (((measurable_evF_comp mf1
      (mc1.add (measurable_snd.const_smul τ))).sub (measurable_evF_comp mf1 mc1)).pow_const 2)
  set g1 : MlpParam n mF 1 × (Fin n → ℝ) → ℝ≥0∞ := fun x =>
    ∫⁻ γ, Q3 (x, γ) ∂stdGauss (Fin n) with hg1
  have mg1 : Measurable g1 := mQ3.lintegral_prod_right'
  have step : ∀ F : MlpParam n mF 1,
      ∫⁻ M, ENNReal.ofReal ((gT2 μ h b σ₀ (M, F) - gO b τ (M, F)) ^ 2) ∂gaussMat n m v ≤
        ENNReal.ofReal Lt * ∫⁻ c, g1 (F, c) ∂cDist n v b := by
    intro F
    obtain ⟨C, _, hC⟩ := evF_growth F
    exact standIn2_lint μ hb hh σ₀ (measurable_evF F) hC hLt
  have inner : ∀ c : Fin n → ℝ,
      ∫⁻ F, g1 (F, c) ∂mlpGauss n mF 1 ≤ ENNReal.ofReal (2 * τ ^ 2) := by
    intro c
    obtain ⟨hi, hle⟩ := lemmaC_gauss (m := mF) hn hmF c τ
    have mf : Measurable (fun p : MlpParam n mF 1 × (Fin n → ℝ) =>
        ENNReal.ofReal ((mlpEval p.1 (c + τ • p.2) 0 - mlpEval p.1 c 0) ^ 2)) := by
      have : (fun p : MlpParam n mF 1 × (Fin n → ℝ) =>
          ENNReal.ofReal ((mlpEval p.1 (c + τ • p.2) 0 - mlpEval p.1 c 0) ^ 2)) =
          fun p => Q3 ((p.1, c), p.2) := rfl
      rw [this]
      exact mQ3.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    have e1 : ∫⁻ F, g1 (F, c) ∂mlpGauss n mF 1 =
        ∫⁻ p, ENNReal.ofReal ((mlpEval p.1 (c + τ • p.2) 0 - mlpEval p.1 c 0) ^ 2)
          ∂((mlpGauss n mF 1).prod (stdGauss (Fin n))) := by
      rw [lintegral_prod _ mf.aemeasurable]
      rfl
    rw [e1, ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  calc ∫⁻ F, ∫⁻ M, ENNReal.ofReal ((gT2 μ h b σ₀ (M, F) - gO b τ (M, F)) ^ 2) ∂gaussMat n m v
        ∂mlpGauss n mF 1
      ≤ ∫⁻ F, ENNReal.ofReal Lt * ∫⁻ c, g1 (F, c) ∂cDist n v b ∂mlpGauss n mF 1 :=
        lintegral_mono step
    _ = ENNReal.ofReal Lt * ∫⁻ F, ∫⁻ c, g1 (F, c) ∂cDist n v b ∂mlpGauss n mF 1 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal Lt * ∫⁻ c, ∫⁻ F, g1 (F, c) ∂mlpGauss n mF 1 ∂cDist n v b := by
        rw [lintegral_lintegral_swap (f := fun F c => g1 (F, c)) mg1.aemeasurable]
    _ ≤ ENNReal.ofReal Lt * ∫⁻ _c, ENNReal.ofReal (2 * τ ^ 2) ∂cDist n v b :=
        mul_le_mul' le_rfl (lintegral_mono inner)
    _ = ENNReal.ofReal (Lt * (2 * τ ^ 2)) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_mul hLt0]

/-- **The error of the stage of `A`, second route**:
`E_{A₃, F}(E_u F(A₃h(u)) − E_γ F(A₃b + τγ))² ≤ (1 + η)·2v·(Yl + S) + (1 + 1/η)·Lt·2τ²`,
`τ = √v·σ₀`. -/
theorem stageA2 {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {H : ℝ} (hH : ∀ u, normSq (h u) ≤ H) (hn : 1 ≤ n) (hmF : 1 ≤ mF)
    (σ₀ : ℝ) {Yl S : ℝ}
    (hYl : ∫ u, normSq b * (lam b (h u) - 1) ^ 2 ∂μ ≤ Yl)
    (hS : ∫ u, (√(normSq (res b (h u))) - σ₀) ^ 2 ∂μ ≤ S) {Lt : ℝ} (hLt0 : 0 ≤ Lt)
    (hLt : ∑ j, (∫ u, eDir b (h u) j ∂μ) ^ 2 +
      ∫ p, (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ∂(μ.prod μ) +
      (μ.real {u | eDir b (h u) = 0}) ^ 2 ≤ Lt) {η : ℝ} (hη : 0 < η) :
    ∫⁻ p, ENNReal.ofReal ((gT μ h p - gO b (√v * σ₀) p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal ((1 + η) * (2 * v * (Yl + S)) +
        (1 + 1 / η) * (Lt * (2 * (√v * σ₀) ^ 2))) := by
  have hYl0 : 0 ≤ Yl :=
    (integral_nonneg fun _ => mul_nonneg (normSq_nonneg _) (sq_nonneg _)).trans hYl
  have hS0 : 0 ≤ S := (integral_nonneg fun _ => sq_nonneg _).trans hS
  have m1 : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gT μ h p - gT2 μ h b σ₀ p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_gT μ hh).sub (measurable_gT2 μ hh b σ₀)).pow_const 2)
  have m2 : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gT2 μ h b σ₀ p - gO b (√v * σ₀) p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_gT2 μ hh b σ₀).sub (measurable_gO b _)).pow_const 2)
  have pt : ∀ p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1,
      ENNReal.ofReal ((gT μ h p - gO b (√v * σ₀) p) ^ 2) ≤
        ENNReal.ofReal (1 + η) * ENNReal.ofReal ((gT μ h p - gT2 μ h b σ₀ p) ^ 2) +
          ENNReal.ofReal (1 + 1 / η) *
            ENNReal.ofReal ((gT2 μ h b σ₀ p - gO b (√v * σ₀) p) ^ 2) := by
    intro p
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (1 + η) * (gT μ h p - gT2 μ h b σ₀ p) ^ 2 +
        (1 + 1 / η) * (gT2 μ h b σ₀ p - gO b (√v * σ₀) p) ^ 2 -
        (gT μ h p - gO b (√v * σ₀) p) ^ 2 =
        (η * (gT μ h p - gT2 μ h b σ₀ p) - (gT2 μ h b σ₀ p - gO b (√v * σ₀) p)) ^ 2 / η := by
      field_simp
      ring
    have : 0 ≤ (η * (gT μ h p - gT2 μ h b σ₀ p) -
        (gT2 μ h b σ₀ p - gO b (√v * σ₀) p)) ^ 2 / η := by positivity
    linarith
  refine (lintegral_mono pt).trans ?_
  rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1, lintegral_const_mul _ m2]
  refine (add_le_add (mul_le_mul' le_rfl (stageM2 μ hv hb hh hH hn hmF σ₀ hYl hS))
    (mul_le_mul' le_rfl (stageU2 μ hb hh hn hmF σ₀ hLt0 hLt))).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end stage2

end BstLean.Part149

open BstLean.Part149 in
#print axioms stageM2
open BstLean.Part149 in
#print axioms standIn2_lint
open BstLean.Part149 in
#print axioms stageU2
open BstLean.Part149 in
#print axioms stageA2
