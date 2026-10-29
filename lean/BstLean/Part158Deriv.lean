import BstLean.Part158Theta
import BstLean.Part158Coord
import BstLean.Part158Ibp

/-!
# Part 158 (file `Deriv`): the derivative formula of the interpolation

Do not use `sorry`, `native_decide` or `axiom`.

**`psiDeriv`** (`PsiDerivStmt`): for a regular family `F` (`Fam`) and a finite measure `μ`,
`d/dθ Psi(cos θ, sin θ) = sin θ cos θ · E_ξ [e^T · Σ_k (L⁻¹ ∫ w_k² dμ − V_k²)]`.

Proof: `Fam.Psi_theta` gives the derivative as `E_ξ [e^T · L⁻¹ ∫ (∂_θ U / U) dμ]`; Fubini; for every
`x` and every coordinate `k`, Gaussian integration by parts along the rotated pair (`ibp_star`)
with `W = e^T / U_x` (`Fam.W_coord`); Fubini.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)

variable {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι]
  {F : X → (ι → ℝ) → ℝ} {dF : X → (ι → ℝ) → ι → ℝ} {a b C : ℝ}

lemma integrable_of_bddD {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {g : α → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) : Integrable g ν :=
  Integrable.of_bound hg.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)

/-- `W_x = e^T / U_x`. -/
noncomputable def Wx (μ : Measure X) (L : ℝ) (F : X → (ι → ℝ) → ℝ) (c s : ℝ) (x : X)
    (ξ : ι → ℝ) : ℝ :=
  exp (T μ L F c s ξ) / U F c s x ξ

/-- The bound of `|T|`. -/
noncomputable def Mb (μ : Measure X) (L a b : ℝ) : ℝ :=
  |L⁻¹| * ((|log a| + |log b|) * μ.real Set.univ)

/-- The bound of `|Vv|`. -/
noncomputable def Vb (μ : Measure X) (L a C : ℝ) : ℝ := |L⁻¹| * (C / a * μ.real Set.univ)

lemma Fam.expT_le (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L c s : ℝ)
    (ξ : ι → ℝ) : exp (T μ L F c s ξ) ≤ exp (Mb μ L a b) :=
  exp_le_exp.mpr ((le_abs_self _).trans (h.T_le μ L c s ξ))

lemma Fam.Wx_le (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L c s : ℝ) (x : X)
    (ξ : ι → ℝ) : |Wx μ L F c s x ξ| ≤ exp (Mb μ L a b) / a := by
  unfold Wx
  rw [abs_div, abs_of_pos (exp_pos _), abs_of_pos (h.U_pos c s x ξ)]
  exact div_le_div₀ (exp_pos _).le (h.expT_le μ L c s ξ) h.ha (h.U_lo c s x ξ)

lemma Fam.measurable_Wx (h : Fam F dF a b C) (μ : Measure X) [SFinite μ] (L c s : ℝ) :
    Measurable (fun p : X × (ι → ℝ) => Wx μ L F c s p.1 p.2) :=
  ((h.measurable_T μ L c s).exp.comp measurable_snd).div (h.measurable_U c s)

/-- One term of `dthU`. -/
noncomputable def Jk (dF : X → (ι → ℝ) → ι → ℝ) (c s : ℝ) (x : X) (k : ι) (ξ : ι → ℝ) : ℝ :=
  ∫ ξ', dF x (c • ξ + s • ξ') k * (-s * ξ k + c * ξ' k) ∂stdGauss ι

/-- `E |ξ_k|`. -/
noncomputable def Ek (k : ι) : ℝ := ∫ ξ' : ι → ℝ, |ξ' k| ∂stdGauss ι

lemma Fam.term_le (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X) (k : ι)
    (ξ ξ' : ι → ℝ) :
    |dF x (c • ξ + s • ξ') k * (-s * ξ k + c * ξ' k)| ≤ C * (|ξ k| + |ξ' k|) := by
  rw [abs_mul]
  have h1 := h.hC x (c • ξ + s • ξ') k
  have hC : 0 ≤ C := (abs_nonneg _).trans h1
  have h2 : |-s * ξ k + c * ξ' k| ≤ |ξ k| + |ξ' k| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg]
    have := mul_le_mul_of_nonneg_right hs (abs_nonneg (ξ k))
    have := mul_le_mul_of_nonneg_right hc (abs_nonneg (ξ' k))
    linarith
  exact mul_le_mul h1 h2 (abs_nonneg _) hC

lemma Fam.measurable_term2 (h : Fam F dF a b C) (c s : ℝ) (x : X) (k : ι) :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) =>
      dF x (c • p.1 + s • p.2) k * (-s * p.1 k + c * p.2 k)) := by
  refine ((h.mdFx x k).comp (measurable_pt c s)).mul ?_
  exact (((measurable_pi_apply k).comp measurable_fst).const_mul _).add
    (((measurable_pi_apply k).comp measurable_snd).const_mul _)

lemma Fam.integrable_term (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X)
    (k : ι) (ξ : ι → ℝ) :
    Integrable (fun ξ' => dF x (c • ξ + s • ξ') k * (-s * ξ k + c * ξ' k)) (stdGauss ι) :=
  Integrable.mono'
    (((integrable_const |ξ k|).add (BstLean.Part152.integrable_coord k).abs).const_mul C)
    ((h.measurable_term2 c s x k).comp measurable_prodMk_left).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ' => by
      rw [Real.norm_eq_abs]; exact h.term_le hc hs x k ξ ξ')

lemma Fam.dthU_eq_sum (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X)
    (ξ : ι → ℝ) : dthU dF c s x ξ = ∑ k, Jk dF c s x k ξ := by
  unfold dthU dthI Jk
  exact integral_finsetSum _ fun k _ => h.integrable_term hc hs x k ξ

lemma Fam.measurable_Jk (h : Fam F dF a b C) (c s : ℝ) (x : X) (k : ι) :
    Measurable (Jk dF c s x k) :=
  ((h.measurable_term2 c s x k).stronglyMeasurable.integral_prod_right'
    (ν := stdGauss ι)).measurable

lemma Fam.Jk_le (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X) (k : ι)
    (ξ : ι → ℝ) : |Jk dF c s x k ξ| ≤ C * (|ξ k| + Ek k) := by
  unfold Jk
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (h.integrable_term hc hs x k ξ).abs
    (((integrable_const |ξ k|).add (BstLean.Part152.integrable_coord k).abs).const_mul C)
    (fun ξ' => h.term_le hc hs x k ξ ξ')
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) (BstLean.Part152.integrable_coord k).abs]
  simp [Ek]

/-- The integrand after the integration by parts. -/
noncomputable def Hk (μ : Measure X) (L : ℝ) (F : X → (ι → ℝ) → ℝ) (dF : X → (ι → ℝ) → ι → ℝ)
    (c s : ℝ) (k : ι) (x : X) (ξ : ι → ℝ) : ℝ :=
  exp (T μ L F c s ξ) * ((Vv μ L F dF c s ξ k - wv F dF c s x ξ k) * wv F dF c s x ξ k)

lemma Fam.measurable_Hk (h : Fam F dF a b C) (μ : Measure X) [SFinite μ] (L c s : ℝ) (k : ι) :
    Measurable (fun p : X × (ι → ℝ) => Hk μ L F dF c s k p.1 p.2) :=
  ((h.measurable_T μ L c s).exp.comp measurable_snd).mul
    ((((h.measurable_Vv μ L c s k).comp measurable_snd).sub (h.measurable_wv c s k)).mul
      (h.measurable_wv c s k))

lemma Fam.Hk_le (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L c s : ℝ) (k : ι)
    (x : X) (ξ : ι → ℝ) :
    |Hk μ L F dF c s k x ξ| ≤ exp (Mb μ L a b) * ((Vb μ L a C + C / a) * (C / a)) := by
  unfold Hk
  rw [abs_mul, abs_mul, abs_of_pos (exp_pos _)]
  have h1 := h.wv_le c s x ξ k
  have h2 := h.Vv_le μ L c s ξ k
  have h3 : |Vv μ L F dF c s ξ k - wv F dF c s x ξ k| ≤ Vb μ L a C + C / a :=
    (abs_sub _ _).trans (add_le_add h2 h1)
  exact mul_le_mul (h.expT_le μ L c s ξ)
    (mul_le_mul h3 h1 (abs_nonneg _) ((abs_nonneg _).trans h3))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (exp_pos _).le

lemma abs_le_one_of_sq_add {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : |c| ≤ 1 ∧ |s| ≤ 1 := by
  constructor
  · rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg s]
  · rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg c]

/-- The integration by parts for one `x`. -/
lemma Fam.step_x (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ]
    (L : ℝ) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (x : X) :
    ∫ ξ, Wx μ L F c s x ξ * dthU dF c s x ξ ∂stdGauss ι =
      ∑ k, -s * c * ∫ ξ, Hk μ L F dF c s k x ξ ∂stdGauss ι := by
  classical
  obtain ⟨hc, hs⟩ := abs_le_one_of_sq_add hcs
  have mW : Measurable (Wx μ L F c s x) := (h.measurable_Wx μ L c s).comp measurable_prodMk_left
  simp_rw [h.dthU_eq_sum hc hs, Finset.mul_sum]
  rw [integral_finsetSum]
  swap
  · intro k _
    refine Integrable.bdd_mul (c := exp (Mb μ L a b) / a) ?_ mW.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]; exact h.Wx_le μ L c s x ξ)
    refine Integrable.mono'
      (((BstLean.Part152.integrable_coord k).abs.add (integrable_const (Ek k))).const_mul C)
      (h.measurable_Jk c s x k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]; exact h.Jk_le hc hs x k ξ)
  refine Finset.sum_congr rfl fun k _ => ?_
  have hC : 0 ≤ C := (abs_nonneg _).trans (h.hC x (0 : ι → ℝ) k)
  have hW0 : 0 ≤ exp (Mb μ L a b) / a := div_nonneg (exp_pos _).le h.ha.le
  have hVb : 0 ≤ Vb μ L a C := (abs_nonneg _).trans (h.Vv_le μ L c s (0 : ι → ℝ) k)
  have hCa : 0 ≤ C / a := div_nonneg hC h.ha.le
  set C' := exp (Mb μ L a b) / a + exp (Mb μ L a b) / a * (Vb μ L a C + C / a) + C with hC'
  have hprod : 0 ≤ exp (Mb μ L a b) / a * (Vb μ L a C + C / a) :=
    mul_nonneg hW0 (add_nonneg hVb hCa)
  have key := ibp_star k hcs (W := Wx μ L F c s x)
    (dW := fun ξ => Wx μ L F c s x ξ * (c * Vv μ L F dF c s ξ k - c * wv F dF c s x ξ k))
    (A := fun ξ => dF x ξ k) (C := C') mW
    (mW.mul (((h.measurable_Vv μ L c s k).const_mul c).sub
      (((h.measurable_wv c s k).comp measurable_prodMk_left).const_mul c)))
    (h.mdFx x k) (fun ξ => h.W_coord μ L c s x k ξ)
    (fun ξ => (h.Wx_le μ L c s x ξ).trans (by linarith))
    (fun ξ => by
      rw [abs_mul]
      have h1 := h.Wx_le μ L c s x ξ
      have h2 : |c * Vv μ L F dF c s ξ k - c * wv F dF c s x ξ k| ≤ Vb μ L a C + C / a := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          calc |c| * |Vv μ L F dF c s ξ k| ≤ 1 * Vb μ L a C :=
                mul_le_mul hc (h.Vv_le μ L c s ξ k) (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        · rw [abs_mul]
          calc |c| * |wv F dF c s x ξ k| ≤ 1 * (C / a) :=
                mul_le_mul hc (h.wv_le c s x ξ k) (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
      have := mul_le_mul h1 h2 (abs_nonneg _) hW0
      linarith)
    (fun ξ => (h.hC x ξ k).trans (by linarith))
  unfold Jk
  rw [key, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hU0 : U F c s x ξ ≠ 0 := (h.U_pos c s x ξ).ne'
  change Wx μ L F c s x ξ * (c * Vv μ L F dF c s ξ k - c * wv F dF c s x ξ k) *
      Abar dF c s x ξ k = c * Hk μ L F dF c s k x ξ
  unfold Hk Wx wv
  field_simp

/-- `∫ w_k² dμ`. -/
noncomputable def Qk (μ : Measure X) (F : X → (ι → ℝ) → ℝ) (dF : X → (ι → ℝ) → ι → ℝ)
    (c s : ℝ) (k : ι) (ξ : ι → ℝ) : ℝ :=
  ∫ x, wv F dF c s x ξ k ^ 2 ∂μ

lemma Fam.measurable_Qk (h : Fam F dF a b C) (μ : Measure X) [SFinite μ] (c s : ℝ) (k : ι) :
    Measurable (Qk μ F dF c s k) := by
  have h1 : Measurable (fun p : (ι → ℝ) × X => wv F dF c s p.2 p.1 k ^ 2) :=
    ((h.measurable_wv c s k).comp measurable_swap).pow_const 2
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma Fam.wv_sq_le (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) (k : ι) :
    |wv F dF c s x ξ k ^ 2| ≤ (C / a) ^ 2 := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (h.wv_le c s x ξ k) 2

lemma Fam.integrable_wv_sq (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (c s : ℝ)
    (ξ : ι → ℝ) (k : ι) : Integrable (fun x => wv F dF c s x ξ k ^ 2) μ :=
  integrable_of_bddD (((h.measurable_wv c s k).comp measurable_prodMk_right).pow_const 2)
    (fun x => h.wv_sq_le c s x ξ k)

lemma Fam.Qk_le (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (c s : ℝ) (k : ι)
    (ξ : ι → ℝ) : |Qk μ F dF c s k ξ| ≤ (C / a) ^ 2 * μ.real Set.univ := by
  unfold Qk
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (h.integrable_wv_sq μ c s ξ k).abs (integrable_const ((C / a) ^ 2))
    (fun x => h.wv_sq_le c s x ξ k)
  simpa [mul_comm] using this

/-- **The identity for the derivative.** -/
theorem Fam.deriv_identity (h : Fam F dF a b C) (μ : Measure X)
    [IsFiniteMeasure μ] (L : ℝ) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    ∫ ξ, exp (T μ L F c s ξ) * dthT μ L F dF c s ξ ∂stdGauss ι =
      s * c * ∫ ξ, exp (T μ L F c s ξ) *
        ∑ k, (L⁻¹ * ∫ x, wv F dF c s x ξ k ^ 2 ∂μ - Vv μ L F dF c s ξ k ^ 2) ∂stdGauss ι := by
  obtain ⟨hc, hs⟩ := abs_le_one_of_sq_add hcs
  have e1 : ∀ ξ, exp (T μ L F c s ξ) * dthT μ L F dF c s ξ =
      L⁻¹ * ∫ x, Wx μ L F c s x ξ * dthU dF c s x ξ ∂μ := by
    intro ξ
    unfold dthT Wx
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- the first exchange of the integrals
  have hint1 : Integrable (Function.uncurry fun (ξ : ι → ℝ) (x : X) =>
      Wx μ L F c s x ξ * dthU dF c s x ξ) ((stdGauss ι).prod μ) := by
    have hb : Integrable (fun p : (ι → ℝ) × X =>
        exp (Mb μ L a b) / a * (|C| * (N1 p.1 + EN1 ι))) ((stdGauss ι).prod μ) :=
      Integrable.const_mul (Integrable.const_mul
        (Integrable.comp_fst (f := fun ξ : ι → ℝ => N1 ξ + EN1 ι)
          (integrable_N1.add (integrable_const _)) μ) _) _
    refine Integrable.mono' hb
      (((h.measurable_Wx μ L c s).mul (h.measurable_dthU c s)).comp
        measurable_swap).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    change |Wx μ L F c s p.2 p.1 * dthU dF c s p.2 p.1| ≤ _
    rw [abs_mul]
    have h1 := h.Wx_le μ L c s p.2 p.1
    have h2 := h.dthU_le hc hs p.2 p.1
    have h3 : C * (N1 p.1 + EN1 ι) ≤ |C| * (N1 p.1 + EN1 ι) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (add_nonneg (N1_nonneg _) EN1_nonneg)
    exact mul_le_mul h1 (h2.trans h3) (abs_nonneg _) (div_nonneg (exp_pos _).le h.ha.le)
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap hint1]
  simp_rw [h.step_x μ L hcs]
  -- the terms
  have mHx : ∀ k, Measurable (fun x => ∫ ξ, Hk μ L F dF c s k x ξ ∂stdGauss ι) := fun k =>
    ((h.measurable_Hk μ L c s k).stronglyMeasurable.integral_prod_right'
      (ν := stdGauss ι)).measurable
  have bHx : ∀ k x, |∫ ξ, Hk μ L F dF c s k x ξ ∂stdGauss ι| ≤
      exp (Mb μ L a b) * ((Vb μ L a C + C / a) * (C / a)) := by
    intro k x
    refine (abs_integral_le_integral_abs).trans ?_
    have := integral_mono
      (integrable_of_bddD ((h.measurable_Hk μ L c s k).comp measurable_prodMk_left)
        (fun ξ => h.Hk_le μ L c s k x ξ)).abs
      (integrable_const (μ := stdGauss ι) (exp (Mb μ L a b) * ((Vb μ L a C + C / a) * (C / a))))
      (fun ξ => h.Hk_le μ L c s k x ξ)
    simpa using this
  rw [integral_finsetSum _ fun k _ => (integrable_of_bddD (mHx k) (bHx k)).const_mul _]
  simp_rw [integral_const_mul]
  -- the second exchange
  have e2 : ∀ k, L⁻¹ * ∫ x, ∫ ξ, Hk μ L F dF c s k x ξ ∂stdGauss ι ∂μ =
      ∫ ξ, exp (T μ L F c s ξ) * (Vv μ L F dF c s ξ k ^ 2 - L⁻¹ * Qk μ F dF c s k ξ)
        ∂stdGauss ι := by
    intro k
    have hint2 : Integrable (Function.uncurry fun (x : X) (ξ : ι → ℝ) =>
        Hk μ L F dF c s k x ξ) (μ.prod (stdGauss ι)) :=
      integrable_of_bddD (h.measurable_Hk μ L c s k) (fun p => h.Hk_le μ L c s k p.1 p.2)
    rw [integral_integral_swap hint2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    change L⁻¹ * ∫ x, Hk μ L F dF c s k x ξ ∂μ = _
    have e3 : ∀ x, Hk μ L F dF c s k x ξ = exp (T μ L F c s ξ) *
        (Vv μ L F dF c s ξ k * wv F dF c s x ξ k - wv F dF c s x ξ k ^ 2) := by
      intro x; unfold Hk; ring
    simp_rw [e3]
    rw [integral_const_mul, integral_sub ((h.integrable_wv μ c s ξ k).const_mul _)
      (h.integrable_wv_sq μ c s ξ k), integral_const_mul]
    have e4 : L⁻¹ * ∫ x, wv F dF c s x ξ k ∂μ = Vv μ L F dF c s ξ k := rfl
    unfold Qk
    rw [← e4]
    ring
  have e5 : L⁻¹ * ∑ k, -s * c * ∫ x, ∫ ξ, Hk μ L F dF c s k x ξ ∂stdGauss ι ∂μ =
      ∑ k, -s * c * (L⁻¹ * ∫ x, ∫ ξ, Hk μ L F dF c s k x ξ ∂stdGauss ι ∂μ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e5]
  simp_rw [e2, Finset.mul_sum]
  have iR : ∀ k, Integrable (fun ξ => exp (T μ L F c s ξ) *
      (L⁻¹ * Qk μ F dF c s k ξ - Vv μ L F dF c s ξ k ^ 2)) (stdGauss ι) := by
    intro k
    refine integrable_of_bddD (B := exp (Mb μ L a b) *
      (|L⁻¹| * ((C / a) ^ 2 * μ.real Set.univ) + Vb μ L a C ^ 2))
      ((h.measurable_T μ L c s).exp.mul (((h.measurable_Qk μ c s k).const_mul _).sub
        ((h.measurable_Vv μ L c s k).pow_const 2))) (fun ξ => ?_)
    rw [abs_mul, abs_of_pos (exp_pos _)]
    have h1 : |L⁻¹ * Qk μ F dF c s k ξ| ≤ |L⁻¹| * ((C / a) ^ 2 * μ.real Set.univ) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h.Qk_le μ c s k ξ) (abs_nonneg _)
    have h2 : |Vv μ L F dF c s ξ k ^ 2| ≤ Vb μ L a C ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (h.Vv_le μ L c s ξ k) 2
    have h3 := (abs_sub (L⁻¹ * Qk μ F dF c s k ξ) (Vv μ L F dF c s ξ k ^ 2)).trans
      (add_le_add h1 h2)
    exact mul_le_mul (h.expT_le μ L c s ξ) h3 (abs_nonneg _) (exp_pos _).le
  change _ = s * c * ∫ ξ, ∑ k, exp (T μ L F c s ξ) *
    (L⁻¹ * Qk μ F dF c s k ξ - Vv μ L F dF c s ξ k ^ 2) ∂stdGauss ι
  rw [integral_finsetSum _ fun k _ => iR k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e6 : ∫ ξ, exp (T μ L F c s ξ) * (Vv μ L F dF c s ξ k ^ 2 - L⁻¹ * Qk μ F dF c s k ξ)
      ∂stdGauss ι = -∫ ξ, exp (T μ L F c s ξ) *
        (L⁻¹ * Qk μ F dF c s k ξ - Vv μ L F dF c s ξ k ^ 2) ∂stdGauss ι := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    ring
  rw [e6]
  ring

/-- **The derivative formula of the interpolation** (`PsiDerivStmt`). -/
theorem psiDeriv : PsiDerivStmt := by
  intro X _ μ _ ι _ F dF a b C h L θ
  classical
  have h1 := h.Psi_theta μ L θ
  have hcs : cos θ ^ 2 + sin θ ^ 2 = 1 := cos_sq_add_sin_sq θ
  rw [h.deriv_identity μ L hcs] at h1
  exact h1

end BstLean.Part158

open BstLean.Part158 in
#print axioms psiDeriv
