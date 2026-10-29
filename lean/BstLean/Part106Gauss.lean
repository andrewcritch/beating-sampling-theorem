import BstLean.Part105Final
import BstLean.Part56PropD_Polar

/-!
# Part 106: two facts about the standard Gaussian

* `gauss_scale_dom`: for `0 < a ≤ b` and a bounded measurable `f ≥ 0` on `ℝⁿ`:
  `E f(a g) ≤ (b/a)^n · E f(b g)` (the density of `N(0, a² I)` with respect to `N(0, b² I)` is at
  most `(b/a)^n`).
* `chiSq_cheb`: the Chebyshev inequality for `Σ ξ_i²`, `ξ` standard Gaussian in `ℝ^ι`:
  `P(|Σ ξ_i² − D| ≥ t) ≤ 2D/t²`, `D` the number of coordinates.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-! ## Domination under scaling -/

lemma pdf_scale_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    gaussianPDF 0 (NNReal.mk (a ^ 2) (sq_nonneg a)) x ≤
      ENNReal.ofReal (b / a) * gaussianPDF 0 (NNReal.mk (b ^ 2) (sq_nonneg b)) x := by
  have hb : 0 < b := ha.trans_le hab
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal, NNReal.coe_mk, sub_zero]
  have h2 : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have ea : Real.sqrt (2 * Real.pi * a ^ 2) = Real.sqrt (2 * Real.pi) * a := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
  have eb : Real.sqrt (2 * Real.pi * b ^ 2) = Real.sqrt (2 * Real.pi) * b := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb.le]
  rw [ea, eb]
  have he : Real.exp (-x ^ 2 / (2 * a ^ 2)) ≤ Real.exp (-x ^ 2 / (2 * b ^ 2)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (sq_nonneg x) (by positivity)
    have := pow_le_pow_left₀ ha.le hab 2
    linarith
  have e3 : b / a * ((Real.sqrt (2 * Real.pi) * b)⁻¹ * Real.exp (-x ^ 2 / (2 * b ^ 2))) =
      (Real.sqrt (2 * Real.pi) * a)⁻¹ * Real.exp (-x ^ 2 / (2 * b ^ 2)) := by
    field_simp
  rw [e3]
  exact mul_le_mul_of_nonneg_left he (by positivity)

lemma one_dim_dom {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G (a * x) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal (b / a) * ∫⁻ x, G (b * x) ∂gaussianReal 0 1 := by
  have hb : 0 < b := ha.trans_le hab
  have key : ∀ c : ℝ, 0 < c → ∫⁻ x, G (c * x) ∂gaussianReal 0 1 =
      ∫⁻ x, gaussianPDF 0 (NNReal.mk (c ^ 2) (sq_nonneg c)) x * G x := by
    intro c hc
    have hm : Measurable (fun x : ℝ => c * x) := measurable_const_mul c
    rw [← lintegral_map hG hm, gaussianReal_map_const_mul]
    have hv : NNReal.mk (c ^ 2) (sq_nonneg c) ≠ 0 := by
      intro h
      have := congrArg NNReal.toReal h
      simp only [NNReal.coe_mk, NNReal.coe_zero] at this
      exact (pow_pos hc 2).ne' this
    simp only [mul_one, mul_zero]
    rw [gaussianReal_of_var_ne_zero _ hv,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hG]
    rfl
  rw [key a ha, key b hb, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  calc gaussianPDF 0 (NNReal.mk (a ^ 2) (sq_nonneg a)) x * G x
      ≤ (ENNReal.ofReal (b / a) * gaussianPDF 0 (NNReal.mk (b ^ 2) (sq_nonneg b)) x) * G x :=
        mul_le_mul_left (pdf_scale_le ha hab x) _
    _ = _ := by rw [mul_assoc]

lemma cons_smul {k : ℕ} (c x : ℝ) (z : Fin k → ℝ) :
    c • (Fin.cons x z : Fin (k + 1) → ℝ) = Fin.cons (c * x) (c • z) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The domination for nonnegative measurable functions. -/
theorem gauss_scale_dom_lintegral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ (n : ℕ) (F : (Fin n → ℝ) → ℝ≥0∞), Measurable F →
      ∫⁻ z, F (a • z) ∂stdGauss (Fin n) ≤
        ENNReal.ofReal (b / a) ^ n * ∫⁻ z, F (b • z) ∂stdGauss (Fin n) := by
  intro n
  induction n with
  | zero =>
    intro F _
    have : ∀ z : Fin 0 → ℝ, a • z = b • z := fun z => Subsingleton.elim _ _
    simp [this]
  | succ k ih =>
    intro F hF
    have hcons : Measurable (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) := by
      refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]; exact measurable_fst
      · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd
    have hsm : ∀ c : ℝ, Measurable (fun z : Fin (k + 1) → ℝ => c • z) :=
      fun c => measurable_const_smul c
    have hsm' : ∀ c : ℝ, Measurable (fun z : Fin k → ℝ => c • z) :=
      fun c => measurable_const_smul c
    -- `H y = ∫ F (cons y (b z))`
    set H : ℝ → ℝ≥0∞ := fun y => ∫⁻ z, F (Fin.cons y (b • z)) ∂stdGauss (Fin k) with hH
    have hHm : Measurable H := by
      have : Measurable (fun p : ℝ × (Fin k → ℝ) => F (Fin.cons p.1 (b • p.2))) :=
        hF.comp (hcons.comp (measurable_fst.prodMk ((hsm' b).comp measurable_snd)))
      exact this.lintegral_prod_right'
    rw [BstLean.Part56.stdGauss_cons_lintegral k (fun g => F (a • g)) (hF.comp (hsm a)),
      BstLean.Part56.stdGauss_cons_lintegral k (fun g => F (b • g)) (hF.comp (hsm b))]
    simp only [cons_smul]
    calc ∫⁻ x, ∫⁻ z, F (Fin.cons (a * x) (a • z)) ∂stdGauss (Fin k) ∂gaussianReal 0 1
        ≤ ∫⁻ x, ENNReal.ofReal (b / a) ^ k * H (a * x) ∂gaussianReal 0 1 := by
          refine lintegral_mono fun x => ?_
          exact ih (fun z => F (Fin.cons (a * x) z))
            (hF.comp (hcons.comp (measurable_const.prodMk measurable_id)))
      _ = ENNReal.ofReal (b / a) ^ k * ∫⁻ x, H (a * x) ∂gaussianReal 0 1 :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      _ ≤ ENNReal.ofReal (b / a) ^ k *
            (ENNReal.ofReal (b / a) * ∫⁻ x, H (b * x) ∂gaussianReal 0 1) := by
          gcongr
          exact one_dim_dom ha hab H hHm
      _ = ENNReal.ofReal (b / a) ^ (k + 1) * ∫⁻ x, H (b * x) ∂gaussianReal 0 1 := by
          rw [pow_succ, mul_assoc]

/-- **Domination of a Gaussian by a wider Gaussian**: `E f(a g) ≤ (b/a)^n · E f(b g)` for
`0 < a ≤ b` and bounded measurable `f ≥ 0`. -/
theorem gauss_scale_dom {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : BM f) (hf0 : ∀ z, 0 ≤ f z)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ z, f (a • z) ∂stdGauss (Fin n) ≤ (b / a) ^ n * ∫ z, f (b • z) ∂stdGauss (Fin n) := by
  have hb : 0 < b := ha.trans_le hab
  have hsm : ∀ c : ℝ, Measurable (fun z : Fin n → ℝ => c • z) := fun c => measurable_const_smul c
  have hF : Measurable (fun z => ENNReal.ofReal (f z)) := hf.meas.ennreal_ofReal
  have h := gauss_scale_dom_lintegral ha hab n (fun z => ENNReal.ofReal (f z)) hF
  have e : ∀ c : ℝ, ∫ z, f (c • z) ∂stdGauss (Fin n) =
      (∫⁻ z, ENNReal.ofReal (f (c • z)) ∂stdGauss (Fin n)).toReal := fun c =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hf0 _)
      (hf.meas.comp (hsm c)).aestronglyMeasurable
  have fin : ∀ c : ℝ, ∫⁻ z, ENNReal.ofReal (f (c • z)) ∂stdGauss (Fin n) ≠ ⊤ := fun c =>
    ((hf.comp (hsm c)).integrable _).lintegral_lt_top.ne
  rw [e a, e b]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (fin b)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h2
  exact h2

/-! ## The chi-square -/

lemma memLp_sq_gauss : MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
  have h4 : MemLp (id : ℝ → ℝ) 4 (gaussianReal 0 1) := memLp_id_gaussianReal 4
  have hi : Integrable (fun x : ℝ => ‖id x‖ ^ 4) (gaussianReal 0 1) := by
    have := h4.integrable_norm_pow (p := 4) (by norm_num)
    simpa using this
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [id, Real.norm_eq_abs]
  rw [← pow_mul, ← abs_pow, abs_of_nonneg (by positivity)]

lemma var_sq_gauss : Var[fun x : ℝ => x ^ 2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub memLp_sq_gauss]
  have h4 : ∫ x : ℝ, ((fun x : ℝ => x ^ 2) ^ 2) x ∂gaussianReal 0 1 = 3 := by
    have := BstLean.Part29.gaussMom_eq 4
    simp only [Pi.pow_apply, ← pow_mul]
    rw [this]
    norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
  have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [BstLean.Part29.gaussMom_eq 2]
    norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
  rw [h4, h2]
  norm_num

/-- **Chebyshev for the chi-square**: `P(|Σ ξ_i² − D| ≥ t) ≤ 2D/t²`. -/
theorem chiSq_cheb (ι : Type*) [Fintype ι] {t : ℝ} (ht : 0 < t) :
    (stdGauss ι).real {ξ | t ≤ |∑ i, ξ i ^ 2 - (Fintype.card ι : ℝ)|} ≤
      2 * (Fintype.card ι : ℝ) / t ^ 2 := by
  classical
  set X : ι → (ι → ℝ) → ℝ := fun i ξ => ξ i ^ 2 with hX
  have hmp : ∀ i, MeasurePreserving (Function.eval i : (ι → ℝ) → ℝ) (stdGauss ι)
      (gaussianReal 0 1) := fun i => by
    unfold stdGauss
    exact measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  have hmem : ∀ i, MemLp (X i) 2 (stdGauss ι) := fun i =>
    memLp_sq_gauss.comp_measurePreserving (hmp i)
  have hind : iIndepFun X (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun _ (x : ℝ) => x ^ 2)
      (fun _ => by fun_prop)
  have hvar_i : ∀ i, Var[X i; stdGauss ι] = 2 := fun i => by
    have : X i = (fun x : ℝ => x ^ 2) ∘ (Function.eval i) := rfl
    rw [this, ← variance_map (by fun_prop) (hmp i).measurable.aemeasurable, (hmp i).map_eq]
    exact var_sq_gauss
  have hmean_i : ∀ i, ∫ ξ, X i ξ ∂stdGauss ι = 1 := fun i => by
    have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
      rw [BstLean.Part29.gaussMom_eq 2]
      norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
    have h := integral_map (μ := stdGauss ι) (φ := Function.eval i)
      (hmp i).measurable.aemeasurable (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [(hmp i).map_eq, h2] at h
    exact h.symm
  have hsum : (fun ξ : ι → ℝ => ∑ i, ξ i ^ 2) = ∑ i, X i := by
    funext ξ; simp [hX]
  have hvar : Var[fun ξ : ι → ℝ => ∑ i, ξ i ^ 2; stdGauss ι] = 2 * (Fintype.card ι : ℝ) := by
    rw [hsum, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp [hvar_i, mul_comm]
  have hmean : ∫ ξ : ι → ℝ, ∑ i, ξ i ^ 2 ∂stdGauss ι = (Fintype.card ι : ℝ) := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    rw [Finset.sum_congr rfl (fun i _ => hmean_i i)]
    simp
  have hm2 : MemLp (fun ξ : ι → ℝ => ∑ i, ξ i ^ 2) 2 (stdGauss ι) := by
    rw [hsum]
    exact memLp_finsetSum' _ (fun i _ => hmem i)
  have h := meas_ge_le_variance_div_sq hm2 ht
  rw [hmean, hvar] at h
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

end BstLean.Part106

#print axioms BstLean.Part106.gauss_scale_dom
#print axioms BstLean.Part106.chiSq_cheb
