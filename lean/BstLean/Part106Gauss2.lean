import BstLean.Part106Gauss

/-!
# Part 106: two more facts about the standard Gaussian

* `gauss_shift_dom`: for `0 < a < b`, centres `μ₁`, `μ₂` and a bounded measurable `f ≥ 0` on `ℝⁿ`:
  `E f(μ₁ + a g) ≤ (b/a)^n · exp(|μ₁ − μ₂|²/(2(b² − a²))) · E f(μ₂ + b g)`.
* `chiSq_cheb_sub`: the Chebyshev inequality for `Σ_j ξ_{e j}²` over an injective sub-family of
  the coordinates.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-! ## Domination with a shift -/

lemma shift_quad {a b : ℝ} (ha : 0 < a) (hab : a < b) (p Δ : ℝ) :
    (p + Δ) ^ 2 / b ^ 2 ≤ p ^ 2 / a ^ 2 + Δ ^ 2 / (b ^ 2 - a ^ 2) := by
  have hb : 0 < b := ha.trans hab
  have hd : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have e : p ^ 2 / a ^ 2 + Δ ^ 2 / (b ^ 2 - a ^ 2) - (p + Δ) ^ 2 / b ^ 2 =
      (p * (b ^ 2 - a ^ 2) - Δ * a ^ 2) ^ 2 / (a ^ 2 * b ^ 2 * (b ^ 2 - a ^ 2)) := by
    field_simp
    ring
  have : 0 ≤ (p * (b ^ 2 - a ^ 2) - Δ * a ^ 2) ^ 2 / (a ^ 2 * b ^ 2 * (b ^ 2 - a ^ 2)) := by
    positivity
  linarith

lemma pdf_shift_le {a b : ℝ} (ha : 0 < a) (hab : a < b) (c₁ c₂ x : ℝ) :
    gaussianPDF c₁ (NNReal.mk (a ^ 2) (sq_nonneg a)) x ≤
      ENNReal.ofReal (b / a * Real.exp ((c₁ - c₂) ^ 2 / (2 * (b ^ 2 - a ^ 2)))) *
        gaussianPDF c₂ (NNReal.mk (b ^ 2) (sq_nonneg b)) x := by
  have hb : 0 < b := ha.trans hab
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal, NNReal.coe_mk]
  have h2 : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have ea : Real.sqrt (2 * Real.pi * a ^ 2) = Real.sqrt (2 * Real.pi) * a := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
  have eb : Real.sqrt (2 * Real.pi * b ^ 2) = Real.sqrt (2 * Real.pi) * b := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb.le]
  rw [ea, eb]
  have he : Real.exp (-(x - c₁) ^ 2 / (2 * a ^ 2)) ≤
      Real.exp ((c₁ - c₂) ^ 2 / (2 * (b ^ 2 - a ^ 2))) *
        Real.exp (-(x - c₂) ^ 2 / (2 * b ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := shift_quad ha hab (x - c₁) (c₁ - c₂)
    have e1 : x - c₁ + (c₁ - c₂) = x - c₂ := by ring
    rw [e1] at h
    have e2 : -(x - c₁) ^ 2 / (2 * a ^ 2) = -((x - c₁) ^ 2 / a ^ 2) / 2 := by ring
    have e3 : (c₁ - c₂) ^ 2 / (2 * (b ^ 2 - a ^ 2)) = (c₁ - c₂) ^ 2 / (b ^ 2 - a ^ 2) / 2 := by
      rw [div_div, mul_comm]
    have e4 : -(x - c₂) ^ 2 / (2 * b ^ 2) = -((x - c₂) ^ 2 / b ^ 2) / 2 := by ring
    rw [e2, e3, e4]
    linarith
  have e3 : b / a * Real.exp ((c₁ - c₂) ^ 2 / (2 * (b ^ 2 - a ^ 2))) *
        ((Real.sqrt (2 * Real.pi) * b)⁻¹ * Real.exp (-(x - c₂) ^ 2 / (2 * b ^ 2))) =
      (Real.sqrt (2 * Real.pi) * a)⁻¹ * (Real.exp ((c₁ - c₂) ^ 2 / (2 * (b ^ 2 - a ^ 2))) *
        Real.exp (-(x - c₂) ^ 2 / (2 * b ^ 2))) := by
    field_simp
  rw [e3]
  exact mul_le_mul_of_nonneg_left he (by positivity)

lemma one_dim_shift_dom {a b : ℝ} (ha : 0 < a) (hab : a < b) (c₁ c₂ : ℝ) (G : ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ x, G (c₁ + a * x) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal (b / a * Real.exp ((c₁ - c₂) ^ 2 / (2 * (b ^ 2 - a ^ 2)))) *
        ∫⁻ x, G (c₂ + b * x) ∂gaussianReal 0 1 := by
  have hb : 0 < b := ha.trans hab
  have key : ∀ c s : ℝ, 0 < s → ∫⁻ x, G (c + s * x) ∂gaussianReal 0 1 =
      ∫⁻ x, gaussianPDF c (NNReal.mk (s ^ 2) (sq_nonneg s)) x * G x := by
    intro c s hs
    have hm : Measurable (fun x : ℝ => s * x) := measurable_const_mul s
    have hG' : Measurable (fun y : ℝ => G (c + y)) := hG.comp (measurable_const_add c)
    rw [← lintegral_map hG' hm, gaussianReal_map_const_mul,
      ← lintegral_map hG (measurable_const_add c), gaussianReal_map_const_add]
    have hv : NNReal.mk (s ^ 2) (sq_nonneg s) ≠ 0 := by
      intro h
      have := congrArg NNReal.toReal h
      simp only [NNReal.coe_mk, NNReal.coe_zero] at this
      exact (pow_pos hs 2).ne' this
    simp only [mul_one, mul_zero, zero_add]
    rw [gaussianReal_of_var_ne_zero _ hv,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hG]
    rfl
  rw [key c₁ a ha, key c₂ b hb, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  calc gaussianPDF c₁ (NNReal.mk (a ^ 2) (sq_nonneg a)) x * G x
      ≤ (ENNReal.ofReal (b / a * Real.exp ((c₁ - c₂) ^ 2 / (2 * (b ^ 2 - a ^ 2)))) *
          gaussianPDF c₂ (NNReal.mk (b ^ 2) (sq_nonneg b)) x) * G x :=
        mul_le_mul_left (pdf_shift_le ha hab c₁ c₂ x) _
    _ = _ := by rw [mul_assoc]

lemma cons_shift {k : ℕ} (c x : ℝ) (μ : Fin (k + 1) → ℝ) (z : Fin k → ℝ) :
    μ + c • (Fin.cons x z : Fin (k + 1) → ℝ) =
      Fin.cons (μ 0 + c * x) (Fin.tail μ + c • z) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

/-- The domination with a shift, for nonnegative measurable functions. -/
theorem gauss_shift_dom_lintegral {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ (n : ℕ) (F : (Fin n → ℝ) → ℝ≥0∞), Measurable F → ∀ μ₁ μ₂ : Fin n → ℝ,
      ∫⁻ z, F (μ₁ + a • z) ∂stdGauss (Fin n) ≤
        ENNReal.ofReal ((b / a) ^ n *
            Real.exp ((∑ i, (μ₁ i - μ₂ i) ^ 2) / (2 * (b ^ 2 - a ^ 2)))) *
          ∫⁻ z, F (μ₂ + b • z) ∂stdGauss (Fin n) := by
  have hb : 0 < b := ha.trans hab
  intro n
  induction n with
  | zero =>
    intro F _ μ₁ μ₂
    have : ∀ z : Fin 0 → ℝ, μ₁ + a • z = μ₂ + b • z := fun z => Subsingleton.elim _ _
    rw [show (fun z : Fin 0 → ℝ => F (μ₁ + a • z)) = fun z => F (μ₂ + b • z) from
      funext fun z => by rw [this z]]
    simp
  | succ k ih =>
    intro F hF μ₁ μ₂
    have hcons : Measurable (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) := by
      refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]; exact measurable_fst
      · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd
    have hsm : ∀ (ν : Fin (k + 1) → ℝ) (c : ℝ), Measurable (fun z : Fin (k + 1) → ℝ => ν + c • z) :=
      fun ν c => (measurable_const_smul c).const_add ν
    have hsm' : ∀ (ν : Fin k → ℝ) (c : ℝ), Measurable (fun z : Fin k → ℝ => ν + c • z) :=
      fun ν c => (measurable_const_smul c).const_add ν
    set H : ℝ → ℝ≥0∞ := fun y => ∫⁻ z, F (Fin.cons y (Fin.tail μ₂ + b • z)) ∂stdGauss (Fin k)
      with hH
    have hHm : Measurable H := by
      have : Measurable (fun p : ℝ × (Fin k → ℝ) => F (Fin.cons p.1 (Fin.tail μ₂ + b • p.2))) :=
        hF.comp (hcons.comp (measurable_fst.prodMk ((hsm' _ b).comp measurable_snd)))
      exact this.lintegral_prod_right'
    set Ck : ℝ := (b / a) ^ k *
      Real.exp ((∑ i, (Fin.tail μ₁ i - Fin.tail μ₂ i) ^ 2) / (2 * (b ^ 2 - a ^ 2))) with hCk
    set C1 : ℝ := b / a * Real.exp ((μ₁ 0 - μ₂ 0) ^ 2 / (2 * (b ^ 2 - a ^ 2))) with hC1
    have hCk0 : 0 ≤ Ck := by positivity
    have hC10 : 0 ≤ C1 := by positivity
    have hconst : (b / a) ^ (k + 1) *
        Real.exp ((∑ i, (μ₁ i - μ₂ i) ^ 2) / (2 * (b ^ 2 - a ^ 2))) = Ck * C1 := by
      rw [hCk, hC1, Fin.sum_univ_succ, add_div, Real.exp_add]
      simp only [Fin.tail]
      ring
    rw [BstLean.Part56.stdGauss_cons_lintegral k (fun g => F (μ₁ + a • g)) (hF.comp (hsm μ₁ a)),
      BstLean.Part56.stdGauss_cons_lintegral k (fun g => F (μ₂ + b • g)) (hF.comp (hsm μ₂ b))]
    simp only [cons_shift]
    calc ∫⁻ x, ∫⁻ z, F (Fin.cons (μ₁ 0 + a * x) (Fin.tail μ₁ + a • z)) ∂stdGauss (Fin k)
          ∂gaussianReal 0 1
        ≤ ∫⁻ x, ENNReal.ofReal Ck * H (μ₁ 0 + a * x) ∂gaussianReal 0 1 := by
          refine lintegral_mono fun x => ?_
          exact ih (fun z => F (Fin.cons (μ₁ 0 + a * x) z))
            (hF.comp (hcons.comp (measurable_const.prodMk measurable_id)))
            (Fin.tail μ₁) (Fin.tail μ₂)
      _ = ENNReal.ofReal Ck * ∫⁻ x, H (μ₁ 0 + a * x) ∂gaussianReal 0 1 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Ck *
            (ENNReal.ofReal C1 * ∫⁻ x, H (μ₂ 0 + b * x) ∂gaussianReal 0 1) := by
          gcongr
          exact one_dim_shift_dom ha hab (μ₁ 0) (μ₂ 0) H hHm
      _ = ENNReal.ofReal ((b / a) ^ (k + 1) *
            Real.exp ((∑ i, (μ₁ i - μ₂ i) ^ 2) / (2 * (b ^ 2 - a ^ 2)))) *
            ∫⁻ x, H (μ₂ 0 + b * x) ∂gaussianReal 0 1 := by
          rw [hconst, ENNReal.ofReal_mul hCk0, mul_assoc]

/-- **Domination of a narrower shifted Gaussian by a wider Gaussian with another centre.** -/
theorem gauss_shift_dom {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : BM f) (hf0 : ∀ z, 0 ≤ f z)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (μ₁ μ₂ : Fin n → ℝ) :
    ∫ z, f (μ₁ + a • z) ∂stdGauss (Fin n) ≤
      (b / a) ^ n * Real.exp ((∑ i, (μ₁ i - μ₂ i) ^ 2) / (2 * (b ^ 2 - a ^ 2))) *
        ∫ z, f (μ₂ + b • z) ∂stdGauss (Fin n) := by
  have hb : 0 < b := ha.trans hab
  have hsm : ∀ (ν : Fin n → ℝ) (c : ℝ), Measurable (fun z : Fin n → ℝ => ν + c • z) :=
    fun ν c => (measurable_const_smul c).const_add ν
  have hF : Measurable (fun z => ENNReal.ofReal (f z)) := hf.meas.ennreal_ofReal
  have h := gauss_shift_dom_lintegral ha hab n (fun z => ENNReal.ofReal (f z)) hF μ₁ μ₂
  have e : ∀ (ν : Fin n → ℝ) (c : ℝ), ∫ z, f (ν + c • z) ∂stdGauss (Fin n) =
      (∫⁻ z, ENNReal.ofReal (f (ν + c • z)) ∂stdGauss (Fin n)).toReal := fun ν c =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hf0 _)
      (hf.meas.comp (hsm ν c)).aestronglyMeasurable
  have fin : ∀ (ν : Fin n → ℝ) (c : ℝ),
      ∫⁻ z, ENNReal.ofReal (f (ν + c • z)) ∂stdGauss (Fin n) ≠ ⊤ := fun ν c =>
    ((hf.comp (hsm ν c)).integrable _).lintegral_lt_top.ne
  rw [e μ₁ a, e μ₂ b]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fin μ₂ b)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  exact h2

/-! ## The chi-square of a sub-family of coordinates -/

/-- **Chebyshev for the chi-square of a sub-family**: `P(|Σ_j ξ_{e j}² − D'| ≥ t) ≤ 2D'/t²`. -/
theorem chiSq_cheb_sub (ι : Type*) [Fintype ι] {κ : Type*} [Fintype κ] (e : κ → ι)
    (he : Function.Injective e) {t : ℝ} (ht : 0 < t) :
    (stdGauss ι).real {ξ | t ≤ |∑ j, ξ (e j) ^ 2 - (Fintype.card κ : ℝ)|} ≤
      2 * (Fintype.card κ : ℝ) / t ^ 2 := by
  classical
  set X : κ → (ι → ℝ) → ℝ := fun j ξ => ξ (e j) ^ 2 with hX
  have hmp : ∀ i, MeasurePreserving (Function.eval i : (ι → ℝ) → ℝ) (stdGauss ι)
      (gaussianReal 0 1) := fun i => by
    unfold stdGauss
    exact measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  have hmem : ∀ j, MemLp (X j) 2 (stdGauss ι) := fun j =>
    memLp_sq_gauss.comp_measurePreserving (hmp (e j))
  have hind0 : iIndepFun (fun (i : ι) (ξ : ι → ℝ) => ξ i ^ 2) (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun _ (x : ℝ) => x ^ 2)
      (fun _ => by fun_prop)
  have hind : iIndepFun X (stdGauss ι) := hind0.precomp he
  have hvar_i : ∀ j, Var[X j; stdGauss ι] = 2 := fun j => by
    have : X j = (fun x : ℝ => x ^ 2) ∘ (Function.eval (e j)) := rfl
    rw [this, ← variance_map (by fun_prop) (hmp (e j)).measurable.aemeasurable,
      (hmp (e j)).map_eq]
    exact var_sq_gauss
  have hmean_i : ∀ j, ∫ ξ, X j ξ ∂stdGauss ι = 1 := fun j => by
    have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
      rw [BstLean.Part29.gaussMom_eq 2]
      norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
    have h := integral_map (μ := stdGauss ι) (φ := Function.eval (e j))
      (hmp (e j)).measurable.aemeasurable (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [(hmp (e j)).map_eq, h2] at h
    exact h.symm
  have hsum : (fun ξ : ι → ℝ => ∑ j, ξ (e j) ^ 2) = ∑ j, X j := by
    funext ξ; simp [hX]
  have hvar : Var[fun ξ : ι → ℝ => ∑ j, ξ (e j) ^ 2; stdGauss ι] =
      2 * (Fintype.card κ : ℝ) := by
    rw [hsum, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp [hvar_i, mul_comm]
  have hmean : ∫ ξ : ι → ℝ, ∑ j, ξ (e j) ^ 2 ∂stdGauss ι = (Fintype.card κ : ℝ) := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    rw [Finset.sum_congr rfl (fun i _ => hmean_i i)]
    simp
  have hm2 : MemLp (fun ξ : ι → ℝ => ∑ j, ξ (e j) ^ 2) 2 (stdGauss ι) := by
    rw [hsum]
    exact memLp_finsetSum' _ (fun i _ => hmem i)
  have h := meas_ge_le_variance_div_sq hm2 ht
  rw [hmean, hvar] at h
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

end BstLean.Part106

#print axioms BstLean.Part106.gauss_shift_dom
#print axioms BstLean.Part106.chiSq_cheb_sub
