import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Part 182 (file `Bern`): the row-sum (Bernstein) inequality of Lemma TI

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, proof of Lemma `t7:p04:ti`, "a row-sum
inequality used three times": independent rows `X_j` with `|X_j| ≤ b₀(U_j² + V_j²)/2`, where
`U_j, V_j` are standard normal (any dependence inside a row), satisfy
`Pr(|∑_j (X_j − E X_j)| > 2b₀(√(2mτ) + τ)) ≤ 2e^{−τ}`.

* `bn_gauss_exp`, `bn_gauss_sq`: `E e^{aU²} = (1 − 2a)^{−1/2}` (`a < 1/2`), `E U² = 1`.
* `BernCond μ Y b`: for `0 ≤ s < 1/(2b)`, `E[e^{s|Y|} − 1 − s|Y|] ≤ 2b²s²/(1 − 2bs)`.
* `bn_of_gauss`: Gaussian domination `|Y| ≤ b(U² + V²)/2` gives `BernCond μ Y b` (and `Y ∈ L¹`).
  Route: monotonicity of `e^w − 1 − w`, convexity of `exp`, and
  `(1 − 2a)^{−1/2} − 1 − a ≤ 2a²/(1 − 2a)` (`bn_num`), in place of the paper's Minkowski moment
  bound `E|Y|^k ≤ b^k(2k−1)!!` and the series; the resulting MGF bound is the paper's.
* `bn_mgf`: `E e^{s(Y − EY)} ≤ exp(2b²s²/(1 − 2bs))`.
* `bn_upper`, `bn_two_sided`: the Chernoff step with the paper's `s`.
* **`bn_rowsum`**: the paper's statement.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real

lemma bn_pdf_mul (a x : ℝ) :
    gaussianPDFReal 0 1 x * exp (a * x ^ 2) = (√(2 * π))⁻¹ * exp (-(1 / 2 - a) * x ^ 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `E e^{aU²} = (1 − 2a)^{−1/2}` for `U ~ N(0,1)`, `a < 1/2`. -/
lemma bn_gauss_exp {a : ℝ} (ha : a < 1 / 2) :
    Integrable (fun x => exp (a * x ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, exp (a * x ^ 2) ∂gaussianReal 0 1 = 1 / √(1 - 2 * a) := by
  have hb : 0 < 1 / 2 - a := by linarith
  have hI := (integrable_exp_neg_mul_sq hb).const_mul (√(2 * π))⁻¹
  constructor
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    refine hI.congr (ae_of_all _ fun x => ?_)
    simp only [toReal_gaussianPDF, smul_eq_mul]
    rw [bn_pdf_mul]
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul, bn_pdf_mul]
    rw [integral_const_mul, integral_gaussian]
    have h1 : (0 : ℝ) < 2 * π := by positivity
    have h2 : 0 < 1 - 2 * a := by linarith
    rw [show π / (1 / 2 - a) = (2 * π) / (1 - 2 * a) by field_simp]
    rw [Real.sqrt_div h1.le, inv_mul_eq_div]
    have h3 : 0 < √(2 * π) := Real.sqrt_pos.2 h1
    field_simp

lemma bn_gauss_sq : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa [integral_id_gaussianReal] using h

/-! ## Pointwise inequalities -/

/-- `e^y − 1 − y ≤ e^{|y|} − 1 − |y|`. -/
lemma bn_exp_sub_le_abs (y : ℝ) : exp y - 1 - y ≤ exp |y| - 1 - |y| := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy]
    have h := (Real.self_le_sinh_iff (x := -y)).2 (by linarith)
    rw [Real.sinh_eq, neg_neg] at h
    linarith

/-- `w ↦ e^w − 1 − w` is monotone on `w ≥ 0`. -/
lemma bn_phi_mono {u w : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) :
    exp u - 1 - u ≤ exp w - 1 - w := by
  have h1 := Real.add_one_le_exp (w - u)
  have h2 : exp w = exp u * exp (w - u) := by rw [← Real.exp_add]; ring_nf
  have h3 : 1 ≤ exp u := Real.one_le_exp hu
  have h4 : 0 ≤ w - u := by linarith
  have h5 : exp u * (w - u + 1) ≤ exp u * exp (w - u) :=
    mul_le_mul_of_nonneg_left h1 (exp_pos _).le
  nlinarith

/-- `e^{(x+y)/2} ≤ (e^x + e^y)/2`. -/
lemma bn_exp_mid (x y : ℝ) : exp ((x + y) / 2) ≤ (exp x + exp y) / 2 := by
  have hx : exp x = exp (x / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have hy : exp y = exp (y / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have hxy : exp ((x + y) / 2) = exp (x / 2) * exp (y / 2) := by rw [← Real.exp_add]; ring_nf
  rw [hx, hy, hxy]
  nlinarith [sq_nonneg (exp (x / 2) - exp (y / 2))]

/-- `(1 − 2a)^{−1/2} − 1 − a ≤ 2a²/(1 − 2a)` for `0 ≤ a < 1/2`. -/
lemma bn_num {a : ℝ} (ha : a < 1 / 2) :
    1 / √(1 - 2 * a) - 1 - a ≤ 2 * a ^ 2 / (1 - 2 * a) := by
  have h2 : 0 < 1 - 2 * a := by linarith
  set r := √(1 - 2 * a) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 h2
  have hr2 : r ^ 2 = 1 - 2 * a := Real.sq_sqrt h2.le
  have ha' : a = (1 - r ^ 2) / 2 := by linarith
  rw [← hr2, ha']
  have e : 2 * ((1 - r ^ 2) / 2) ^ 2 / r ^ 2 - (1 / r - 1 - (1 - r ^ 2) / 2) =
      (1 - r) ^ 2 / (2 * r ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (1 - r) ^ 2 / (2 * r ^ 2) := by positivity
  linarith

/-! ## The Bernstein condition and the moment generating function of one summand -/

/-- **The Bernstein exponential-moment condition** with scale `b`: for `0 ≤ s < 1/(2b)`,
`e^{s|Y|}` is integrable and `E[e^{s|Y|} − 1 − s|Y|] ≤ 2b²s²/(1 − 2bs)`. -/
def BernCond {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (b : ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → 2 * b * s < 1 →
    Integrable (fun ω => exp (s * |Y ω|)) μ ∧
      ∫ ω, (exp (s * |Y ω|) - 1 - s * |Y ω|) ∂μ ≤ 2 * b ^ 2 * s ^ 2 / (1 - 2 * b * s)

lemma bn_bernCond_neg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ} {b : ℝ}
    (h : BernCond μ Y b) : BernCond μ (fun ω => -Y ω) b := by
  intro s hs hbs
  simpa only [abs_neg] using h s hs hbs

/-- **The centred moment generating function of one summand**:
`E e^{s(Y − EY)} ≤ exp(2b²s²/(1 − 2bs))`, and the integrability of `e^{s(Y − EY)}`. -/
theorem bn_mgf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {b s : ℝ} (hYm : Measurable Y) (hYi : Integrable Y μ) (hB : BernCond μ Y b)
    (hs : 0 ≤ s) (hbs : 2 * b * s < 1) :
    Integrable (fun ω => exp (s * (Y ω - ∫ x, Y x ∂μ))) μ ∧
      mgf (fun ω => Y ω - ∫ x, Y x ∂μ) μ s ≤ exp (2 * b ^ 2 * s ^ 2 / (1 - 2 * b * s)) := by
  obtain ⟨hI, hC⟩ := hB s hs hbs
  set m := ∫ x, Y x ∂μ with hm
  set K := 2 * b ^ 2 * s ^ 2 / (1 - 2 * b * s) with hK
  have hsY : Integrable (fun ω => exp (s * Y ω)) μ := by
    refine hI.mono' ((hYm.const_mul s).exp.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact Real.exp_le_exp.2 (by
      have := le_abs_self (Y ω)
      nlinarith [abs_nonneg (Y ω)])
  have hAbs : Integrable (fun ω => |Y ω|) μ := hYi.abs
  have hpt : ∀ ω, exp (s * Y ω) ≤ 1 + s * Y ω + (exp (s * |Y ω|) - 1 - s * |Y ω|) := by
    intro ω
    have h := bn_exp_sub_le_abs (s * Y ω)
    rw [abs_mul, abs_of_nonneg hs] at h
    linarith
  have hR : Integrable (fun ω => 1 + s * Y ω + (exp (s * |Y ω|) - 1 - s * |Y ω|)) μ :=
    ((integrable_const _).add (hYi.const_mul s)).add
      ((hI.sub (integrable_const _)).sub (hAbs.const_mul s))
  have h1 : ∫ ω, exp (s * Y ω) ∂μ ≤ 1 + s * m + K := by
    refine (integral_mono hsY hR hpt).trans ?_
    have hA : Integrable (fun x => 1 + s * Y x) μ := (integrable_const _).add (hYi.const_mul s)
    have hB' : Integrable (fun x => exp (s * |Y x|) - 1 - s * |Y x|) μ :=
      (hI.sub (integrable_const _)).sub (hAbs.const_mul s)
    have hS : Integrable (fun x => s * Y x) μ := hYi.const_mul s
    rw [integral_add hA hB', integral_add (integrable_const (1 : ℝ)) hS, integral_const,
      integral_const_mul]
    simp only [probReal_univ, one_smul]
    linarith
  have heq : ∀ ω, exp (s * (Y ω - m)) = exp (-(s * m)) * exp (s * Y ω) := by
    intro ω; rw [← Real.exp_add]; ring_nf
  refine ⟨?_, ?_⟩
  · simp_rw [heq]; exact hsY.const_mul _
  · unfold mgf
    simp_rw [heq]
    rw [integral_const_mul]
    calc exp (-(s * m)) * ∫ ω, exp (s * Y ω) ∂μ ≤ exp (-(s * m)) * (1 + s * m + K) :=
          mul_le_mul_of_nonneg_left h1 (exp_pos _).le
      _ ≤ exp (-(s * m)) * exp (s * m + K) := by
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          have := Real.add_one_le_exp (s * m + K)
          linarith
      _ = exp K := by rw [← Real.exp_add]; ring_nf

/-! ## The row-sum inequality -/

/-- The exponent algebra of the Bernstein tail: with `L = √(2mτ)`, `λ = L/(2mb)`,
`s = λ/(1 + 2bλ)`: `−s·2b(L + τ) + m·2b²s²/(1 − 2bs) = −τ`, and `2bs < 1`. -/
lemma bn_exponent {m b τ : ℝ} (hm : 0 < m) (hb : 0 < b) (hτ : 0 ≤ τ) :
    let L := √(2 * m * τ)
    let lam := L / (2 * m * b)
    let s := lam / (1 + 2 * b * lam)
    0 ≤ s ∧ 2 * b * s < 1 ∧
      -s * (2 * b * (L + τ)) + m * (2 * b ^ 2 * s ^ 2 / (1 - 2 * b * s)) = -τ := by
  intro L lam s
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hL2 : L ^ 2 = 2 * m * τ := Real.sq_sqrt (by positivity)
  have hlam0 : 0 ≤ lam := by positivity
  have hd : 0 < 1 + 2 * b * lam := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hbs : 2 * b * s < 1 := by
    show 2 * b * (lam / (1 + 2 * b * lam)) < 1
    rw [mul_div_assoc', div_lt_one hd]; linarith
  refine ⟨hs0, hbs, ?_⟩
  have h1 : 1 - 2 * b * s = 1 / (1 + 2 * b * lam) := by
    show 1 - 2 * b * (lam / (1 + 2 * b * lam)) = 1 / (1 + 2 * b * lam)
    field_simp
    ring
  have hlamL : 2 * b * lam * L = 2 * τ := by
    show 2 * b * (L / (2 * m * b)) * L = 2 * τ
    field_simp
    rw [hL2]
  rw [h1]
  show -(lam / (1 + 2 * b * lam)) * (2 * b * (L + τ)) +
      m * (2 * b ^ 2 * (lam / (1 + 2 * b * lam)) ^ 2 / (1 / (1 + 2 * b * lam))) = -τ
  have hm2 : m * (2 * b ^ 2 * lam ^ 2) = τ := by
    have : lam = L / (2 * m * b) := rfl
    rw [this, div_pow, hL2]; field_simp
  field_simp
  nlinarith [hlamL, hm2]

/-- **The upper tail of the row sum** (Bernstein): independent summands with the Bernstein
condition at scale `b > 0`, `m ≥ 1` rows, `τ ≥ 0`:
`Pr(∑_j (X_j − E X_j) ≥ 2b(√(2mτ) + τ)) ≤ e^{−τ}`. -/
theorem bn_upper {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} {X : Fin m → Ω → ℝ} (hind : iIndepFun X μ) (hXm : ∀ j, Measurable (X j))
    (hXi : ∀ j, Integrable (X j) μ) {b τ : ℝ} (hB : ∀ j, BernCond μ (X j) b) (hb : 0 < b)
    (hm : 0 < m) (hτ : 0 ≤ τ) :
    μ.real {ω | 2 * b * (√(2 * m * τ) + τ) ≤ ∑ j, (X j ω - ∫ x, X j x ∂μ)} ≤ exp (-τ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hs0, hbs, hE⟩ := bn_exponent hmR hb hτ
  set L := √(2 * (m : ℝ) * τ)
  set s := L / (2 * m * b) / (1 + 2 * b * (L / (2 * m * b))) with hsd
  set Y : Fin m → Ω → ℝ := fun j ω => X j ω - ∫ x, X j x ∂μ with hY
  have hYind : iIndepFun Y μ :=
    hind.comp (fun j x => x - ∫ x, X j x ∂μ) (fun j => measurable_id.sub_const _)
  have hYm : ∀ j, Measurable (Y j) := fun j => (hXm j).sub_const _
  have hone := fun j => bn_mgf (hXm j) (hXi j) (hB j) hs0 hbs
  have hfun : (fun ω => ∑ j, (X j ω - ∫ x, X j x ∂μ)) = ∑ j ∈ Finset.univ, Y j := by
    funext ω; simp [hY, Finset.sum_apply]
  have hint : Integrable (fun ω => exp (s * (∑ j ∈ Finset.univ, Y j) ω)) μ :=
    hYind.integrable_exp_mul_sum hYm (fun j _ => (hone j).1)
  have hch := measure_ge_le_exp_mul_mgf (X := ∑ j ∈ Finset.univ, Y j)
    (2 * b * (L + τ)) hs0 hint
  rw [hYind.mgf_sum hYm] at hch
  have hprod : ∏ j ∈ Finset.univ, mgf (Y j) μ s ≤
      ∏ _j ∈ (Finset.univ : Finset (Fin m)), exp (2 * b ^ 2 * s ^ 2 / (1 - 2 * b * s)) :=
    Finset.prod_le_prod₀ (fun j _ => (mgf_pos (hone j).1).le) (fun j _ => (hone j).2)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul] at hprod
  have hset : {ω | 2 * b * (√(2 * m * τ) + τ) ≤ ∑ j, (X j ω - ∫ x, X j x ∂μ)} =
      {ω | 2 * b * (L + τ) ≤ (∑ j ∈ Finset.univ, Y j) ω} := by
    rw [← hfun]
  rw [hset]
  refine hch.trans ?_
  calc exp (-s * (2 * b * (L + τ))) * ∏ j ∈ Finset.univ, mgf (Y j) μ s
      ≤ exp (-s * (2 * b * (L + τ))) * exp (m * (2 * b ^ 2 * s ^ 2 / (1 - 2 * b * s))) :=
        mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp (-τ) := by rw [← Real.exp_add, hE]

/-- **The row-sum inequality, two-sided** (paper, proof of Lemma `t7:p04:ti`):
`Pr(|∑_j (X_j − E X_j)| > 2b(√(2mτ) + τ)) ≤ 2e^{−τ}`. -/
theorem bn_two_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} {X : Fin m → Ω → ℝ} (hind : iIndepFun X μ) (hXm : ∀ j, Measurable (X j))
    (hXi : ∀ j, Integrable (X j) μ) {b τ : ℝ} (hB : ∀ j, BernCond μ (X j) b) (hb : 0 < b)
    (hm : 0 < m) (hτ : 0 ≤ τ) :
    μ.real {ω | 2 * b * (√(2 * m * τ) + τ) < |∑ j, (X j ω - ∫ x, X j x ∂μ)|} ≤
      2 * exp (-τ) := by
  have hup := bn_upper hind hXm hXi hB hb hm hτ
  have hindN : iIndepFun (fun j ω => -X j ω) μ :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hlo := bn_upper hindN (fun j => (hXm j).neg) (fun j => (hXi j).neg)
    (fun j => bn_bernCond_neg (hB j)) hb hm hτ
  have hsub : {ω | 2 * b * (√(2 * m * τ) + τ) < |∑ j, (X j ω - ∫ x, X j x ∂μ)|} ⊆
      {ω | 2 * b * (√(2 * m * τ) + τ) ≤ ∑ j, (X j ω - ∫ x, X j x ∂μ)} ∪
        {ω | 2 * b * (√(2 * m * τ) + τ) ≤ ∑ j, (-X j ω - ∫ x, -X j x ∂μ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases lt_abs.1 hω with h | h
    · exact Or.inl h.le
    · right
      simp only [Set.mem_setOf_eq, integral_neg]
      have e : ∑ j, (-X j ω - -∫ x, X j x ∂μ) = -∑ j, (X j ω - ∫ x, X j x ∂μ) := by
        rw [← Finset.sum_neg_distrib]; congr 1; funext j; ring
      rw [e]; exact h.le
  calc μ.real {ω | 2 * b * (√(2 * m * τ) + τ) < |∑ j, (X j ω - ∫ x, X j x ∂μ)|}
      ≤ μ.real ({ω | 2 * b * (√(2 * m * τ) + τ) ≤ ∑ j, (X j ω - ∫ x, X j x ∂μ)} ∪
        {ω | 2 * b * (√(2 * m * τ) + τ) ≤ ∑ j, (-X j ω - ∫ x, -X j x ∂μ)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ exp (-τ) + exp (-τ) := add_le_add hup hlo
    _ = 2 * exp (-τ) := by ring

/-! ## Gaussian domination implies the Bernstein condition -/

lemma bn_pull {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ} (hUm : Measurable U)
    (hU : μ.map U = gaussianReal 0 1) {g : ℝ → ℝ} (hg : Measurable g)
    (hgi : Integrable g (gaussianReal 0 1)) :
    Integrable (fun ω => g (U ω)) μ ∧ ∫ ω, g (U ω) ∂μ = ∫ x, g x ∂gaussianReal 0 1 := by
  rw [← hU] at hgi ⊢
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable hUm.aemeasurable).1 hgi, ?_⟩
  exact (integral_map hUm.aemeasurable hg.aestronglyMeasurable).symm

lemma bn_integrable_sq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  have h := ((bn_gauss_exp (a := 1 / 4) (by norm_num)).1).const_mul 4
  refine h.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  have := Real.add_one_le_exp (1 / 4 * x ^ 2)
  nlinarith

/-- **Gaussian domination gives the Bernstein condition**: if `|Y| ≤ b(U² + V²)/2` with
`U, V ~ N(0, 1)` (possibly dependent) and `b ≥ 0`, then `Y` is integrable and satisfies
`BernCond μ Y b`. (Paper: Minkowski gives `E|Y|^k ≤ b^k (2k−1)!!`; here the exponential form is
proved directly from `E e^{aU²} = (1 − 2a)^{−1/2}` and the convexity of `exp`.) -/
theorem bn_of_gauss {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y U V : Ω → ℝ} {b : ℝ} (hb : 0 ≤ b) (hYm : Measurable Y) (hUm : Measurable U)
    (hVm : Measurable V) (hU : μ.map U = gaussianReal 0 1) (hV : μ.map V = gaussianReal 0 1)
    (hdom : ∀ ω, |Y ω| ≤ b * (U ω ^ 2 + V ω ^ 2) / 2) :
    Integrable Y μ ∧ BernCond μ Y b := by
  obtain ⟨hU2, hU2e⟩ := bn_pull hUm hU (by fun_prop) bn_integrable_sq
  obtain ⟨hV2, hV2e⟩ := bn_pull hVm hV (by fun_prop) bn_integrable_sq
  rw [bn_gauss_sq] at hU2e hV2e
  have hW : Integrable (fun ω => b * (U ω ^ 2 + V ω ^ 2) / 2) μ :=
    ((hU2.add hV2).const_mul b).div_const 2
  have hYi : Integrable Y μ := by
    refine hW.mono' hYm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hdom ω
  refine ⟨hYi, fun s hs hbs => ?_⟩
  set a := s * b with ha
  have ha0 : 0 ≤ a := mul_nonneg hs hb
  have ha2 : a < 1 / 2 := by rw [ha]; linarith
  obtain ⟨hgi, hge⟩ := bn_gauss_exp ha2
  obtain ⟨hEU, hEUe⟩ := bn_pull hUm hU (g := fun x => exp (a * x ^ 2)) (by fun_prop) hgi
  obtain ⟨hEV, hEVe⟩ := bn_pull hVm hV (g := fun x => exp (a * x ^ 2)) (by fun_prop) hgi
  have hpt1 : ∀ ω, 0 ≤ s * |Y ω| ∧ s * |Y ω| ≤ (a * U ω ^ 2 + a * V ω ^ 2) / 2 := by
    intro ω
    refine ⟨mul_nonneg hs (abs_nonneg _), ?_⟩
    have := mul_le_mul_of_nonneg_left (hdom ω) hs
    rw [ha]; nlinarith
  have hexp : ∀ ω, exp (s * |Y ω|) ≤ (exp (a * U ω ^ 2) + exp (a * V ω ^ 2)) / 2 := fun ω =>
    (Real.exp_le_exp.2 (hpt1 ω).2).trans (bn_exp_mid _ _)
  have hI : Integrable (fun ω => exp (s * |Y ω|)) μ := by
    refine ((hEU.add hEV).div_const 2).mono' (((continuous_abs.measurable.comp hYm).const_mul s).exp.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hexp ω
  refine ⟨hI, ?_⟩
  have hphi : ∀ ω, exp (s * |Y ω|) - 1 - s * |Y ω| ≤
      ((exp (a * U ω ^ 2) - 1 - a * U ω ^ 2) + (exp (a * V ω ^ 2) - 1 - a * V ω ^ 2)) / 2 := by
    intro ω
    refine (bn_phi_mono (hpt1 ω).1 (hpt1 ω).2).trans ?_
    have := bn_exp_mid (a * U ω ^ 2) (a * V ω ^ 2)
    linarith
  have hL : Integrable (fun ω => exp (s * |Y ω|) - 1 - s * |Y ω|) μ :=
    (hI.sub (integrable_const _)).sub
      ((show Integrable (fun ω => |Y ω|) μ by simpa only [Real.norm_eq_abs] using hYi.norm).const_mul s)
  have hAU : Integrable (fun ω => exp (a * U ω ^ 2) - 1 - a * U ω ^ 2) μ :=
    (hEU.sub (integrable_const _)).sub (hU2.const_mul a)
  have hAV : Integrable (fun ω => exp (a * V ω ^ 2) - 1 - a * V ω ^ 2) μ :=
    (hEV.sub (integrable_const _)).sub (hV2.const_mul a)
  have h1 := integral_mono hL ((hAU.add hAV).div_const 2) hphi
  have eU : ∫ ω, (exp (a * U ω ^ 2) - 1 - a * U ω ^ 2) ∂μ = 1 / √(1 - 2 * a) - 1 - a := by
    have hA1 : Integrable (fun ω => exp (a * U ω ^ 2) - 1) μ := hEU.sub (integrable_const _)
    have hA2 : Integrable (fun ω => a * U ω ^ 2) μ := hU2.const_mul a
    rw [integral_sub hA1 hA2, integral_sub hEU (integrable_const (1 : ℝ)), integral_const,
      integral_const_mul, hEUe, hge, hU2e]
    simp
  have eV : ∫ ω, (exp (a * V ω ^ 2) - 1 - a * V ω ^ 2) ∂μ = 1 / √(1 - 2 * a) - 1 - a := by
    have hA1 : Integrable (fun ω => exp (a * V ω ^ 2) - 1) μ := hEV.sub (integrable_const _)
    have hA2 : Integrable (fun ω => a * V ω ^ 2) μ := hV2.const_mul a
    rw [integral_sub hA1 hA2, integral_sub hEV (integrable_const (1 : ℝ)), integral_const,
      integral_const_mul, hEVe, hge, hV2e]
    simp
  simp only [Pi.add_apply] at h1
  rw [integral_div, integral_add hAU hAV, eU, eV] at h1
  have h2 := bn_num ha2
  have e2 : 2 * a ^ 2 / (1 - 2 * a) = 2 * b ^ 2 * s ^ 2 / (1 - 2 * b * s) := by
    rw [ha]; ring_nf
  linarith

/-- **The row-sum inequality of Lemma `t7:p04:ti`** (paper statement): independent rows
`X_j` with `|X_j| ≤ b(U_j² + V_j²)/2`, `U_j, V_j ~ N(0, 1)` (any dependence inside a row),
`b > 0`, `m ≥ 1`, `τ ≥ 0`: `Pr(|∑_j (X_j − E X_j)| > 2b(√(2mτ) + τ)) ≤ 2e^{−τ}`. -/
theorem bn_rowsum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} {X U V : Fin m → Ω → ℝ} (hind : iIndepFun X μ) (hXm : ∀ j, Measurable (X j))
    (hUm : ∀ j, Measurable (U j)) (hVm : ∀ j, Measurable (V j))
    (hU : ∀ j, μ.map (U j) = gaussianReal 0 1) (hV : ∀ j, μ.map (V j) = gaussianReal 0 1)
    {b τ : ℝ} (hb : 0 < b) (hdom : ∀ j ω, |X j ω| ≤ b * (U j ω ^ 2 + V j ω ^ 2) / 2)
    (hm : 0 < m) (hτ : 0 ≤ τ) :
    μ.real {ω | 2 * b * (√(2 * m * τ) + τ) < |∑ j, (X j ω - ∫ x, X j x ∂μ)|} ≤
      2 * exp (-τ) := by
  have h := fun j => bn_of_gauss hb.le (hXm j) (hUm j) (hVm j) (hU j) (hV j) (hdom j)
  exact bn_two_sided hind hXm (fun j => (h j).1) (fun j => (h j).2) hb hm hτ

end BstLean.Part182

open BstLean.Part182 in
#print axioms bn_rowsum
open BstLean.Part182 in
#print axioms bn_two_sided
open BstLean.Part182 in
#print axioms bn_of_gauss
