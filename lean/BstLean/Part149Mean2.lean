import BstLean.Part149Mean
import BstLean.Part149Cos3
import BstLean.Part149KK

/-!
# Part 149, helper `Mean2`: the kernel error and the fluctuation of `X`, second route

Role: `delegations/statements/p149-spec.md`.

Do not use `sorry`, `native_decide` or `axiom`.

`q = β²/(β² + τ²)` is in the window `462/1000 ≤ q ≤ 527/1000`; `b` is the slope of `κ∘κ` at `q`
(`kk_quad_at_sharp`: `9/20 ≤ b ≤ 1/2`), which takes the place of the Lipschitz constant `1` of
`errK_mean`.

* `errXc c τ θ = E_γ (⟨a₂(x(γ)), b̄⟩ − |b̄|²)²`; `measurable_errXc`.
* `dK2`, **`errK_mean2`**: `E_ξ E_θ errKc ((m/n)·κ(κ(q))) (β·ξ) τ θ ≤ ((m/n)·dK2 n m q)²`.
* `dX2`, **`errX_mean2`**: `E_ξ E_θ errXc (β·ξ) τ θ ≤ ((m/n)·dX2 n m q)²`.
* **`dK2_le`**, **`dX2_le`**: for `n ≥ 4096`, `m = mA n` and `q` in the window,
  `dK2 ≤ 0.393278/√n + 11.363/n` and `dX2 ≤ 0.16034/√n + 11.363/n`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part145

variable {n m : ℕ}

/-! ## Definitions -/

/-- The integrated squared fluctuation of `X(γ) = ⟨a₂(x(γ)), b̄⟩` around `|b̄|²`. -/
noncomputable def errXc {n m : ℕ} (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : ℝ :=
  ∫ γ, (∑ j, hA c τ θ γ j * bbar c τ θ j - normSq (bbar c τ θ)) ^ 2 ∂stdGauss (Fin n)

/-- The bound of the kernel error against a constant, second route. -/
noncomputable def dK2 (n m : ℕ) (q : ℝ) : ℝ :=
  cF2o m + 1 / 2 * ((1 - q ^ 2) / √(n : ℝ) + jCosC n) + 6 / 5 * m4c n q

/-- The bound of the fluctuation of `X`. -/
noncomputable def dX2 (n m : ℕ) (q : ℝ) : ℝ :=
  cF2o m + 1 / 2 * (√(q * (1 - q) ^ 2 * (1 - q / 2) / (n : ℝ)) + jCosC n) + 6 / 5 * m4c n q

/-- The cosine of the two points of the cheap stand-in. -/
noncomputable abbrev cosS (β τ : ℝ) (w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2))

/-- The Gram kernel of the hidden layers at the two points of the cheap stand-in. -/
noncomputable abbrev gramS (β τ : ℝ) (z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m) : ℝ :=
  dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
    (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2)))

/-! ## Abstract tools -/

section Generic

variable {α β' δ Θ : Type*} [MeasurableSpace α] [MeasurableSpace β'] [MeasurableSpace δ]
  [MeasurableSpace Θ]

/-- **Jensen over the middle coordinate.** -/
theorem L2le_integral_mid (μ : Measure α) (ν : Measure β') (ρ : Measure Θ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {f : (α × β') × Θ → ℝ} {a : ℝ} (h : L2le ((μ.prod ν).prod ρ) f a) :
    L2le (μ.prod ρ) (fun p : α × Θ => ∫ y, f ((p.1, y), p.2) ∂ν) a := by
  have e0 : Measure.map MeasurableEquiv.prodAssoc ((μ.prod ν).prod ρ) = μ.prod (ν.prod ρ) :=
    Measure.prodAssoc_prod
  have h1 : L2le (μ.prod (ν.prod ρ))
      (fun z : α × β' × Θ => f (MeasurableEquiv.prodAssoc.symm z)) a :=
    h.comp_map MeasurableEquiv.prodAssoc.symm.measurable (by
      rw [← e0]
      exact MeasurableEquiv.map_symm_map _)
  have h2 : L2le (μ.prod (ρ.prod ν))
      (fun z : α × Θ × β' => f (MeasurableEquiv.prodAssoc.symm (Prod.map id Prod.swap z))) a :=
    h1.comp_map (φ := Prod.map id Prod.swap) (measurable_id.prodMap measurable_swap) (by
      rw [← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id,
        Measure.prod_swap])
  have h3 := h2.comp_map (P := (μ.prod ρ).prod ν) MeasurableEquiv.prodAssoc.measurable
    Measure.prodAssoc_prod
  exact h3.integral_right.congr_fun fun p => rfl

/-- Jensen over the third coordinate of a triple, with a fourth coordinate kept. -/
theorem L2le_integral_third (μ₁ : Measure α) (μ₂ : Measure β') (μ₃ : Measure δ) (ρ : Measure Θ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃]
    [IsProbabilityMeasure ρ] {f : (α × β' × δ) × Θ → ℝ} {a : ℝ}
    (h : L2le ((μ₁.prod (μ₂.prod μ₃)).prod ρ) f a) :
    L2le ((μ₁.prod μ₂).prod ρ)
      (fun p : (α × β') × Θ => ∫ y, f ((p.1.1, p.1.2, y), p.2) ∂μ₃) a := by
  have h1 : L2le (((μ₁.prod μ₂).prod μ₃).prod ρ)
      (fun z : ((α × β') × δ) × Θ => f (Prod.map MeasurableEquiv.prodAssoc id z)) a :=
    h.comp_map (MeasurableEquiv.prodAssoc.measurable.prodMap measurable_id) (by
      rw [← Measure.map_prod_map _ _ MeasurableEquiv.prodAssoc.measurable measurable_id,
        Measure.map_id, Measure.prodAssoc_prod])
  exact (L2le_integral_mid (μ₁.prod μ₂) μ₃ ρ h1).congr_fun fun p => rfl

/-- A finite sum of bounded measurable functions. -/
lemma bm_sum {ι : Type*} (s : Finset ι) {F : ι → α → ℝ} (h : ∀ i, BM (F i)) :
    BM (fun x => ∑ i ∈ s, F i x) := by
  classical
  refine Finset.induction_on s (by simpa using BM.const (α := α) 0) ?_
  intro a s ha ih
  simp only [Finset.sum_insert ha]
  exact (h a).add ih

/-- **The variance is the least mean square deviation from a constant.** -/
lemma var_min {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ} (hX : BM X) (a : ℝ) :
    ∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ ≤ ∫ x, (X x - a) ^ 2 ∂μ := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ y, X y ∂μ := ⟨_, rfl⟩
  rw [← hc]
  have i1 : Integrable (fun x => (X x - c) ^ 2) μ := ((hX.sub (BM.const c)).sq).integrable μ
  have i2 : Integrable (fun x => X x - c) μ := (hX.sub (BM.const c)).integrable μ
  have e : (fun x => (X x - a) ^ 2) =
      fun x => (X x - c) ^ 2 + 2 * (c - a) * (X x - c) + (c - a) ^ 2 := by
    funext x; ring
  have z : ∫ x, (X x - c) ∂μ = 0 := by
    rw [integral_sub (hX.integrable μ) (integrable_const c), integral_const, ← hc]
    simp
  have i3 : Integrable (fun x => 2 * (c - a) * (X x - c)) μ := i2.const_mul _
  have i4 : Integrable (fun x => (X x - c) ^ 2 + 2 * (c - a) * (X x - c)) μ := i1.add i3
  rw [e, integral_add i4 (integrable_const _), integral_add i1 i3, integral_const_mul, z,
    integral_const]
  have := sq_nonneg (c - a)
  have hu : μ.real univ = 1 := by simp
  rw [hu, one_smul, mul_zero, add_zero]
  linarith

/-- The decomposition of an integral into three parts. -/
lemma int_decomp {μ : Measure α} [IsProbabilityMeasure μ] {Gf K S : α → ℝ}
    (iG : Integrable Gf μ) (iK : Integrable K μ) (iS : Integrable S μ) (d kq b φ : ℝ) :
    (∫ y, (Gf y - d * K y) ∂μ) + (∫ y, d * (K y - kq - b * S y) ∂μ) +
        d * b * ((∫ y, S y ∂μ) - φ) =
      (∫ y, Gf y ∂μ) - d * (kq + b * φ) := by
  have e1 : ∫ y, (Gf y - d * K y) ∂μ = (∫ y, Gf y ∂μ) - d * ∫ y, K y ∂μ := by
    rw [integral_sub iG (iK.const_mul d), integral_const_mul]
  have e2 : ∫ y, d * (K y - kq - b * S y) ∂μ =
      d * ((∫ y, K y ∂μ) - kq - b * ∫ y, S y ∂μ) := by
    have i1 : Integrable (fun y => K y - kq) μ := iK.sub (integrable_const kq)
    have i2 : Integrable (fun y => b * S y) μ := iS.const_mul b
    rw [integral_const_mul, integral_sub i1 i2, integral_sub iK (integrable_const kq),
      integral_const_mul, integral_const]
    simp
  rw [e1, e2]
  ring

end Generic

local notation "G1" => stdGauss (Fin n)

/-! ## The three parts in `L²` -/

/-- The remainder of `κ∘κ` after its tangent at `q`, at the cosine of the two points. -/
lemma remR_L2 (hn : 1 ≤ n) (β τ : ℝ) {q b c4 : ℝ}
    (hquad : ∀ s ∈ Icc (-1 : ℝ) 1, 0 ≤ kappa (kappa s) - kappa (kappa q) - b * (s - q) ∧
      kappa (kappa s) - kappa (kappa q) - b * (s - q) ≤ 6 / 5 * (s - q) ^ 2)
    (c2 : L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => (cosS β τ w - q) ^ 2) c4) :
    L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        kappa (kappa (cosS β τ w)) - kappa (kappa q) - b * (cosS β τ w - q)) (6 / 5 * c4) := by
  have c3 := c2.const_mul_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5)
  refine L2le.of_abs_le ?_ c3 fun w => ?_
  · exact ((((continuous_kappa.comp continuous_kappa).measurable.comp
      (measurable_cheapDot β τ)).sub measurable_const).sub
        (((measurable_cheapDot β τ).sub measurable_const).const_mul b)).aestronglyMeasurable
  · obtain ⟨h0, h1⟩ := hquad _ (abs_cheapDot_mem hn β τ w)
    rw [abs_of_nonneg h0, abs_of_nonneg (by positivity)]
    exact h1

/-- **The kernel against the constant `(m/n)·κ(κ(q))`, with the slope `b ≤ 1/2`.** -/
lemma kern2_L2 (hn : 1 ≤ n) (hm : 1 ≤ m) (β τ : ℝ) {q b c1 c4 : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2) (hc1 : 0 ≤ c1) (hc4 : 0 ≤ c4)
    (hquad : ∀ s ∈ Icc (-1 : ℝ) 1, 0 ≤ kappa (kappa s) - kappa (kappa q) - b * (s - q) ∧
      kappa (kappa s) - kappa (kappa q) - b * (s - q) ≤ 6 / 5 * (s - q) ^ 2)
    (c0 : L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => cosS β τ w - q) c1)
    (c2 : L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => (cosS β τ w - q) ^ 2) c4) :
    L2le (((G1).prod ((G1).prod G1)).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        gramS β τ z - (m : ℝ) / n * kappa (kappa q))
      ((m : ℝ) / n * (cF2o m + 1 / 2 * c1 + 6 / 5 * c4)) := by
  have hd : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
  have hF := (Part136.cF2o_pos hm).le
  have p1 : L2le (((G1).prod ((G1).prod G1)).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        gramS β τ z - (m : ℝ) / n * kappa (kappa (cosS β τ z.1)))
      ((m : ℝ) / n * cF2o m) := cheapGram_L2 hn hm β τ
  have p2 : L2le (((G1).prod ((G1).prod G1)).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        (m : ℝ) / n * b * (cosS β τ z.1 - q)) ((m : ℝ) / n * (1 / 2 * c1)) :=
    ((c0.comp_fst (ν := hidGauss n m)).const_mul_nonneg (mul_nonneg hd hb0)).mono
      (mul_nonneg (mul_nonneg hd hb0) hc1) (by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb1 hc1) hd
        linarith)
  have p3 : L2le (((G1).prod ((G1).prod G1)).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        (m : ℝ) / n * (kappa (kappa (cosS β τ z.1)) - kappa (kappa q) - b * (cosS β τ z.1 - q)))
      ((m : ℝ) / n * (6 / 5 * c4)) :=
    ((remR_L2 hn β τ hquad c2).comp_fst (ν := hidGauss n m)).const_mul_nonneg hd
  have key := ((p1.add' p2 (mul_nonneg hd hF) (mul_nonneg hd (by positivity))).add' p3
    (add_nonneg (mul_nonneg hd hF) (mul_nonneg hd (by positivity)))
    (mul_nonneg hd (by positivity)))
  refine (key.congr_fun fun z => ?_).congr_bound (by ring)
  ring

/-! ## The function `X` -/

lemma dot_hA_int (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) (γ : Fin n → ℝ) :
    Integrable (fun y : Fin n → ℝ => dotp (hA c τ θ γ) (hA c τ θ y)) G1 ∧
      ∫ y, dotp (hA c τ θ γ) (hA c τ θ y) ∂G1 = ∑ j, hA c τ θ γ j * bbar c τ θ j := by
  constructor
  · change Integrable (fun y : Fin n → ℝ => ∑ j, hA c τ θ γ j * hA c τ θ y j) G1
    exact integrable_finsetSum _ fun j _ => ((bm_hA hn c τ θ j).integrable _).const_mul _
  · change ∫ y, ∑ j, hA c τ θ γ j * hA c τ θ y j ∂G1 = ∑ j, hA c τ θ γ j * bbar c τ θ j
    rw [integral_finsetSum _ fun j _ => ((bm_hA hn c τ θ j).integrable _).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl

lemma kk_cos_int (hn : 1 ≤ n) (β τ : ℝ) (ξ γ : Fin n → ℝ) :
    Integrable (fun y : Fin n → ℝ => kappa (kappa (cosS β τ (ξ, γ, y)))) G1 := by
  have m0 : Measurable (fun γ' : Fin n → ℝ => (ξ, γ, γ')) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have m1 : Measurable (fun y : Fin n → ℝ => kappa (kappa (cosS β τ (ξ, γ, y)))) :=
    (continuous_kappa.comp continuous_kappa).measurable.comp
      ((measurable_cheapDot (n := n) β τ).comp m0)
  refine Integrable.mono' (integrable_const (1 : ℝ)) m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hs := abs_cheapDot_mem hn β τ (ξ, γ, y)
  have h1 := kappa_mem hs.1 hs.2
  have h2 := kappa_mem (t := kappa (cosS β τ (ξ, γ, y))) (by linarith [h1.1]) h1.2
  rw [Real.norm_eq_abs, abs_of_nonneg h2.1]
  exact h2.2

/-- The decomposition of `X(γ) − (m/n)(κ(κ(q)) + b·φ)` into three integrals over `γ′`. -/
lemma X_decomp (hn : 1 ≤ n) (β τ q b d : ℝ) (ξ γ : Fin n → ℝ) (θ : HidParam n m) (φ : ℝ) :
    (∫ y, (gramS β τ ((ξ, γ, y), θ) - d * kappa (kappa (cosS β τ (ξ, γ, y)))) ∂G1) +
      (∫ y, d * (kappa (kappa (cosS β τ (ξ, γ, y))) - kappa (kappa q) -
        b * (cosS β τ (ξ, γ, y) - q)) ∂G1) +
      d * b * ((∫ y, (cosS β τ (ξ, γ, y) - q) ∂G1) - φ) =
    (∑ j, hA (β • ξ) τ θ γ j * bbar (β • ξ) τ θ j) - d * (kappa (kappa q) + b * φ) := by
  obtain ⟨iG, eG⟩ := dot_hA_int hn (β • ξ) τ θ γ
  have h := int_decomp (μ := G1) (Gf := fun y : Fin n → ℝ => dotp (hA (β • ξ) τ θ γ)
    (hA (β • ξ) τ θ y)) (K := fun y : Fin n → ℝ => kappa (kappa (cosS β τ (ξ, γ, y))))
    (S := fun y : Fin n → ℝ => cosS β τ (ξ, γ, y) - q) iG (kk_cos_int hn β τ ξ γ)
    (cheapDot_int hn β τ q ξ γ) d (kappa (kappa q)) b φ
  exact h.trans (congrArg (fun t : ℝ => t - d * (kappa (kappa q) + b * φ)) eG)

/-- **`X − (m/n)(κ(κ(q)) + b·φ(ξ))` in `L²` over `(ξ, γ)` and the hidden weights.** -/
lemma fluct_L2 (hn : 1 ≤ n) (hm : 1 ≤ m) (β τ : ℝ) {q b c3 c4 : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4)
    (hquad : ∀ s ∈ Icc (-1 : ℝ) 1, 0 ≤ kappa (kappa s) - kappa (kappa q) - b * (s - q) ∧
      kappa (kappa s) - kappa (kappa q) - b * (s - q) ≤ 6 / 5 * (s - q) ^ 2)
    (c0 : L2le ((G1).prod G1) (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (∫ y, (cosS β τ (p.1, p.2, y) - q) ∂G1) - phi3 β τ p.1) c3)
    (c2 : L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => (cosS β τ w - q) ^ 2) c4) :
    L2le (((G1).prod G1).prod (hidGauss n m))
      (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        (∑ j, hA (β • p.1.1) τ p.2 p.1.2 j * bbar (β • p.1.1) τ p.2 j) -
          (m : ℝ) / n * (kappa (kappa q) + b * phi3 β τ p.1.1))
      ((m : ℝ) / n * (cF2o m + 1 / 2 * c3 + 6 / 5 * c4)) := by
  have hd : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
  have hF := (Part136.cF2o_pos hm).le
  have p1 : L2le (((G1).prod ((G1).prod G1)).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        gramS β τ z - (m : ℝ) / n * kappa (kappa (cosS β τ z.1)))
      ((m : ℝ) / n * cF2o m) := cheapGram_L2 hn hm β τ
  have p3 : L2le (((G1).prod ((G1).prod G1)).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        (m : ℝ) / n * (kappa (kappa (cosS β τ z.1)) - kappa (kappa q) - b * (cosS β τ z.1 - q)))
      ((m : ℝ) / n * (6 / 5 * c4)) :=
    ((remR_L2 hn β τ hquad c2).comp_fst (ν := hidGauss n m)).const_mul_nonneg hd
  have u1 := L2le_integral_third G1 G1 G1 (hidGauss n m) p1
  have u2 := L2le_integral_third G1 G1 G1 (hidGauss n m) p3
  have u3 : L2le (((G1).prod G1).prod (hidGauss n m))
      (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        (m : ℝ) / n * b * ((∫ y, (cosS β τ (p.1.1, p.1.2, y) - q) ∂G1) - phi3 β τ p.1.1))
      ((m : ℝ) / n * (1 / 2 * c3)) :=
    ((c0.comp_fst (ν := hidGauss n m)).const_mul_nonneg (mul_nonneg hd hb0)).mono
      (mul_nonneg (mul_nonneg hd hb0) hc3) (by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb1 hc3) hd
        linarith)
  have key := ((u1.add' u2 (mul_nonneg hd hF) (mul_nonneg hd (by positivity))).add' u3
    (add_nonneg (mul_nonneg hd hF) (mul_nonneg hd (by positivity)))
    (mul_nonneg hd (by positivity)))
  refine (key.congr_fun fun p => ?_).congr_bound (by ring)
  exact X_decomp hn β τ q b ((m : ℝ) / n) p.1.1 p.1.2 p.2 (phi3 β τ p.1.1)

/-- **The fluctuation of `X` is at most the mean square deviation from any constant.** -/
lemma errXc_le (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) (a : ℝ) :
    errXc c τ θ ≤ ∫ γ, ((∑ j, hA c τ θ γ j * bbar c τ θ j) - a) ^ 2 ∂G1 := by
  have bX : BM (fun γ : Fin n → ℝ => ∑ j, hA c τ θ γ j * bbar c τ θ j) :=
    bm_sum _ fun j => (bm_hA hn c τ θ j).mul (BM.const _)
  have e : normSq (bbar c τ θ) = ∫ γ, ∑ j, hA c τ θ γ j * bbar c τ θ j ∂G1 := by
    rw [integral_finsetSum _ fun j _ => ((bm_hA hn c τ θ j).mul (BM.const _)).integrable _]
    unfold normSq
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, sq]
    rfl
  unfold errXc
  rw [e]
  exact var_min bX a

/-! ## Joint measurability -/

lemma measurable_errXc {n m : ℕ} :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => errXc x.1.1 x.1.2 x.2) := by
  have mb : Measurable (fun z : (((Fin n → ℝ) × ℝ) × HidParam n m) × (Fin n → ℝ) =>
      bbar z.1.1.1 z.1.1.2 z.1.2) := measurable_bbar.comp measurable_fst
  have mf : Measurable (fun z : (((Fin n → ℝ) × ℝ) × HidParam n m) × (Fin n → ℝ) =>
      (∑ j, hA z.1.1.1 z.1.1.2 z.1.2 z.2 j * bbar z.1.1.1 z.1.1.2 z.1.2 j -
        normSq (bbar z.1.1.1 z.1.1.2 z.1.2)) ^ 2) :=
    ((Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp measurable_hA_joint).mul
        ((measurable_pi_apply j).comp mb)).sub
      (continuous_normSq.measurable.comp mb)).pow_const 2
  exact (mf.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

/-! ## From `L²` bounds to the means -/

/-- The passage of `errK_mean`, for any constant and any bound. -/
lemma errK_of_L2 {β τ a B : ℝ}
    (g : L2le (((G1).prod ((G1).prod G1)).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
          (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) - a) B) :
    ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal (errKc a (β • ξ) τ θ) ∂hidGauss n m) ∂G1 ≤
      ENNReal.ofReal (B ^ 2) := by
  obtain ⟨G, hG⟩ : ∃ G : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m → ENNReal,
      G = fun z => ENNReal.ofReal
        ((dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
          (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) - a) ^ 2) := ⟨_, rfl⟩
  have mG : Measurable G := by
    rw [hG]
    have m1 : Measurable (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1))) :=
      continuous_hid2_joint.measurable.comp
        (measurable_snd.prodMk ((measurable_cheapPt β τ).1.comp measurable_fst))
    have m2 : Measurable (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) :=
      continuous_hid2_joint.measurable.comp
        (measurable_snd.prodMk ((measurable_cheapPt β τ).2.comp measurable_fst))
    exact (((continuous_dotp.measurable.comp (m1.prodMk m2)).sub measurable_const).pow_const
      2).ennreal_ofReal
  have step : ∀ ξ : Fin n → ℝ, ∀ θ : HidParam n m,
      ENNReal.ofReal (errKc a (β • ξ) τ θ) ≤
        ∫⁻ p, G ((ξ, p), θ) ∂((G1).prod G1) := by
    intro ξ θ
    rw [hG]
    exact ofReal_integral_le _ _ fun _ => sq_nonneg _
  calc ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal (errKc a (β • ξ) τ θ) ∂hidGauss n m) ∂G1
      ≤ ∫⁻ ξ, (∫⁻ θ, ∫⁻ p, G ((ξ, p), θ) ∂((G1).prod G1) ∂hidGauss n m) ∂G1 :=
        lintegral_mono fun ξ => lintegral_mono fun θ => step ξ θ
    _ = ∫⁻ ξ, (∫⁻ p, ∫⁻ θ, G ((ξ, p), θ) ∂hidGauss n m ∂((G1).prod G1)) ∂G1 := by
        refine lintegral_congr fun ξ => ?_
        exact lintegral_lintegral_swap
          (f := fun (θ : HidParam n m) (p : (Fin n → ℝ) × (Fin n → ℝ)) => G ((ξ, p), θ))
          (mG.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    _ = ∫⁻ w, (∫⁻ θ, G (w, θ) ∂hidGauss n m) ∂((G1).prod ((G1).prod G1)) :=
        (lintegral_prod (fun w => ∫⁻ θ, G (w, θ) ∂hidGauss n m)
          mG.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ z, G z ∂(((G1).prod ((G1).prod G1)).prod (hidGauss n m)) :=
        (lintegral_prod _ mG.aemeasurable).symm
    _ = ENNReal.ofReal (∫ z, (dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
          (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) - a) ^ 2
          ∂(((G1).prod ((G1).prod G1)).prod (hidGauss n m))) := by
        rw [hG]
        exact (ofReal_integral_eq_lintegral_ofReal g.int_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal g.le

lemma measurable_Xsum (β τ : ℝ) :
    Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
      ∑ j, hA (β • p.1.1) τ p.2 p.1.2 j * bbar (β • p.1.1) τ p.2 j) := by
  have mc : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
      ((β • p.1.1, τ), p.2)) :=
    (((measurable_fst.comp measurable_fst).const_smul β).prodMk measurable_const).prodMk
      measurable_snd
  have e1 : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
      hA (β • p.1.1) τ p.2 p.1.2) :=
    measurable_hA_joint.comp (mc.prodMk (measurable_snd.comp measurable_fst))
  have e2 : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
      bbar (β • p.1.1) τ p.2) := measurable_bbar.comp mc
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp e1).mul ((measurable_pi_apply j).comp e2)

/-- The passage from an `L²` bound of `X − a(ξ)` to the mean of `errXc`. -/
lemma errX_of_L2 (hn : 1 ≤ n) {β τ B : ℝ} {a : (Fin n → ℝ) → ℝ} (ha : Measurable a)
    (g : L2le (((G1).prod G1).prod (hidGauss n m))
      (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        (∑ j, hA (β • p.1.1) τ p.2 p.1.2 j * bbar (β • p.1.1) τ p.2 j) - a p.1.1) B) :
    ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal (errXc (β • ξ) τ θ) ∂hidGauss n m) ∂G1 ≤
      ENNReal.ofReal (B ^ 2) := by
  obtain ⟨H, hH⟩ : ∃ H : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m → ENNReal,
      H = fun p => ENNReal.ofReal
        (((∑ j, hA (β • p.1.1) τ p.2 p.1.2 j * bbar (β • p.1.1) τ p.2 j) - a p.1.1) ^ 2) :=
    ⟨_, rfl⟩
  have mH : Measurable H := by
    rw [hH]
    exact (((measurable_Xsum β τ).sub
      (ha.comp (measurable_fst.comp measurable_fst))).pow_const 2).ennreal_ofReal
  have step : ∀ ξ : Fin n → ℝ, ∀ θ : HidParam n m,
      ENNReal.ofReal (errXc (β • ξ) τ θ) ≤ ∫⁻ γ, H ((ξ, γ), θ) ∂G1 := by
    intro ξ θ
    rw [hH]
    exact (ENNReal.ofReal_le_ofReal (errXc_le hn (β • ξ) τ θ (a ξ))).trans
      (ofReal_integral_le _ _ fun _ => sq_nonneg _)
  calc ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal (errXc (β • ξ) τ θ) ∂hidGauss n m) ∂G1
      ≤ ∫⁻ ξ, (∫⁻ θ, ∫⁻ γ, H ((ξ, γ), θ) ∂G1 ∂hidGauss n m) ∂G1 :=
        lintegral_mono fun ξ => lintegral_mono fun θ => step ξ θ
    _ = ∫⁻ ξ, (∫⁻ γ, ∫⁻ θ, H ((ξ, γ), θ) ∂hidGauss n m ∂G1) ∂G1 := by
        refine lintegral_congr fun ξ => ?_
        exact lintegral_lintegral_swap
          (f := fun (θ : HidParam n m) (γ : Fin n → ℝ) => H ((ξ, γ), θ))
          (mH.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    _ = ∫⁻ w, (∫⁻ θ, H (w, θ) ∂hidGauss n m) ∂((G1).prod G1) :=
        (lintegral_prod (fun w => ∫⁻ θ, H (w, θ) ∂hidGauss n m)
          mH.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ z, H z ∂(((G1).prod G1).prod (hidGauss n m)) :=
        (lintegral_prod _ mH.aemeasurable).symm
    _ = ENNReal.ofReal (∫ p : ((Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m,
          ((∑ j, hA (β • p.1.1) τ p.2 p.1.2 j * bbar (β • p.1.1) τ p.2 j) - a p.1.1) ^ 2
          ∂(((G1).prod G1).prod (hidGauss n m))) := by
        rw [hH]
        exact (ofReal_integral_eq_lintegral_ofReal g.int_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal g.le

/-! ## The two means -/

lemma window_nonneg {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) :
    0 ≤ 1 - q ^ 2 ∧ 0 ≤ q * (1 - q) ^ 2 * (1 - q / 2) := by
  refine ⟨by nlinarith, ?_⟩
  have h1 : 0 ≤ q := by linarith
  have h2 : 0 ≤ 1 - q / 2 := by linarith
  positivity

/-- **The mean of the kernel error, with the slope `1/2`**; `q = β²/(β² + τ²)` in the window. -/
theorem errK_mean2 (hn : 1 ≤ n) (hm : 1 ≤ m) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    (hq1 : 462 / 1000 ≤ β ^ 2 / (β ^ 2 + τ ^ 2)) (hq2 : β ^ 2 / (β ^ 2 + τ ^ 2) ≤ 527 / 1000) :
    ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal
        (errKc ((m : ℝ) / n * kappa (kappa (β ^ 2 / (β ^ 2 + τ ^ 2)))) (β • ξ) τ θ)
          ∂hidGauss n m) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (((m : ℝ) / n * dK2 n m (β ^ 2 / (β ^ 2 + τ ^ 2))) ^ 2) := by
  obtain ⟨b, hb0, hb1, hquad⟩ := kk_quad_at_sharp hq1 hq2
  have hc1 : 0 ≤ (1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) / √(n : ℝ) + jCosC n :=
    add_nonneg (div_nonneg (window_nonneg hq1 hq2).1 (Real.sqrt_nonneg _)) (jCosC_nonneg n)
  have hc4 : 0 ≤ m4c n (β ^ 2 / (β ^ 2 + τ ^ 2)) := Real.sqrt_nonneg _
  have key := kern2_L2 hn hm β τ (by linarith) hb1 hc1 hc4 hquad (cheapCos_L2 hn hβ hτ)
    (cheapCos_M4 hn hβ hτ)
  unfold dK2
  exact errK_of_L2 key

/-- **The mean of the fluctuation of `X(γ) = ⟨a₂(x(γ)), b̄⟩`**; `q = β²/(β² + τ²)` in the
window. -/
theorem errX_mean2 (hn : 1 ≤ n) (hm : 1 ≤ m) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    (hq1 : 462 / 1000 ≤ β ^ 2 / (β ^ 2 + τ ^ 2)) (hq2 : β ^ 2 / (β ^ 2 + τ ^ 2) ≤ 527 / 1000) :
    ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal (errXc (β • ξ) τ θ) ∂hidGauss n m) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (((m : ℝ) / n * dX2 n m (β ^ 2 / (β ^ 2 + τ ^ 2))) ^ 2) := by
  obtain ⟨b, hb0, hb1, hquad⟩ := kk_quad_at_sharp hq1 hq2
  have hc3 : 0 ≤ √(β ^ 2 / (β ^ 2 + τ ^ 2) * (1 - β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2 *
      (1 - β ^ 2 / (β ^ 2 + τ ^ 2) / 2) / (n : ℝ)) + jCosC n :=
    add_nonneg (Real.sqrt_nonneg _) (jCosC_nonneg n)
  have hc4 : 0 ≤ m4c n (β ^ 2 / (β ^ 2 + τ ^ 2)) := Real.sqrt_nonneg _
  have key := fluct_L2 hn hm β τ (by linarith) hb1 hc3 hc4 hquad (cheapCos3_L2 hn hβ hτ)
    (cheapCos_M4 hn hβ hτ)
  unfold dX2
  exact errX_of_L2 hn
    (a := fun ξ => (m : ℝ) / n * (kappa (kappa (β ^ 2 / (β ^ 2 + τ ^ 2))) + b * phi3 β τ ξ))
    (((measurable_phi3 β τ).const_mul b).const_add _ |>.const_mul _) key

/-! ## The numbers for `n ≥ 4096` and `m = mA n` -/

lemma num_basic {n : ℕ} (hn : 4096 ≤ n) :
    ∃ y z : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ 0 < y ∧ 0 < z ∧ y = z * z ∧
      cF2o (mA n) ≤ 4728 / 1000 * y ∧ jCosC n ≤ 4475 / 1000 * y := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), rfl, rfl, by positivity, by positivity, ?_, ?_, ?_⟩
  · rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  · have hm6 : 1000000 ≤ mA n := by unfold mA; nlinarith
    have h := cF2o_sq_le hm6
    rw [mA_eqR] at h
    have h0 := (Part136.cF2o_pos (m := mA n) (by omega)).le
    refine (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp ?_
    have e : 2235 / 100 / (n : ℝ) ^ 2 = 2235 / 100 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [e] at h
    have := sq_nonneg (1 / (n : ℝ))
    nlinarith
  · have := jCosC_le hn
    linarith [show (4475 : ℝ) / 1000 / n = 4475 / 1000 * (1 / n) by ring]

lemma m4c_window {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) :
    m4c n q ≤ 36639 / 10000 * (1 / (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  refine (m4c_le_q hn (by linarith) (by linarith)).trans ?_
  rw [div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine sqrt_le_of_sq (by norm_num) ?_
  have hq0 : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hq3 : 1 - q ^ 2 ≤ 786556 / 1000000 := by nlinarith
  have hb : (1 - q ^ 2) * (18617 / 10000) + 4195 / 10000 ≤ 18838313052 / 10000000000 := by
    linarith
  have h4 := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ (1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) hb 4
  norm_num at h4 ⊢
  linarith

/-- **`dK2 n (mA n) q ≤ 0.393278/√n + 11.363/n`** for `n ≥ 4096` and `q` in the window. -/
theorem dK2_le {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) :
    dK2 n (mA n) q ≤ 393278 / 1000000 / √(n : ℝ) + 11363 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hyz, hc, hj⟩ := num_basic hn
  have h4 := m4c_window hn hq1 hq2
  rw [← hy] at h4
  have h1 : (1 - q ^ 2) / √(n : ℝ) ≤ 786556 / 1000000 * z := by
    rw [hz, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have e : 393278 / 1000000 / √(n : ℝ) + 11363 / 1000 / (n : ℝ) =
      393278 / 1000000 * z + 11363 / 1000 * y := by rw [hy, hz]; ring
  unfold dK2
  rw [e]
  linarith

lemma fq_window {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) :
    q * (1 - q) ^ 2 * (1 - q / 2) ≤ (32068 / 100000) ^ 2 := by
  have h1 : 0 ≤ q - 462 / 1000 := by linarith
  have h2 : 0 ≤ 527 / 1000 - q := by linarith
  have h3 : 1 - 5 * q + 6 * q ^ 2 - 2 * q ^ 3 ≤ 0 := by
    nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h1) h1, mul_nonneg h1 h1]
  -- `f(q) − f(q₀) = (q − q₀)·(a polynomial that is ≤ 0)`
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h1) h1, mul_nonneg h1 h1,
    mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h1 h1), mul_nonneg h1 (neg_nonneg.mpr h3)]

/-- **`dX2 n (mA n) q ≤ 0.16034/√n + 11.363/n`** for `n ≥ 4096` and `q` in the window. -/
theorem dX2_le {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) :
    dX2 n (mA n) q ≤ 16034 / 100000 / √(n : ℝ) + 11363 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hyz, hc, hj⟩ := num_basic hn
  have h4 := m4c_window hn hq1 hq2
  rw [← hy] at h4
  have h1 : √(q * (1 - q) ^ 2 * (1 - q / 2) / (n : ℝ)) ≤ 32068 / 100000 * z := by
    refine sqrt_le_of_sq (by positivity) ?_
    have e : (32068 / 100000 * z) ^ 2 = (32068 / 100000) ^ 2 * y := by rw [hyz]; ring
    rw [e, div_eq_mul_one_div, ← hy]
    exact mul_le_mul_of_nonneg_right (fq_window hq1 hq2) hy0.le
  have e : 16034 / 100000 / √(n : ℝ) + 11363 / 1000 / (n : ℝ) =
      16034 / 100000 * z + 11363 / 1000 * y := by rw [hy, hz]; ring
  unfold dX2
  rw [e]
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms errK_mean2
open BstLean.Part149 in
#print axioms errX_mean2
open BstLean.Part149 in
#print axioms measurable_errXc
open BstLean.Part149 in
#print axioms dK2_le
open BstLean.Part149 in
#print axioms dX2_le
