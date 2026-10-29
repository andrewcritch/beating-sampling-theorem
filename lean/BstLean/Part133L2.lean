import BstLean.Part132Final

/-!
# Part 133, tools: bounds of `L²` norms

Role: `delegations/statements/p133-spec.md`. This file holds the abstract `L²` tools of Part 133.

* `L2le μ f a`: `f` is in `L²(μ)` and `∫ f² dμ ≤ a²` (the `L²` norm of `f` is at most `a`).
* `L2le.add`, `L2le.sub`: the triangle inequality. `L2le.const_mul`, `L2le.mono`, `L2le.of_abs_le`.
* `L2le.prod`: from a bound of every section to a bound on a product measure (Fubini).
* `L2le.integral_right`, `L2le.integral_left`: the integral over one coordinate has a smaller
  `L²` norm (Jensen; this is `Var(P) ≤ Var(k)` for a conditional expectation `P` of `k`).
* `L2le.comp_map`, `L2le.comp_fst`, `L2le.comp_snd`: change of variables.
* `variance_le_of_L2le`: `Var f ≤ a²` if `‖f − c‖₂ ≤ a` for one constant `c`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `‖f‖_{L²(μ)} ≤ a`: `f` is measurable (a.e.), `f²` is integrable and `∫ f² dμ ≤ a²`. -/
def L2le (μ : Measure Ω) (f : Ω → ℝ) (a : ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ Integrable (fun ω => f ω ^ 2) μ ∧ ∫ ω, f ω ^ 2 ∂μ ≤ a ^ 2

namespace L2le

variable {f g : Ω → ℝ} {a b : ℝ}

lemma aesm (h : L2le μ f a) : AEStronglyMeasurable f μ := h.1
lemma int_sq (h : L2le μ f a) : Integrable (fun ω => f ω ^ 2) μ := h.2.1
lemma le (h : L2le μ f a) : ∫ ω, f ω ^ 2 ∂μ ≤ a ^ 2 := h.2.2

lemma mk' (hf : AEStronglyMeasurable f μ) (hi : Integrable (fun ω => f ω ^ 2) μ)
    (hle : ∫ ω, f ω ^ 2 ∂μ ≤ a ^ 2) : L2le μ f a := ⟨hf, hi, hle⟩

lemma mono (h : L2le μ f a) (ha : 0 ≤ a) (hab : a ≤ b) : L2le μ f b :=
  ⟨h.1, h.2.1, h.2.2.trans (pow_le_pow_left₀ ha hab 2)⟩

lemma congr_bound (h : L2le μ f a) (hab : a = b) : L2le μ f b := hab ▸ h

lemma congr_fun (h : L2le μ f a) (hfg : ∀ ω, f ω = g ω) : L2le μ g a := by
  have : f = g := funext hfg
  exact this ▸ h

/-- From a pointwise bound of the square. -/
lemma of_sq_le {G : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hG : Integrable G μ)
    (h : ∀ ω, f ω ^ 2 ≤ G ω) (hI : ∫ ω, G ω ∂μ ≤ a ^ 2) : L2le μ f a := by
  have hi : Integrable (fun ω => f ω ^ 2) μ := by
    refine Integrable.mono' hG (hf.pow 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h ω
  exact ⟨hf, hi, (integral_mono hi hG h).trans hI⟩

lemma of_abs_le (hf : AEStronglyMeasurable f μ) (hg : L2le μ g a) (h : ∀ ω, |f ω| ≤ |g ω|) :
    L2le μ f a :=
  of_sq_le hf hg.int_sq (fun ω => by
    have := h ω
    rw [← sq_abs (f ω), ← sq_abs (g ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2) hg.le

lemma neg (h : L2le μ f a) : L2le μ (fun ω => -f ω) a := by
  refine ⟨h.1.neg, ?_, ?_⟩
  · simpa using h.2.1
  · simpa using h.2.2

lemma const_mul (h : L2le μ f a) (c : ℝ) : L2le μ (fun ω => c * f ω) (|c| * a) := by
  refine ⟨h.1.const_mul c, ?_, ?_⟩
  · have := h.2.1.const_mul (c ^ 2)
    simpa [mul_pow] using this
  · have e : ∀ ω, (c * f ω) ^ 2 = c ^ 2 * f ω ^ 2 := fun ω => by ring
    simp only [e]
    rw [integral_const_mul, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left h.2.2 (sq_nonneg c)

lemma const_mul_nonneg (h : L2le μ f a) {c : ℝ} (hc : 0 ≤ c) :
    L2le μ (fun ω => c * f ω) (c * a) := by
  have := h.const_mul c
  rwa [abs_of_nonneg hc] at this

lemma sq_add_le {x y a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (x + y) ^ 2 ≤ (1 + b / a) * x ^ 2 + (1 + a / b) * y ^ 2 := by
  have e : (1 + b / a) * x ^ 2 + (1 + a / b) * y ^ 2 - (x + y) ^ 2 =
      (b * x - a * y) ^ 2 / (a * b) := by
    field_simp
    ring
  have : 0 ≤ (b * x - a * y) ^ 2 / (a * b) := by positivity
  linarith

/-- **The triangle inequality in `L²`.** -/
theorem add (hf : L2le μ f a) (hg : L2le μ g b) (ha : 0 < a) (hb : 0 < b) :
    L2le μ (fun ω => f ω + g ω) (a + b) := by
  have hG : Integrable (fun ω => (1 + b / a) * f ω ^ 2 + (1 + a / b) * g ω ^ 2) μ :=
    (hf.int_sq.const_mul _).add (hg.int_sq.const_mul _)
  refine of_sq_le (hf.1.add hg.1) hG (fun ω => sq_add_le ha hb) ?_
  rw [integral_add (hf.int_sq.const_mul _) (hg.int_sq.const_mul _), integral_const_mul,
    integral_const_mul]
  have h1 : (1 + b / a) * ∫ ω, f ω ^ 2 ∂μ ≤ (1 + b / a) * a ^ 2 :=
    mul_le_mul_of_nonneg_left hf.le (by positivity)
  have h2 : (1 + a / b) * ∫ ω, g ω ^ 2 ∂μ ≤ (1 + a / b) * b ^ 2 :=
    mul_le_mul_of_nonneg_left hg.le (by positivity)
  have e : (1 + b / a) * a ^ 2 + (1 + a / b) * b ^ 2 = (a + b) ^ 2 := by
    field_simp
    ring
  linarith

theorem sub (hf : L2le μ f a) (hg : L2le μ g b) (ha : 0 < a) (hb : 0 < b) :
    L2le μ (fun ω => f ω - g ω) (a + b) := by
  have := hf.add hg.neg ha hb
  exact this.congr_fun fun ω => by ring

/-- A constant function on a probability space. -/
lemma const [IsProbabilityMeasure μ] (c : ℝ) : L2le μ (fun _ => c) |c| := by
  refine ⟨aestronglyMeasurable_const, integrable_const _, ?_⟩
  simp

/-- A bounded function on a probability space. -/
lemma of_bound [IsProbabilityMeasure μ] (hf : AEStronglyMeasurable f μ) {c : ℝ}
    (h : ∀ ω, |f ω| ≤ c) : L2le μ f c :=
  of_sq_le hf (integrable_const (c ^ 2)) (fun ω => by
    rw [← sq_abs (f ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (h ω) 2) (by simp)

/-- Change of variables. -/
theorem comp_map {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {φ : Ω' → Ω}
    (hφ : Measurable φ) (hmap : P.map φ = μ) (h : L2le μ f a) :
    L2le P (fun ω => f (φ ω)) a := by
  subst hmap
  have h1 : AEStronglyMeasurable f (P.map φ) := h.1
  refine ⟨h1.comp_measurable hφ, ?_, ?_⟩
  · exact (integrable_map_measure (h1.pow 2) hφ.aemeasurable).1 h.2.1
  · have := integral_map hφ.aemeasurable (f := fun ω => f ω ^ 2) (h1.pow 2)
    rw [← this]
    exact h.2.2

end L2le

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- A function of the first coordinate. -/
theorem L2le.comp_fst [SFinite μ] [IsProbabilityMeasure ν] {f : α → ℝ} {a : ℝ} (h : L2le μ f a) :
    L2le (μ.prod ν) (fun z : α × β => f z.1) a :=
  h.comp_map measurable_fst (by simp [Measure.map_fst_prod])

/-- A function of the second coordinate. -/
theorem L2le.comp_snd [IsProbabilityMeasure μ] [SFinite ν] {f : β → ℝ} {a : ℝ} (h : L2le ν f a) :
    L2le (μ.prod ν) (fun z : α × β => f z.2) a :=
  h.comp_map measurable_snd (by simp [Measure.map_snd_prod])

/-- **Fubini for `L²` bounds.** If almost every section `y ↦ f (x, y)` has `L²(ν)` norm at most
`g x`, and `g` has `L²(μ)` norm at most `a`, then `f` has `L²(μ ⊗ ν)` norm at most `a`. -/
theorem L2le.prod [SFinite μ] [SFinite ν] {f : α × β → ℝ} {g : α → ℝ} {a : ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : L2le μ g a)
    (h : ∀ᵐ x ∂μ, Integrable (fun y => f (x, y) ^ 2) ν ∧ ∫ y, f (x, y) ^ 2 ∂ν ≤ g x ^ 2) :
    L2le (μ.prod ν) f a := by
  have hF : AEStronglyMeasurable (fun z : α × β => f z ^ 2) (μ.prod ν) := hf.pow 2
  have hdom : Integrable (fun x => ∫ y, ‖f (x, y) ^ 2‖ ∂ν) μ := by
    refine Integrable.mono' hg.int_sq hF.norm.integral_prod_right' ?_
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact hx.2
  have hi : Integrable (fun z : α × β => f z ^ 2) (μ.prod ν) :=
    (integrable_prod_iff hF).2 ⟨h.mono fun x hx => hx.1, hdom⟩
  refine ⟨hf, hi, ?_⟩
  rw [integral_prod _ hi]
  refine (integral_mono_ae hi.integral_prod_left hg.int_sq ?_).trans hg.le
  filter_upwards [h] with x hx using hx.2

/-- `L2le.prod` with sections stated by `L2le`. -/
theorem L2le.prod' [SFinite μ] [SFinite ν] {f : α × β → ℝ} {g : α → ℝ} {a : ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : L2le μ g a)
    (h : ∀ᵐ x ∂μ, L2le ν (fun y => f (x, y)) (g x)) : L2le (μ.prod ν) f a :=
  L2le.prod hf hg (h.mono fun _ hx => ⟨hx.int_sq, hx.le⟩)

/-- `L2le.prod` with one bound for all sections. -/
theorem L2le.prod_const [IsProbabilityMeasure μ] [SFinite ν] {f : α × β → ℝ} {a : ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (h : ∀ᵐ x ∂μ, L2le ν (fun y => f (x, y)) a) : L2le (μ.prod ν) f a := by
  have hc : L2le μ (fun _ : α => a) a :=
    ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
  exact L2le.prod' hf hc h

/-- `L2le.prod_const` for the sections in the first coordinate. -/
theorem L2le.prod_const_left [SFinite μ] [IsProbabilityMeasure ν] {f : α × β → ℝ} {a : ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (h : ∀ᵐ y ∂ν, L2le μ (fun x => f (x, y)) a) : L2le (μ.prod ν) f a := by
  have hf' : AEStronglyMeasurable (fun z : β × α => f z.swap) (ν.prod μ) := hf.prod_swap
  have h1 : L2le (ν.prod μ) (fun z : β × α => f z.swap) a := L2le.prod_const hf' h
  have := h1.comp_map (P := μ.prod ν) (φ := Prod.swap) measurable_swap Measure.prod_swap
  exact this.congr_fun fun z => by simp

lemma sq_integral_le {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {f : Ω → ℝ} (h2 : Integrable (fun ω => f ω ^ 2) ρ) :
    (∫ ω, f ω ∂ρ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂ρ := by
  by_cases h1 : Integrable f ρ
  · set c := ∫ ω, f ω ∂ρ with hc
    have h3 : Integrable (fun ω => (f ω - c) ^ 2) ρ := by
      have : (fun ω => (f ω - c) ^ 2) = fun ω => f ω ^ 2 - 2 * c * f ω + c ^ 2 := by
        funext ω; ring
      rw [this]
      exact (h2.sub (h1.const_mul _)).add (integrable_const _)
    have h4 : 0 ≤ ∫ ω, (f ω - c) ^ 2 ∂ρ := integral_nonneg fun ω => sq_nonneg _
    have h5 : ∫ ω, (f ω - c) ^ 2 ∂ρ = ∫ ω, f ω ^ 2 ∂ρ - c ^ 2 := by
      have : (fun ω => (f ω - c) ^ 2) = fun ω => f ω ^ 2 - 2 * c * f ω + c ^ 2 := by
        funext ω; ring
      have hA : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω) ρ := h2.sub (h1.const_mul _)
      have hB : Integrable (fun ω => 2 * c * f ω) ρ := h1.const_mul _
      rw [this, integral_add hA (integrable_const _), integral_sub h2 hB, integral_const_mul,
        ← hc]
      simp
      ring
    linarith
  · rw [integral_undef h1]
    simpa using integral_nonneg (μ := ρ) fun ω => sq_nonneg (f ω)

/-- **Jensen**: the integral over the second coordinate does not increase the `L²` norm. For a
kernel `k` and `P = E[k | first coordinate]` this is `‖P − c‖₂ ≤ ‖k − c‖₂`. -/
theorem L2le.integral_right [SFinite μ] [IsProbabilityMeasure ν] {f : α × β → ℝ} {a : ℝ}
    (h : L2le (μ.prod ν) f a) : L2le μ (fun x => ∫ y, f (x, y) ∂ν) a := by
  have hm : AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ := h.aesm.integral_prod_right'
  have hae : ∀ᵐ x ∂μ, Integrable (fun y => f (x, y) ^ 2) ν := h.int_sq.prod_right_ae
  have hpt : ∀ᵐ x ∂μ, (∫ y, f (x, y) ∂ν) ^ 2 ≤ ∫ y, f (x, y) ^ 2 ∂ν := by
    filter_upwards [hae] with x hx using sq_integral_le hx
  have hi : Integrable (fun x => (∫ y, f (x, y) ∂ν) ^ 2) μ := by
    refine Integrable.mono' h.int_sq.integral_prod_left (hm.pow 2) ?_
    filter_upwards [hpt] with x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hm, hi, ?_⟩
  refine (integral_mono_ae hi h.int_sq.integral_prod_left hpt).trans ?_
  rw [← integral_prod _ h.int_sq]
  exact h.le

/-- `L2le.integral_right` for the integral over the first coordinate. -/
theorem L2le.integral_left [IsProbabilityMeasure μ] [SFinite ν] {f : α × β → ℝ} {a : ℝ}
    (h : L2le (μ.prod ν) f a) : L2le ν (fun y => ∫ x, f (x, y) ∂μ) a := by
  have h1 : L2le (ν.prod μ) (fun z : β × α => f z.swap) a :=
    h.comp_map (P := ν.prod μ) (φ := Prod.swap) measurable_swap Measure.prod_swap
  exact h1.integral_right

end Prod

/-- `Var f ≤ a²` if `‖f − c‖₂ ≤ a` for one constant `c`. -/
theorem variance_le_of_L2le [IsProbabilityMeasure μ] {f : Ω → ℝ} {a c : ℝ}
    (h : L2le μ (fun ω => f ω - c) a) : Var[f; μ] ≤ a ^ 2 := by
  have hf : AEStronglyMeasurable f μ := by
    have := h.aesm.add (aestronglyMeasurable_const (b := c))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have h2 : MemLp (fun ω => f ω - c) 2 μ :=
    (memLp_two_iff_integrable_sq h.aesm).2 h.int_sq
  have hfm : MemLp f 2 μ := by
    have := h2.add (memLp_const c)
    refine this.ae_eq (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have hv : Var[f; μ] = Var[fun ω => f ω - c; μ] := by
    have := variance_sub_const (X := f) (μ := μ) hf c
    exact this.symm
  rw [hv, variance_eq_sub h2]
  have : 0 ≤ (∫ ω, (fun ω => f ω - c) ω ∂μ) ^ 2 := sq_nonneg _
  have h3 : ∫ ω, ((fun ω => f ω - c) ^ 2) ω ∂μ = ∫ ω, (f ω - c) ^ 2 ∂μ := rfl
  have := h.le
  simp only [Pi.pow_apply] at *
  linarith

end BstLean.Part133
