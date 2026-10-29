import BstLean.Part108Defs

/-!
# Part 108: total variation for a change of the noise scale (`DrawsTV108`)

`Dens P T ρ c`: the image of `P` under `T` has the density `ρ ≥ 0` with respect to `P`, and
`∫ ρ² dP ≤ c`. It passes to products and to finite powers. For a probability measure it gives
`P(T ∈ B) ≤ P(B) + √(c − 1)`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-- The image of `P` under `T` has the density `ρ` with respect to `P`, and `∫ ρ² ≤ c`. -/
structure Dens {α : Type*} [MeasurableSpace α] (P : Measure α) (T : α → α) (ρ : α → ℝ) (c : ℝ) :
    Prop where
  measT : Measurable T
  measρ : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  chg : ∀ G : α → ℝ≥0∞, Measurable G →
    ∫⁻ x, G (T x) ∂P = ∫⁻ x, ENNReal.ofReal (ρ x) * G x ∂P
  sq : ∫⁻ x, ENNReal.ofReal (ρ x ^ 2) ∂P ≤ ENNReal.ofReal c

/-! ## One dimension -/

lemma pdf_ratio {s : ℝ} (hs : 0 < s) (x : ℝ) :
    gaussianPDFReal 0 1 x *
        (gaussianPDFReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s)) x / gaussianPDFReal 0 1 x) ^ 2 =
      (Real.sqrt (2 * Real.pi) * s ^ 2)⁻¹ * Real.exp (-(1 / s ^ 2 - 1 / 2) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_mk, sub_zero, NNReal.coe_one, mul_one]
  have h2 : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have ea : Real.sqrt (2 * Real.pi * s ^ 2) = Real.sqrt (2 * Real.pi) * s := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
  rw [ea]
  have he : Real.exp (-(1 / s ^ 2 - 1 / 2) * x ^ 2) =
      Real.exp (-x ^ 2 / (2 * s ^ 2)) ^ 2 / Real.exp (-x ^ 2 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    field_simp
    ring
  rw [he]
  have hp : 0 < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
  field_simp

lemma c1_eq {s : ℝ} (hs : 0 < s) (hs2 : s ^ 2 < 2) :
    (Real.sqrt (2 * Real.pi) * s ^ 2)⁻¹ * Real.sqrt (Real.pi / (1 / s ^ 2 - 1 / 2)) =
      (Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ := by
  have h2 : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hd : 0 < 2 - s ^ 2 := by linarith
  have hq : 0 < Real.sqrt (2 - s ^ 2) := Real.sqrt_pos.mpr hd
  have e1 : Real.pi / (1 / s ^ 2 - 1 / 2) = 2 * Real.pi * s ^ 2 / (2 - s ^ 2) := by
    field_simp
  have e2 : Real.sqrt (2 * Real.pi * s ^ 2 / (2 - s ^ 2)) =
      Real.sqrt (2 * Real.pi) * s / Real.sqrt (2 - s ^ 2) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
  have e3 : Real.sqrt (s ^ 2 * (2 - s ^ 2)) = s * Real.sqrt (2 - s ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
  rw [e1, e2, e3]
  field_simp

/-- The one-dimensional case: `c = (√(s²(2 − s²)))⁻¹`. -/
theorem dens_one {s : ℝ} (hs : 0 < s) (hs2 : s ^ 2 < 2) :
    Dens (gaussianReal 0 1) (fun x : ℝ => s * x)
      (fun x => gaussianPDFReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s)) x / gaussianPDFReal 0 1 x)
      (Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ := by
  have hv : NNReal.mk (s ^ 2) (sq_nonneg s) ≠ 0 := by
    intro h
    have := congrArg NNReal.toReal h
    simp only [NNReal.coe_mk, NNReal.coe_zero] at this
    exact (pow_pos hs 2).ne' this
  have h1 : (1 : NNReal) ≠ 0 := one_ne_zero
  have hρm : Measurable (fun x : ℝ =>
      gaussianPDFReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s)) x / gaussianPDFReal 0 1 x) :=
    (measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)
  have hρ0 : ∀ x : ℝ,
      0 ≤ gaussianPDFReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s)) x / gaussianPDFReal 0 1 x :=
    fun x => div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
  refine ⟨measurable_const_mul s, hρm, hρ0, ?_, ?_⟩
  · intro G hG
    have hm : Measurable (fun x : ℝ => s * x) := measurable_const_mul s
    rw [← lintegral_map hG hm, gaussianReal_map_const_mul]
    simp only [mul_one, mul_zero]
    rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ h1,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hG]
    symm
    refine (lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
        (hρm.ennreal_ofReal.mul hG)).trans ?_
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply, gaussianPDF_def]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 2
    have hp := gaussianPDFReal_pos 0 1 x h1
    field_simp
  · rw [gaussianReal_of_var_ne_zero _ h1]
    refine le_of_eq ((lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
        (hρm.pow_const 2).ennreal_ofReal).trans ?_)
    have e : ∀ x : ℝ, (gaussianPDF 0 1 * fun x =>
        ENNReal.ofReal ((gaussianPDFReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s)) x /
          gaussianPDFReal 0 1 x) ^ 2)) x =
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi) * s ^ 2)⁻¹ *
          Real.exp (-(1 / s ^ 2 - 1 / 2) * x ^ 2)) := by
      intro x
      simp only [Pi.mul_apply, gaussianPDF_def]
      rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), pdf_ratio hs]
    simp_rw [e]
    have hb : 0 < 1 / s ^ 2 - 1 / 2 := by
      have : 1 / 2 < 1 / s ^ 2 := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
        linarith
      linarith
    have hint : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi) * s ^ 2)⁻¹ *
        Real.exp (-(1 / s ^ 2 - 1 / 2) * x ^ 2)) := (integrable_exp_neg_mul_sq hb).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    rw [integral_const_mul]
    have hg := integral_gaussian (1 / s ^ 2 - 1 / 2)
    rw [hg, c1_eq hs hs2]

/-! ## Products and powers -/

section prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A factor that is not changed. -/
theorem Dens.prod_right (P₁ : Measure α) [IsProbabilityMeasure P₁] {P₂ : Measure β}
    [IsProbabilityMeasure P₂] {T : β → β} {ρ : β → ℝ} {c : ℝ} (h : Dens P₂ T ρ c) :
    Dens (P₁.prod P₂) (fun p : α × β => (p.1, T p.2)) (fun p => ρ p.2) c := by
  refine ⟨measurable_fst.prodMk (h.measT.comp measurable_snd), h.measρ.comp measurable_snd,
    fun p => h.nonneg _, ?_, ?_⟩
  · intro G hG
    rw [lintegral_prod (fun p : α × β => G (p.1, T p.2)) (hG.comp
        (measurable_fst.prodMk (h.measT.comp measurable_snd))).aemeasurable,
      lintegral_prod (fun p : α × β => ENNReal.ofReal (ρ p.2) * G p)
        (((h.measρ.comp measurable_snd).ennreal_ofReal).mul hG).aemeasurable]
    refine lintegral_congr fun a => ?_
    exact h.chg (fun b => G (a, b)) (hG.comp measurable_prodMk_left)
  · rw [lintegral_prod (fun p : α × β => ENNReal.ofReal (ρ p.2 ^ 2))
      ((h.measρ.comp measurable_snd).pow_const 2).ennreal_ofReal.aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact h.sq

end prod

section pi

universe u

variable {α : Type u} [MeasurableSpace α]

lemma measurable_cons' (k : ℕ) :
    Measurable (fun p : α × (Fin k → α) => (Fin.cons p.1 p.2 : Fin (k + 1) → α)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

/-- Split off the first coordinate of a finite power. -/
theorem pi_cons_lintegral (P : Measure α) [IsProbabilityMeasure P] (k : ℕ)
    (F : (Fin (k + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂Measure.pi (fun _ : Fin (k + 1) => P) =
      ∫⁻ a, ∫⁻ b, F (Fin.cons a b) ∂Measure.pi (fun _ : Fin k => P) ∂P := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) 0
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => P) 0
  have he : (∫⁻ p : α × (Fin k → α), F (Fin.cons p.1 p.2)
      ∂P.prod (Measure.pi (fun _ : Fin k => P))) =
        ∫⁻ x, F x ∂Measure.pi (fun _ : Fin (k + 1) => P) := by
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero] using
      hp.symm.lintegral_comp_emb e.symm.measurableEmbedding F
  rw [← he]
  exact lintegral_prod (fun p : α × (Fin k → α) => F (Fin.cons p.1 p.2))
    (hF.comp (measurable_cons' k)).aemeasurable

/-- Finite powers. -/
theorem Dens.pi {P : Measure α} [IsProbabilityMeasure P] {T : α → α} {ρ : α → ℝ} {c : ℝ}
    (h : Dens P T ρ c) (hc : 0 ≤ c) :
    ∀ k : ℕ, Dens (Measure.pi (fun _ : Fin k => P)) (fun x i => T (x i))
      (fun x => ∏ i, ρ (x i)) (c ^ k) := by
  intro k
  have hTm : ∀ k : ℕ, Measurable (fun (x : Fin k → α) i => T (x i)) := fun k =>
    measurable_pi_iff.mpr fun i => h.measT.comp (measurable_pi_apply i)
  have hρm : ∀ k : ℕ, Measurable (fun x : Fin k → α => ∏ i, ρ (x i)) := fun k =>
    Finset.measurable_prod _ fun i _ => h.measρ.comp (measurable_pi_apply i)
  induction k with
  | zero =>
    refine ⟨hTm 0, hρm 0, fun x => by simp, ?_, ?_⟩
    · intro G _
      have : ∀ x : Fin 0 → α, (fun i => T (x i)) = x := fun x => Subsingleton.elim _ _
      simp [this]
    · simp
  | succ k ih =>
    refine ⟨hTm (k + 1), hρm (k + 1), fun x => Finset.prod_nonneg fun i _ => h.nonneg _, ?_, ?_⟩
    · intro G hG
      have hcT : ∀ (a : α) (b : Fin k → α),
          (fun i => T ((Fin.cons a b : Fin (k + 1) → α) i)) =
            Fin.cons (T a) (fun i => T (b i)) := by
        intro a b
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [pi_cons_lintegral P k (fun x => G fun i => T (x i)) (hG.comp (hTm (k + 1))),
        pi_cons_lintegral P k (fun x => ENNReal.ofReal (∏ i, ρ (x i)) * G x)
          ((hρm (k + 1)).ennreal_ofReal.mul hG)]
      simp only [hcT]
      set H : α → ℝ≥0∞ := fun a' => ∫⁻ b, ENNReal.ofReal (∏ i, ρ (b i)) * G (Fin.cons a' b)
        ∂Measure.pi (fun _ : Fin k => P) with hH
      have hHm : Measurable H := by
        have : Measurable (fun p : α × (Fin k → α) =>
            ENNReal.ofReal (∏ i, ρ (p.2 i)) * G (Fin.cons p.1 p.2)) :=
          (((hρm k).comp measurable_snd).ennreal_ofReal).mul (hG.comp (measurable_cons' k))
        exact this.lintegral_prod_right'
      calc ∫⁻ a, ∫⁻ b, G (Fin.cons (T a) (fun i => T (b i))) ∂Measure.pi (fun _ : Fin k => P) ∂P
          = ∫⁻ a, H (T a) ∂P := by
            refine lintegral_congr fun a => ?_
            exact ih.chg (fun b => G (Fin.cons (T a) b))
              (hG.comp ((measurable_cons' k).comp measurable_prodMk_left))
        _ = ∫⁻ a, ENNReal.ofReal (ρ a) * H a ∂P := h.chg H hHm
        _ = _ := by
            refine lintegral_congr fun a => ?_
            rw [hH]
            simp only
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun b => ?_
            rw [Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [ENNReal.ofReal_mul (h.nonneg _), mul_assoc]
    · rw [pi_cons_lintegral P k (fun x => ENNReal.ofReal ((∏ i, ρ (x i)) ^ 2))
        ((hρm (k + 1)).pow_const 2).ennreal_ofReal]
      have e : ∀ (a : α) (b : Fin k → α),
          ENNReal.ofReal ((∏ i, ρ ((Fin.cons a b : Fin (k + 1) → α) i)) ^ 2) =
            ENNReal.ofReal (ρ a ^ 2) * ENNReal.ofReal ((∏ i, ρ (b i)) ^ 2) := by
        intro a b
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
      simp_rw [e]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_mul_const' _ _ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ih.sq)]
      rw [pow_succ, mul_comm (c ^ k) c, ENNReal.ofReal_mul hc]
      exact mul_le_mul' h.sq ih.sq

end pi

/-! ## The total variation bound -/

/-- If the image of the probability measure `P` under `T` has a density with `∫ ρ² ≤ c`, then
`P(T ∈ B) ≤ P(B) + √(c − 1)`. -/
theorem Dens.tv {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {T : α → α} {ρ : α → ℝ} {c : ℝ} (h : Dens P T ρ c) (hc : 0 ≤ c) {B : Set α}
    (hB : MeasurableSet B) :
    P.real (T ⁻¹' B) ≤ P.real B + Real.sqrt (c - 1) := by
  have hρ0 : ∀ᵐ x ∂P, 0 ≤ ρ x := Filter.Eventually.of_forall h.nonneg
  have hsq0 : ∀ᵐ x ∂P, 0 ≤ ρ x ^ 2 := Filter.Eventually.of_forall fun x => sq_nonneg _
  have hsqm : Measurable (fun x => ρ x ^ 2) := h.measρ.pow_const 2
  -- `ρ²` is integrable with integral at most `c`
  have isq : Integrable (fun x => ρ x ^ 2) P :=
    ⟨hsqm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hsq0).2 (lt_of_le_of_lt h.sq ENNReal.ofReal_lt_top)⟩
  have hsqc : ∫ x, ρ x ^ 2 ∂P ≤ c := by
    rw [integral_eq_lintegral_of_nonneg_ae hsq0 hsqm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hc h.sq
  -- `ρ` is integrable with integral `1`
  have iρ : Integrable ρ P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add isq) h.measρ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg x)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (ρ x - 1), h.nonneg x]
  have hρ1 : ∫ x, ρ x ∂P = 1 := by
    have h1 := h.chg (fun _ => 1) measurable_const
    simp only [lintegral_const, measure_univ, mul_one] at h1
    rw [integral_eq_lintegral_of_nonneg_ae hρ0 h.measρ.aestronglyMeasurable, ← h1]
    simp
  -- `P(T ∈ B) = ∫_B ρ`
  have hTB : P.real (T ⁻¹' B) = ∫ x, B.indicator ρ x ∂P := by
    have h1 := h.chg (B.indicator 1) (measurable_one.indicator hB)
    have e1 : ∫⁻ x, B.indicator (1 : α → ℝ≥0∞) (T x) ∂P = P (T ⁻¹' B) := by
      have : (fun x => B.indicator (1 : α → ℝ≥0∞) (T x)) = (T ⁻¹' B).indicator 1 := by
        funext x
        by_cases hx : T x ∈ B
        · have hx' : x ∈ T ⁻¹' B := hx
          simp [hx, hx']
        · have hx' : x ∉ T ⁻¹' B := hx
          simp [hx, hx']
      rw [this, lintegral_indicator_one (h.measT hB)]
    have e2 : ∀ x, ENNReal.ofReal (ρ x) * B.indicator (1 : α → ℝ≥0∞) x =
        ENNReal.ofReal (B.indicator ρ x) := by
      intro x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [e1] at h1
    simp_rw [e2] at h1
    rw [measureReal_def, h1, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun y _ => h.nonneg y) x)
      (h.measρ.indicator hB).aestronglyMeasurable]
  have hPB : P.real B = ∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂P := by
    rw [integral_indicator hB]
    simp
  -- the absolute deviation
  set m := ∫ x, |ρ x - 1| ∂P with hm
  have iabs : Integrable (fun x => |ρ x - 1|) P := (iρ.sub (integrable_const 1)).abs
  have hdiff : P.real (T ⁻¹' B) - P.real B ≤ m := by
    rw [hTB, hPB, ← integral_sub (iρ.indicator hB) ((integrable_const (1 : ℝ)).indicator hB)]
    refine integral_mono ((iρ.indicator hB).sub ((integrable_const (1 : ℝ)).indicator hB)) iabs
      fun x => ?_
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx]
      exact le_abs_self _
    · simp only [Set.indicator_of_notMem hx, sub_zero]
      exact abs_nonneg _
  have hV : ∫ x, (ρ x - 1) ^ 2 ∂P ≤ c - 1 := by
    have e : ∀ x, (ρ x - 1) ^ 2 = ρ x ^ 2 - 2 * ρ x + 1 := fun x => by ring
    simp_rw [e]
    rw [integral_add (f := fun x => ρ x ^ 2 - 2 * ρ x) (g := fun _ => (1 : ℝ))
        (isq.sub (iρ.const_mul 2)) (integrable_const _),
      integral_sub (f := fun x => ρ x ^ 2) (g := fun x => 2 * ρ x) isq (iρ.const_mul 2),
      integral_const_mul, hρ1]
    simp
    linarith
  have iV : Integrable (fun x => (ρ x - 1) ^ 2) P := by
    have e : (fun x => (ρ x - 1) ^ 2) = fun x => ρ x ^ 2 - 2 * ρ x + 1 := by
      funext x; ring
    rw [e]
    exact (isq.sub (iρ.const_mul 2)).add (integrable_const _)
  have hmsq : m ^ 2 ≤ ∫ x, (ρ x - 1) ^ 2 ∂P := by
    have h0 : 0 ≤ ∫ x, (|ρ x - 1| - m) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
    have e : ∀ x, (|ρ x - 1| - m) ^ 2 = (ρ x - 1) ^ 2 - 2 * m * |ρ x - 1| + m ^ 2 := by
      intro x
      have := sq_abs (ρ x - 1)
      nlinarith
    simp_rw [e] at h0
    rw [integral_add (f := fun x => (ρ x - 1) ^ 2 - 2 * m * |ρ x - 1|) (g := fun _ => m ^ 2)
        (iV.sub (iabs.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => (ρ x - 1) ^ 2) (g := fun x => 2 * m * |ρ x - 1|)
        iV (iabs.const_mul _), integral_const_mul, ← hm] at h0
    simp at h0
    nlinarith
  have hle : m ≤ Real.sqrt (c - 1) :=
    le_trans (le_abs_self m) (Real.abs_le_sqrt (hmsq.trans hV))
  linarith

/-! ## The blocks -/

theorem drawsTV108 : DrawsTV108 := by
  intro N n k hN Bad hBad s hs hs2
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hc1 : 0 ≤ (Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ := by positivity
  have d1 := dens_one hs hs2
  have dn := d1.pi hc1 n
  have dn' : Dens (stdGauss (Fin n)) (fun z : Fin n → ℝ => s • z) _ _ := dn
  have db := Dens.prod_right (uniformSphere N) dn'
  have dk := db.pi (pow_nonneg hc1 n) k
  have h := dk.tv (pow_nonneg (pow_nonneg hc1 n) k) hBad
  have e : (Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ ^ (k * n) =
      ((Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ ^ n) ^ k := by
    rw [← pow_mul, Nat.mul_comm n k]
  rw [e]
  exact h

end BstLean.Part108

#print axioms BstLean.Part108.drawsTV108
