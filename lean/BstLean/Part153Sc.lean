import BstLean.Part153Cen
import BstLean.Part150BF
import BstLean.Part150Gauss
import BstLean.Part150Bin
import BstLean.Part148Tools
import BstLean.Part130Layer
import BstLean.Part130Moments

/-!
# Part 153: the event `E_sc` (Lemma L1, part (b))

Paper source: `proofs/option-n/theorem5-06-centre.tex`, Lemma L1 (b).

`A₁ : m × n` is a Gaussian matrix with entry variance `2/n`; `c`, `τ ≥ 0` are fixed.
`s_h² = sO2 A₁ c τ = (2/m)·Σ_i v_i`, `v_i = Var_Z relu(μ_i + s_i Z) = vS s_i μ_i`.

* `phiG`, `PhiG`, `psiG`: the density `φ`, the distribution function `Φ(v) = Pr(Z > −v)` and
  `ψ₁(v) = vΦ(v) + φ(v)`; `psiS_one`: `psiS 1 v = psiG v`.
* `psiG_mul_le`: `ψ₁(a)·ψ₁(−a) ≤ 1/(2π)`.
* `Vr_add_ge`, `Vr_nonneg`, `Vr_le_one`: `V(a) + V(−a) ≥ 1 − 1/π`, `0 ≤ V(a) ≤ 1`.
* `sO2_mean`: `E s_h² ≥ 2(1 − 1/π)τ²`.
* `sO2_var`: `Var s_h² ≤ 16(1 + 2/n)τ⁴/m`.
* `Esc_prob_gen`, `Esc_prob`: Chebyshev; `Pr(s_h² < c_s τ²) ≤ 3445/n²` for `m = n²`, `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 BstLean.Part137 BstLean.Part150

noncomputable section

/-! ## The functions `φ`, `Φ`, `ψ₁` -/

/-- The standard Gaussian density `φ`. -/
def phiG (x : ℝ) : ℝ := (√(2 * π))⁻¹ * rexp (-(x ^ 2 / 2))

/-- `Φ(v) = Pr(Z > −v)` (`= Pr(Z < v)`), `Z` standard Gaussian. -/
def PhiG (v : ℝ) : ℝ := (gaussianReal 0 1).real (Ioi (-v))

/-- `ψ₁(v) = vΦ(v) + φ(v)`. -/
def psiG (v : ℝ) : ℝ := v * PhiG v + phiG v

lemma pdf_eq (x : ℝ) : gaussianPDFReal 0 1 x = phiG x := by
  simp only [gaussianPDFReal, phiG, NNReal.coe_one, mul_one, sub_zero]
  rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring]

lemma phiG_pos (x : ℝ) : 0 < phiG x := by unfold phiG; positivity

lemma phiG_neg (x : ℝ) : phiG (-x) = phiG x := by unfold phiG; rw [neg_sq]

lemma setInt_gauss (f : ℝ → ℝ) (c : ℝ) :
    ∫ z in Ioi c, f z ∂gaussianReal 0 1 = ∫ z in Ioi c, phiG z * f z := by
  rw [← integral_indicator measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul (by norm_num), ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Ioi c
  · simp only [indicator_of_mem hz, pdf_eq, smul_eq_mul]
  · simp only [indicator_of_notMem hz, smul_zero]

lemma expG_eq (z : ℝ) : rexp (-(1 / 2) * z ^ 2) = rexp (-(z ^ 2 / 2)) := by
  congr 1; ring

lemma integrable_phiG : Integrable phiG := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (√(2 * π))⁻¹
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [phiG, expG_eq]

lemma continuous_phiG : Continuous phiG := by unfold phiG; fun_prop

lemma PhiG_eq_int (v : ℝ) : PhiG v = ∫ z in Ioi (-v), phiG z := by
  have h := setInt_gauss (fun _ => (1 : ℝ)) (-v)
  rw [setIntegral_const] at h
  simp only [smul_eq_mul, mul_one] at h
  exact h

lemma PhiG_pos (v : ℝ) : 0 < PhiG v := by
  unfold PhiG
  rw [measureReal_def, ENNReal.toReal_pos_iff]
  refine ⟨?_, measure_lt_top _ _⟩
  rw [pos_iff_ne_zero]
  intro h
  have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h
  simp at h2

lemma PhiG_le_one (v : ℝ) : PhiG v ≤ 1 := measureReal_le_one

/-- `E[Z; Z > −v] = φ(v)`. -/
lemma int_z (v : ℝ) : ∫ z in Ioi (-v), z ∂gaussianReal 0 1 = phiG v := by
  rw [setInt_gauss (fun z => z) (-v)]
  have e : ∀ z : ℝ, phiG z * z = (√(2 * π))⁻¹ * (z * rexp (-(z ^ 2 / 2))) := by
    intro z; unfold phiG; ring
  simp_rw [e]
  rw [integral_const_mul, (integral_mul_exp_Ioi (-v)).2, neg_sq]
  rfl

lemma tendsto_mul_exp : Tendsto (fun t : ℝ => -(t * rexp (-(t ^ 2 / 2)))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t * rexp (-(t ^ 2 / 2))) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      positivity
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
      rw [pow_one]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
      nlinarith
  simpa using h0.neg

/-- `∫_c^∞ (z² − 1) e^{−z²/2} dz = c e^{−c²/2}`, with integrability. -/
lemma integral_sq_exp_Ioi (c : ℝ) :
    IntegrableOn (fun t : ℝ => (t ^ 2 - 1) * rexp (-(t ^ 2 / 2))) (Ioi c) ∧
      ∫ t in Ioi c, (t ^ 2 - 1) * rexp (-(t ^ 2 / 2)) = c * rexp (-(c ^ 2 / 2)) := by
  have hint : IntegrableOn (fun t : ℝ => (t ^ 2 - 1) * rexp (-(t ^ 2 / 2))) (Ioi c) := by
    have h2 := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2) (by norm_num)
    have h0 := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine ((h2.sub h0).congr (Eventually.of_forall fun t => ?_)).integrableOn
    simp only [Pi.sub_apply, expG_eq, Real.rpow_two]
    ring
  refine ⟨hint, ?_⟩
  have hd : ∀ x ∈ Ici c, HasDerivAt (fun t : ℝ => -(t * rexp (-(t ^ 2 / 2))))
      ((x ^ 2 - 1) * rexp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      convert this using 1; ring
    have h := ((hasDerivAt_id x).mul h1.exp).neg
    have e : -(1 * rexp (-(x ^ 2 / 2)) + id x * (rexp (-(x ^ 2 / 2)) * -x)) =
        (x ^ 2 - 1) * rexp (-(x ^ 2 / 2)) := by simp only [id]; ring
    rw [e] at h
    exact h
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint tendsto_mul_exp]
  ring

/-- `E[Z²; Z > −v] = Φ(v) − vφ(v)`. -/
lemma int_z2 (v : ℝ) : ∫ z in Ioi (-v), z ^ 2 ∂gaussianReal 0 1 = PhiG v - v * phiG v := by
  rw [setInt_gauss (fun z => z ^ 2) (-v), PhiG_eq_int]
  have e : ∀ z : ℝ, phiG z * z ^ 2 =
      phiG z + (√(2 * π))⁻¹ * ((z ^ 2 - 1) * rexp (-(z ^ 2 / 2))) := by
    intro z; unfold phiG; ring
  simp_rw [e]
  rw [integral_add integrable_phiG.integrableOn ((integral_sq_exp_Ioi (-v)).1.const_mul _),
    integral_const_mul, (integral_sq_exp_Ioi (-v)).2, neg_sq]
  unfold phiG
  ring

lemma intOn_id (S : Set ℝ) : IntegrableOn (fun z : ℝ => z) S (gaussianReal 0 1) := by
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  exact h1.integrableOn

/-- `ψ₁(v) = E relu(v + Z) = vΦ(v) + φ(v)`. -/
theorem psiS_one (v : ℝ) : psiS 1 v = psiG v := by
  unfold psiS psiG
  have e : (fun z : ℝ => relu (v + 1 * z)) = (Ioi (-v)).indicator (fun z => v + z) := by
    funext z
    by_cases hz : z ∈ Ioi (-v)
    · rw [indicator_of_mem hz, one_mul, relu_of_nonneg]
      have := mem_Ioi.mp hz
      linarith
    · rw [indicator_of_notMem hz, one_mul, relu_of_nonpos]
      have := not_lt.mp (fun h => hz (mem_Ioi.mpr h))
      linarith
  rw [e, integral_indicator measurableSet_Ioi,
    integral_add (integrable_const _).integrableOn (intOn_id _), setIntegral_const, int_z]
  simp only [smul_eq_mul, PhiG]
  ring

lemma psiG_nonneg (v : ℝ) : 0 ≤ psiG v := by rw [← psiS_one]; exact psiS_nonneg _ _

/-- `φ(v)·ψ₁(v) ≤ Φ(v)²` (the variance of `Z` given `Z > −v` is nonnegative). -/
lemma phi_psi_le (v : ℝ) : phiG v * psiG v ≤ PhiG v ^ 2 := by
  have hP := PhiG_pos v
  set S := Ioi (-v) with hS
  have h2 : IntegrableOn (fun z : ℝ => z ^ 2) S (gaussianReal 0 1) :=
    (integrable_pow_gauss 2).integrableOn
  have h1 := intOn_id S
  have hnn : 0 ≤ ∫ z in S, (PhiG v * z - phiG v) ^ 2 ∂gaussianReal 0 1 :=
    integral_nonneg fun z => sq_nonneg _
  have e : ∀ z : ℝ, (PhiG v * z - phiG v) ^ 2 =
      PhiG v ^ 2 * z ^ 2 + (-(2 * PhiG v * phiG v)) * z + phiG v ^ 2 := by
    intro z; ring
  simp_rw [e] at hnn
  have i2 : IntegrableOn (fun z : ℝ => PhiG v ^ 2 * z ^ 2) S (gaussianReal 0 1) := h2.const_mul _
  have i1 : IntegrableOn (fun z : ℝ => -(2 * PhiG v * phiG v) * z) S (gaussianReal 0 1) :=
    h1.const_mul _
  have i12 : IntegrableOn (fun z : ℝ => PhiG v ^ 2 * z ^ 2 + -(2 * PhiG v * phiG v) * z) S
      (gaussianReal 0 1) := i2.add i1
  rw [integral_add i12 (integrable_const _).integrableOn,
    integral_add i2 i1, integral_const_mul, integral_const_mul,
    setIntegral_const, int_z2, int_z] at hnn
  simp only [smul_eq_mul] at hnn
  have hΦ : (gaussianReal 0 1).real S = PhiG v := rfl
  rw [hΦ] at hnn
  have h3 : 0 ≤ PhiG v * (PhiG v ^ 2 - phiG v * psiG v) := by
    unfold psiG; nlinarith [hnn]
  have := nonneg_of_mul_nonneg_right h3 hP
  linarith

/-! ## Derivatives -/

lemma hasDerivAt_phiG (x : ℝ) : HasDerivAt phiG (-(x * phiG x)) x := by
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-x) x := by
    have := ((hasDerivAt_pow 2 x).div_const 2).neg
    convert this using 1; ring
  have h := (h1.exp).const_mul (√(2 * π))⁻¹
  have e : (√(2 * π))⁻¹ * (rexp (-(x ^ 2 / 2)) * -x) = -(x * phiG x) := by unfold phiG; ring
  rw [e] at h
  exact h

lemma PhiG_eq (v : ℝ) : PhiG v = PhiG 0 + ∫ z in (0 : ℝ)..v, phiG z := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi' (f := phiG) (a := -v) (b := -0)
    integrable_phiG.integrableOn integrable_phiG.integrableOn
  have h1 : ∫ x in (0 : ℝ)..v, phiG (-x) = ∫ x in -v..-0, phiG x :=
    intervalIntegral.integral_comp_neg _
  simp_rw [phiG_neg] at h1
  rw [PhiG_eq_int, PhiG_eq_int, h1]
  linarith

lemma hasDerivAt_PhiG (v : ℝ) : HasDerivAt PhiG (phiG v) v := by
  have h := (intervalIntegral.integral_hasStrictDerivAt_right
    (continuous_phiG.intervalIntegrable 0 v) (continuous_phiG.stronglyMeasurableAtFilter _ _)
    continuous_phiG.continuousAt).hasDerivAt
  have h2 := h.const_add (PhiG 0)
  have e : PhiG = fun u => PhiG 0 + ∫ z in (0 : ℝ)..u, phiG z := funext PhiG_eq
  rw [e]
  exact h2

lemma hasDerivAt_psiG (v : ℝ) : HasDerivAt psiG (PhiG v) v := by
  have h := ((hasDerivAt_id v).mul (hasDerivAt_PhiG v)).add (hasDerivAt_phiG v)
  have e : 1 * PhiG v + id v * phiG v + -(v * phiG v) = PhiG v := by simp only [id]; ring
  rw [e] at h
  exact h

/-- `m(v) = ψ₁(v)/Φ(v)` is increasing. -/
lemma mills_mono : Monotone (fun v => psiG v / PhiG v) := by
  have hd : ∀ v, HasDerivAt (fun v => psiG v / PhiG v)
      ((PhiG v * PhiG v - psiG v * phiG v) / PhiG v ^ 2) v :=
    fun v => (hasDerivAt_psiG v).div (hasDerivAt_PhiG v) (PhiG_pos v).ne'
  refine monotone_of_deriv_nonneg (fun v => (hd v).differentiableAt) fun v => ?_
  rw [(hd v).deriv]
  have := phi_psi_le v
  exact div_nonneg (by nlinarith) (sq_nonneg _)

/-- **`ψ₁(a)·ψ₁(−a) ≤ ψ₁(0)² = 1/(2π)`.** -/
theorem psiG_mul_le (a : ℝ) : psiG a * psiG (-a) ≤ 1 / (2 * π) := by
  have hd : ∀ a, HasDerivAt (fun a => psiG a * psiG (-a))
      (PhiG a * psiG (-a) + psiG a * (PhiG (-a) * -1)) a := by
    intro a
    have h1 : HasDerivAt (fun a => psiG (-a)) (PhiG (-a) * -1) a :=
      (hasDerivAt_psiG (-a)).comp a (hasDerivAt_neg a)
    exact (hasDerivAt_psiG a).mul h1
  have hanti : AntitoneOn (fun a => psiG a * psiG (-a)) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun a => (hd a).continuousAt).continuousOn
      (fun a _ => (hd a).differentiableAt.differentiableWithinAt) fun a ha => ?_
    rw [interior_Ici] at ha
    rw [(hd a).deriv]
    have hm := mills_mono (show -a ≤ a by have := mem_Ioi.mp ha; linarith)
    simp only at hm
    rw [div_le_div_iff₀ (PhiG_pos _) (PhiG_pos _)] at hm
    linarith
  have h0 : psiG 0 * psiG (-0) = 1 / (2 * π) := by
    simp only [neg_zero, psiG, zero_mul, zero_add, phiG]
    have hp : (0 : ℝ) < 2 * π := by positivity
    rw [show -((0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero, mul_one, ← mul_inv,
      Real.mul_self_sqrt hp.le, one_div]
  rcases le_total 0 a with ha | ha
  · have := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ha) ha
    simp only at this
    rw [h0] at this
    exact this
  · have := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr (neg_nonneg.mpr ha)) (neg_nonneg.mpr ha)
    simp only at this
    rw [h0, neg_neg, mul_comm] at this
    exact this

/-! ## The variance of `relu(x + sZ)` -/

/-- `v(s, x) = Var_Z relu(x + sZ)`, `Z` standard Gaussian. -/
def vS (s x : ℝ) : ℝ := ∫ z, relu (x + s * z) ^ 2 ∂gaussianReal 0 1 - psiS s x ^ 2

lemma vS_nonneg (s x : ℝ) : 0 ≤ vS s x := sub_nonneg.mpr (psiS_sq_le s x)

lemma gauss_neg_int {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ z, f (-z) ∂gaussianReal 0 1 = ∫ z, f z ∂gaussianReal 0 1 := by
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  conv_rhs => rw [← hneg]
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable]

/-- `ψ_s(−x) = ψ_s(x) − x`. -/
lemma psiS_neg (s x : ℝ) : psiS s (-x) = psiS s x - x := by
  rw [psiS_eq_abs, psiS_eq_abs]
  have h : ∫ z, |-x + s * z| ∂gaussianReal 0 1 = ∫ z, |x + s * z| ∂gaussianReal 0 1 := by
    rw [← gauss_neg_int (f := fun z => |x + s * z|)
      (by fun_prop : Continuous fun z : ℝ => |x + s * z|).measurable]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show |-x + s * z| = |x + s * -z|
    rw [← abs_neg]; congr 1; ring
  rw [h]; ring

/-- `E relu(x + sZ)² + E relu(−x + sZ)² = x² + s²`. -/
lemma m2_add (s x : ℝ) :
    ∫ z, relu (x + s * z) ^ 2 ∂gaussianReal 0 1 + ∫ z, relu (-x + s * z) ^ 2 ∂gaussianReal 0 1 =
      x ^ 2 + s ^ 2 := by
  have h : ∫ z, relu (-x + s * z) ^ 2 ∂gaussianReal 0 1 =
      ∫ z, relu (-(x + s * z)) ^ 2 ∂gaussianReal 0 1 := by
    rw [← gauss_neg_int (f := fun z => relu (-(x + s * z)) ^ 2)
      ((measurable_relu.comp (by fun_prop)).pow_const 2)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show relu (-x + s * z) ^ 2 = relu (-(x + s * -z)) ^ 2
    congr 2; ring
  have hi2 : Integrable (fun z : ℝ => relu (-(x + s * z)) ^ 2) (gaussianReal 0 1) := by
    have := integrable_relu_shift_sq (-x) (-s)
    refine this.congr (Eventually.of_forall fun z => ?_)
    show relu (-x + -s * z) ^ 2 = relu (-(x + s * z)) ^ 2
    congr 2; ring
  rw [h, ← integral_add (integrable_relu_shift_sq x s) hi2]
  have e : ∀ z : ℝ, relu (x + s * z) ^ 2 + relu (-(x + s * z)) ^ 2 =
      x ^ 2 + (2 * x * s) * z + s ^ 2 * z ^ 2 := by
    intro z; rw [relu_pow_add _ (by norm_num), sq_abs]; ring
  simp_rw [e]
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have h2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := integrable_pow_gauss 2
  have i0 : Integrable (fun _ : ℝ => x ^ 2) (gaussianReal 0 1) := integrable_const _
  have i1 : Integrable (fun z : ℝ => (2 * x * s) * z) (gaussianReal 0 1) := h1.const_mul _
  have i2 : Integrable (fun z : ℝ => s ^ 2 * z ^ 2) (gaussianReal 0 1) := h2.const_mul _
  have i01 : Integrable (fun z : ℝ => x ^ 2 + (2 * x * s) * z) (gaussianReal 0 1) := i0.add i1
  rw [integral_add i01 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    integral_id_gaussianReal, gaussMom_eq 2]
  norm_num [gaussMom]

lemma psiS_zero (x : ℝ) : psiS 0 x = relu x := by
  unfold psiS; simp

lemma psiS_scale {s : ℝ} (hs : 0 < s) (x : ℝ) : psiS s x = s * psiS 1 (x / s) := by
  unfold psiS
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show relu (x + s * z) = s * relu (x / s + 1 * z)
  rw [← relu_mul_of_nonneg hs.le]; congr 1; field_simp

/-- `ψ_s(x)·ψ_s(−x) ≤ s²/(2π)`. -/
lemma psiS_mul_le {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : psiS s x * psiS s (-x) ≤ s ^ 2 / (2 * π) := by
  rcases hs.eq_or_lt with h | h
  · subst h
    rw [psiS_zero, psiS_zero]
    have : relu x * relu (-x) = 0 := by
      rcases le_total 0 x with hx | hx
      · rw [relu_of_nonpos (by linarith : -x ≤ 0), mul_zero]
      · rw [relu_of_nonpos hx, zero_mul]
    rw [this]; simp
  · rw [psiS_scale h, psiS_scale h, neg_div, psiS_one, psiS_one]
    have := psiG_mul_le (x / s)
    have hs2 : 0 < s ^ 2 := by positivity
    calc s * psiG (x / s) * (s * psiG (-(x / s)))
        = s ^ 2 * (psiG (x / s) * psiG (-(x / s))) := by ring
      _ ≤ s ^ 2 * (1 / (2 * π)) := mul_le_mul_of_nonneg_left this hs2.le
      _ = s ^ 2 / (2 * π) := by ring

lemma vS_add (s x : ℝ) : vS s x + vS s (-x) = s ^ 2 - 2 * (psiS s x * psiS s (-x)) := by
  unfold vS
  have h := m2_add s x
  rw [psiS_neg]
  linear_combination h

/-- `v(s, x) + v(s, −x) ≥ (1 − 1/π)·s²`. -/
theorem vS_add_ge {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : (1 - 1 / π) * s ^ 2 ≤ vS s x + vS s (-x) := by
  have hπ := Real.pi_pos
  have h := psiS_mul_le hs x
  have e : (1 - 1 / π) * s ^ 2 = s ^ 2 - 2 * (s ^ 2 / (2 * π)) := by field_simp
  rw [vS_add, e]
  linarith

/-- `v(s, x) ≤ s²`. -/
theorem vS_le (s x : ℝ) : vS s x ≤ s ^ 2 := by
  have h := vS_add s x
  have h1 := vS_nonneg s (-x)
  have h2 := mul_nonneg (psiS_nonneg s x) (psiS_nonneg s (-x))
  linarith

/-! ## Item 1: the one-dimensional inequality -/

/-- `V(a) = Var relu(a + Z)`, `Z` standard Gaussian. -/
def Vr (a : ℝ) : ℝ :=
  ∫ z, relu (a + z) ^ 2 ∂gaussianReal 0 1 - (∫ z, relu (a + z) ∂gaussianReal 0 1) ^ 2

lemma Vr_eq (a : ℝ) : Vr a = vS 1 a := by
  unfold Vr vS psiS
  simp only [one_mul]

/-- **Item 1.** `V(a) + V(−a) ≥ 1 − 1/π`. -/
theorem Vr_add_ge (a : ℝ) : 1 - 1 / π ≤ Vr a + Vr (-a) := by
  have h := vS_add_ge (s := 1) zero_le_one a
  rw [Vr_eq, Vr_eq]
  linarith

/-- **Item 1.** `0 ≤ V(a)`. -/
theorem Vr_nonneg (a : ℝ) : 0 ≤ Vr a := by rw [Vr_eq]; exact vS_nonneg 1 a

/-- **Item 1.** `V(a) ≤ 1`. -/
theorem Vr_le_one (a : ℝ) : Vr a ≤ 1 := by
  have h := vS_le 1 a
  rw [Vr_eq]
  linarith

/-! ## The rows of `A₁` -/

variable {n m : ℕ}

/-- `v_i` as a function of row `i` of `A₁`: `Var_Z relu(⟨a, c⟩ + τ|a|·Z)`. -/
def rowV (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : ℝ :=
  vS (τ * √(∑ j, a j ^ 2)) (∑ j, a j * c j)

/-- `s_h² = (2/m)·Σ_i v_i`. -/
theorem sO2_rows (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    sO2 A₁ c τ = 2 / (m : ℝ) * ∑ i, rowV c τ (rowOf i A₁) := by
  have e : ∀ i, rowV c τ (rowOf i A₁) =
      ∫ z, relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2 ∂gaussianReal 0 1 - hO A₁ c τ i ^ 2 :=
    fun i => rfl
  simp_rw [e]
  unfold sO2 gO
  rw [Finset.sum_sub_distrib]
  ring

lemma measurable_vS : Measurable (fun p : ℝ × ℝ => vS p.1 p.2) := by
  have hF : Measurable (fun q : (ℝ × ℝ) × ℝ => relu (q.1.2 + q.1.1 * q.2) ^ 2) :=
    ((continuous_relu.comp (by fun_prop)).pow 2).measurable
  exact hF.stronglyMeasurable.integral_prod_right'.measurable.sub (measurable_psiS.pow_const 2)

lemma measurable_rowV (c : Fin n → ℝ) (τ : ℝ) : Measurable (rowV c τ) := by
  have h1 : Measurable (fun a : Fin n → ℝ => (τ * √(∑ j, a j ^ 2), ∑ j, a j * c j)) :=
    (by fun_prop : Continuous fun a : Fin n → ℝ => (τ * √(∑ j, a j ^ 2), ∑ j, a j * c j)).measurable
  exact measurable_vS.comp h1

lemma measurable_sO2 (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ) := by
  simp_rw [sO2_rows]
  exact (Finset.measurable_sum _ fun i _ =>
    (measurable_rowV c τ).comp (measurable_rowOf i)).const_mul _

lemma rowV_nonneg (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : 0 ≤ rowV c τ a := vS_nonneg _ _

lemma rowV_le (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) :
    rowV c τ a ≤ τ ^ 2 * normSq a := by
  have h := vS_le (τ * √(∑ j, a j ^ 2)) (∑ j, a j * c j)
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] at h
  exact h

lemma rowV_refl (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (a : Fin n → ℝ) :
    (1 - 1 / π) * (τ ^ 2 * normSq a) ≤ rowV c τ a + rowV c τ (-a) := by
  have h := vS_add_ge (mul_nonneg hτ (Real.sqrt_nonneg (∑ j, a j ^ 2))) (∑ j, a j * c j)
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] at h
  have e : rowV c τ (-a) = vS (τ * √(∑ j, a j ^ 2)) (-(∑ j, a j * c j)) := by
    unfold rowV
    simp only [Pi.neg_apply, neg_sq, neg_mul, Finset.sum_neg_distrib]
  rw [e]
  exact h

lemma sO2_le_fro (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    sO2 A₁ c τ ≤ 2 / (m : ℝ) * τ ^ 2 * froSq A₁ := by
  rw [sO2_rows, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold froSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => rowV_le c τ (rowOf i A₁)

lemma sO2_refl (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    2 / (m : ℝ) * (1 - 1 / π) * τ ^ 2 * froSq A₁ ≤ sO2 A₁ c τ + sO2 (-A₁) c τ := by
  rw [sO2_rows, sO2_rows, ← mul_add, ← Finset.sum_add_distrib]
  have e : 2 / (m : ℝ) * (1 - 1 / π) * τ ^ 2 * froSq A₁ =
      2 / (m : ℝ) * ((1 - 1 / π) * (τ ^ 2 * froSq A₁)) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold froSq
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => rowV_refl c hτ (rowOf i A₁)

/-! ## Item 2: the mean -/

/-- **Item 2.** `E s_h² ≥ 2(1 − 1/π)τ²`, with integrability. -/
theorem sO2_mean (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ) (gaussMat m n (2 / (n : ℝ))) ∧
    2 * (1 - 1 / π) * τ ^ 2 ≤
      ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat m n (2 / (n : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨iF, eF⟩ := froSq_integral (m := m) hn
  have mS := measurable_sO2 (m := m) c τ
  have iS : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ)
      (gaussMat m n (2 / (n : ℝ))) := by
    refine Integrable.mono' (iF.const_mul (2 / (m : ℝ) * τ ^ 2)) mS.aestronglyMeasurable
      (Eventually.of_forall fun A₁ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sO2_nonneg A₁ c τ)]
    exact sO2_le_fro c τ A₁
  refine ⟨iS, ?_⟩
  have mneg : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => -M) := measurable_neg
  have iSn : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 (-A₁) c τ)
      (gaussMat m n (2 / (n : ℝ))) := by
    have h1 : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ)
        ((gaussMat m n (2 / (n : ℝ))).map (fun M => -M)) := by rw [gaussMat_neg]; exact iS
    exact (integrable_map_measure mS.aestronglyMeasurable mneg.aemeasurable).mp h1
  have eSn : ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 (-A₁) c τ ∂gaussMat m n (2 / (n : ℝ)) =
      ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat m n (2 / (n : ℝ)) := by
    have h1 := integral_map (μ := gaussMat m n (2 / (n : ℝ))) mneg.aemeasurable
      mS.aestronglyMeasurable
    rw [gaussMat_neg] at h1
    exact h1.symm
  have h2 : ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, 2 / (m : ℝ) * (1 - 1 / π) * τ ^ 2 * froSq A₁
        ∂gaussMat m n (2 / (n : ℝ)) ≤
      ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, (sO2 A₁ c τ + sO2 (-A₁) c τ) ∂gaussMat m n (2 / (n : ℝ)) :=
    integral_mono (iF.const_mul _) (iS.add iSn) (fun A₁ => sO2_refl c hτ A₁)
  rw [integral_const_mul, eF, integral_add iS iSn, eSn] at h2
  have e : 2 / (m : ℝ) * (1 - 1 / π) * τ ^ 2 * (2 * m) = 4 * (1 - 1 / π) * τ ^ 2 := by
    field_simp
    ring
  linarith

/-! ## Item 3: the variance -/

/-- The distribution of one row of `A₁`: `√(2/n)` times a standard Gaussian vector. -/
def rowLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (stdGauss (Fin n)).map (fun ξ => √(2 / (n : ℝ)) • ξ)

instance (n : ℕ) : IsProbabilityMeasure (rowLaw n) := by unfold rowLaw; infer_instance

/-- `E|a|⁴ = (2/n)²·n(n + 2) = 4(1 + 2/n)` for a row `a`. -/
lemma rowLaw_four (hn : 1 ≤ n) :
    Integrable (fun a : Fin n → ℝ => normSq a ^ 2) (rowLaw n) ∧
    ∫ a, normSq a ^ 2 ∂rowLaw n = 4 * (1 + 2 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsm : Measurable (fun ξ : Fin n → ℝ => √(2 / (n : ℝ)) • ξ) := measurable_const_smul _
  have hg : Measurable (fun y : Fin n → ℝ => normSq y ^ 2) := measurable_normSq.pow_const 2
  have e : ∀ ξ : Fin n → ℝ, normSq (√(2 / (n : ℝ)) • ξ) ^ 2 =
      (2 / (n : ℝ)) ^ 2 * (∑ i, ξ i ^ 2) ^ 2 := by
    intro ξ
    rw [normSq_smul, Real.sq_sqrt (by positivity), mul_pow]
    rfl
  have i4 : Integrable (fun x : ℝ => (x ^ 2) ^ 2) (gaussianReal 0 1) := by
    simp_rw [sq_sq]; exact integrable_pow_gauss 4
  have iI : Integrable (fun ξ : Fin n → ℝ => normSq (√(2 / (n : ℝ)) • ξ) ^ 2)
      (stdGauss (Fin n)) := by
    simp_rw [e]
    exact (pi_sum_sq_integrable (integrable_pow_gauss 2) i4).const_mul _
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable hsm.aemeasurable).mpr iI, ?_⟩
  unfold rowLaw
  rw [integral_map hsm.aemeasurable hg.aestronglyMeasurable]
  simp_rw [e]
  rw [integral_const_mul]
  unfold stdGauss
  rw [pi_sum_sq (integrable_pow_gauss 2) i4]
  simp_rw [sq_sq]
  rw [gaussMom_eq, gaussMom_eq, Fintype.card_fin]
  have : Even 4 := by decide
  simp [gaussMom, this, Nat.doubleFactorial]
  field_simp
  ring

/-- **Item 3.** `Var s_h² ≤ 16(1 + 2/n)τ⁴/m` (the rows of `A₁` are independent). -/
theorem sO2_var (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) :
    MemLp (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ) 2 (gaussMat m n (2 / (n : ℝ))) ∧
    variance (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ) (gaussMat m n (2 / (n : ℝ))) ≤
      16 * (1 + 2 / (n : ℝ)) * τ ^ 4 / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have mf : Measurable (rowV c τ) := measurable_rowV c τ
  obtain ⟨i4, e4⟩ := rowLaw_four hn
  have hf2le : ∀ a, rowV c τ a ^ 2 ≤ τ ^ 4 * normSq a ^ 2 := by
    intro a
    calc rowV c τ a ^ 2 ≤ (τ ^ 2 * normSq a) ^ 2 :=
          pow_le_pow_left₀ (rowV_nonneg c τ a) (rowV_le c τ a) 2
      _ = τ ^ 4 * normSq a ^ 2 := by ring
  have if2 : Integrable (fun a => rowV c τ a ^ 2) (rowLaw n) := by
    refine Integrable.mono' (i4.const_mul (τ ^ 4)) (mf.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hf2le a
  have Lf : MemLp (rowV c τ) 2 (rowLaw n) :=
    (memLp_two_iff_integrable_sq mf.aestronglyMeasurable).mpr if2
  have ef2 : ∫ a, rowV c τ a ^ 2 ∂rowLaw n ≤ τ ^ 4 * (4 * (1 + 2 / (n : ℝ))) := by
    have := integral_mono if2 (i4.const_mul (τ ^ 4)) hf2le
    rwa [integral_const_mul, e4] at this
  -- the product measure of the rows
  obtain ⟨P, hP⟩ : ∃ P : Measure (Fin m → Fin n → ℝ), P = Measure.pi fun _ : Fin m => rowLaw n :=
    ⟨_, rfl⟩
  have hPp : IsProbabilityMeasure P := by rw [hP]; infer_instance
  obtain ⟨X, hX⟩ : ∃ X : Fin m → (Fin m → Fin n → ℝ) → ℝ, X = fun i ω => rowV c τ (ω i) :=
    ⟨_, rfl⟩
  have LX : ∀ i, MemLp (X i) 2 P := by
    intro i
    rw [hX, hP]
    exact Lf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => rowLaw n) i)
  have hind : iIndepFun X P := by
    rw [hX, hP]
    exact iIndepFun_pi (X := fun _ : Fin m => rowV c τ) (μ := fun _ : Fin m => rowLaw n)
      (fun _ => mf.aemeasurable)
  have hvs : variance (∑ i, X i) P = ∑ i, variance (X i) P :=
    IndepFun.variance_sum (fun i _ => LX i) (fun i _ j _ hij => hind.indepFun hij)
  have hvi : ∀ i, variance (X i) P ≤ τ ^ 4 * (4 * (1 + 2 / (n : ℝ))) := by
    intro i
    refine (variance_le_expectation_sq (LX i).aestronglyMeasurable).trans ?_
    have h1 : ∫ ω, (X i ^ 2) ω ∂P = ∫ a, rowV c τ a ^ 2 ∂rowLaw n := by
      rw [hX, hP]
      exact integral_comp_eval (μ := fun _ : Fin m => rowLaw n) (i := i)
        (f := fun a => rowV c τ a ^ 2) (mf.pow_const 2).aestronglyMeasurable
    rw [h1]
    exact ef2
  have Lg : MemLp (fun ω => 2 / (m : ℝ) * (∑ i, X i) ω) 2 P :=
    (memLp_finsetSum' _ fun i _ => LX i).const_mul _
  have hrows : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => fun i => rowOf i M) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  have hmap : (gaussMat m n (2 / (n : ℝ))).map (fun M i => rowOf i M) = P := by
    rw [hP]; exact BstLean.Part148.gaussMat_rows_map m n _
  have hcomp : (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ) =
      (fun ω => 2 / (m : ℝ) * (∑ i, X i) ω) ∘ (fun M i => rowOf i M) := by
    funext A₁
    rw [sO2_rows, hX]
    simp only [Function.comp_apply, Finset.sum_apply]
  have Lg' : MemLp (fun ω => 2 / (m : ℝ) * (∑ i, X i) ω) 2
      ((gaussMat m n (2 / (n : ℝ))).map (fun M i => rowOf i M)) := by rw [hmap]; exact Lg
  refine ⟨by rw [hcomp]; exact Lg'.comp_of_map hrows.aemeasurable, ?_⟩
  rw [hcomp, ← variance_map Lg'.aestronglyMeasurable.aemeasurable hrows.aemeasurable, hmap,
    variance_const_mul, hvs]
  calc (2 / (m : ℝ)) ^ 2 * ∑ i, variance (X i) P
      ≤ (2 / (m : ℝ)) ^ 2 * ∑ _i : Fin m, τ ^ 4 * (4 * (1 + 2 / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hvi i) (sq_nonneg _)
    _ = 16 * (1 + 2 / (n : ℝ)) * τ ^ 4 / m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        generalize 1 + 2 / (n : ℝ) = w
        field_simp
        ring

/-! ## Item 4: Chebyshev, the event `E_sc` -/

/-- **Item 4, general form.** `Pr(s_h² < 0.95·2(1 − 1/π)τ²) ≤
16(1 + 2/n)/(m·(1/20)²·(2(1 − 1/π))²)`. -/
theorem Esc_prob_gen (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (gaussMat m n (2 / (n : ℝ))).real
        {A₁ : Matrix (Fin m) (Fin n) ℝ | sO2 A₁ c τ < 0.95 * 2 * (1 - 1 / π) * τ ^ 2} ≤
      16 * (1 + 2 / (n : ℝ)) / (m * (1 / 20) ^ 2 * (2 * (1 - 1 / π)) ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hπ : (3 : ℝ) < π := Real.pi_gt_three
  have hq : 0 < 1 - 1 / π := by
    have : 1 / π < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  obtain ⟨iS, hmean⟩ := sO2_mean (m := m) hn hm c hτ.le
  obtain ⟨LS, hvar⟩ := sO2_var (m := m) hn hm c τ
  revert hmean hvar
  generalize 1 - 1 / π = q at hq ⊢
  intro hmean hvar
  obtain ⟨E0, hE0⟩ : ∃ E0 : ℝ, E0 = 2 * q * τ ^ 2 := ⟨_, rfl⟩
  have hE0pos : 0 < E0 := by rw [hE0]; positivity
  have hc0 : 0 < E0 / 20 := by positivity
  have hch := meas_ge_le_variance_div_sq LS hc0
  have hsub : {A₁ : Matrix (Fin m) (Fin n) ℝ | sO2 A₁ c τ < 0.95 * 2 * q * τ ^ 2} ⊆
      {A₁ | E0 / 20 ≤ |sO2 A₁ c τ -
        ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat m n (2 / (n : ℝ))|} := by
    intro A₁ hA
    simp only [Set.mem_ofPred_eq] at hA ⊢
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    rw [hE0]
    linarith
  have h1 : (gaussMat m n (2 / (n : ℝ))).real
      {A₁ : Matrix (Fin m) (Fin n) ℝ | sO2 A₁ c τ < 0.95 * 2 * q * τ ^ 2} ≤
      (ENNReal.ofReal (variance (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat m n (2 / (n : ℝ))) / (E0 / 20) ^ 2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hch)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at h1
  refine h1.trans ?_
  calc variance (fun A₁ : Matrix (Fin m) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat m n (2 / (n : ℝ))) / (E0 / 20) ^ 2
      ≤ (16 * (1 + 2 / (n : ℝ)) * τ ^ 4 / m) / (E0 / 20) ^ 2 :=
        div_le_div_of_nonneg_right hvar (by positivity)
    _ = 16 * (1 + 2 / (n : ℝ)) / (m * (1 / 20) ^ 2 * (2 * q) ^ 2) := by
        rw [hE0]
        generalize 1 + 2 / (n : ℝ) = w
        field_simp

/-- **Item 4 (Lemma L1 (b), the event `E_sc`).** For `m = m_A = n²`, `n ≥ 4096`, `τ > 0`:
`Pr(s_h² < c_s τ²) ≤ 3445/n²`, `c_s = 0.95·2(1 − 1/π)`. -/
theorem Esc_prob {n : ℕ} (hn : 4096 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
        {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 0.95 * 2 * (1 - 1 / π) * τ ^ 2} ≤
      3445 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  refine (Esc_prob_gen hn1 hm1 c hτ).trans ?_
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hmA]
  have hπ := Real.pi_gt_d6
  have hq : (0.68168 : ℝ) < 1 - 1 / π := by
    have h1 : 1 / π < 0.31832 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith
    linarith
  have hw : 1 + 2 / (n : ℝ) ≤ 1 + 2 / 4096 := by
    have : 2 / (n : ℝ) ≤ 2 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
    linarith
  revert hq hw
  generalize 1 - 1 / π = q
  generalize 1 + 2 / (n : ℝ) = w
  intro hq hw
  have hq0 : 0 < q := by linarith
  have hq2 : (0.68168 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.le 2
  have key : 16 * w ≤ 3445 * ((1 / 20) ^ 2 * (2 * q) ^ 2) := by
    have e : 3445 * ((1 / 20 : ℝ) ^ 2 * (2 * q) ^ 2) = 34.45 * q ^ 2 := by ring
    rw [e]
    norm_num at hq2 hw ⊢
    linarith
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hK : (0 : ℝ) < (n : ℝ) ^ 2 * (1 / 20) ^ 2 * (2 * q) ^ 2 := by positivity
  rw [div_le_div_iff₀ hK hn2]
  have := mul_le_mul_of_nonneg_left key hn2.le
  linarith

end

end BstLean.Part153

open BstLean.Part153 in
#print axioms psiG_mul_le
open BstLean.Part153 in
#print axioms Vr_add_ge
open BstLean.Part153 in
#print axioms Vr_nonneg
open BstLean.Part153 in
#print axioms Vr_le_one
open BstLean.Part153 in
#print axioms sO2_mean
open BstLean.Part153 in
#print axioms sO2_var
open BstLean.Part153 in
#print axioms Esc_prob_gen
open BstLean.Part153 in
#print axioms Esc_prob
