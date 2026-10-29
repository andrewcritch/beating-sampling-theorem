import BstLean.Part152GC
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Part 152 (file `SF`): the Sudakov–Fernique comparison inequality for finite families

Role: `delegations/statements/p152-spec.md`, optional item 4 (the operator norm of a Gaussian
matrix needs a comparison inequality).
-/

namespace BstLean.Part152

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology
open BstLean.Part29 (stdGauss)

/-! ## Gaussian integration by parts -/

/-- **Stein's identity on the line** for a bounded differentiable function with a bounded
derivative. -/
lemma stein1 {φ φ' : ℝ → ℝ} (hd : ∀ z, HasDerivAt φ (φ' z) z) {C : ℝ}
    (hb : ∀ z, |φ z| ≤ C) (hb' : ∀ z, |φ' z| ≤ C) :
    ∫ z, z * φ z ∂gaussianReal 0 1 = ∫ z, φ' z ∂gaussianReal 0 1 := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun z => (hd z).continuousAt
  have hφ'm : Measurable φ' := by
    have : φ' = deriv φ := funext fun z => (hd z).deriv.symm
    rw [this]
    exact measurable_deriv φ
  set ρ : ℝ → ℝ := fun z => (√(2 * π))⁻¹ * Real.exp (-(1 / 2) * z ^ 2) with hρ
  have hρe : ∀ z, gaussianPDFReal 0 1 z = ρ z := fun z => by
    simp only [gaussianPDFReal, hρ, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  have hρd : ∀ z, HasDerivAt ρ (-(z * ρ z)) z := by
    intro z
    have h1 : HasDerivAt (fun z : ℝ => -(1 / 2) * z ^ 2) (-(1 / 2) * (2 * z)) z := by
      have := (hasDerivAt_pow 2 z).const_mul (-(1 / 2) : ℝ)
      simpa using this
    have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
    convert h2 using 1
    simp only [hρ]
    ring
  have iρ : Integrable ρ := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  have izρ : Integrable (fun z => z * ρ z) := by
    have := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (√(2 * π))⁻¹
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [hρ]
    ring
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb 0)
  have i1 : Integrable (φ * fun z => -(z * ρ z)) := by
    refine Integrable.mono' (izρ.norm.const_mul C)
      (hφc.aestronglyMeasurable.mul izρ.neg.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    simp only [Pi.mul_apply, norm_mul, norm_neg, Real.norm_eq_abs]
    rw [← abs_mul]
    exact mul_le_mul_of_nonneg_right (hb z) (abs_nonneg _)
  have i2 : Integrable (φ' * ρ) := by
    refine Integrable.mono' (iρ.norm.const_mul C)
      (hφ'm.aestronglyMeasurable.mul iρ.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb' z) (abs_nonneg _)
  have i3 : Integrable (φ * ρ) := by
    refine Integrable.mono' (iρ.norm.const_mul C)
      (hφc.aestronglyMeasurable.mul iρ.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb z) (abs_nonneg _)
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := φ) (v := ρ) (u' := φ')
    (v' := fun z => -(z * ρ z)) (fun z _ => hd z) (fun z _ => hρd z) i1 i2 i3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [hρe, smul_eq_mul]
  have e1 : ∫ z, ρ z * (z * φ z) = -∫ z, φ z * -(z * ρ z) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  have e2 : ∫ z, ρ z * φ' z = ∫ z, φ' z * ρ z :=
    integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  rw [e1, e2, ibp, neg_neg]

lemma integrable_coord {κ : Type} [Fintype κ] (k : κ) :
    Integrable (fun ζ : κ → ℝ => ζ k) (stdGauss κ) := by
  unfold stdGauss
  exact integrable_comp_eval (μ := fun _ : κ => gaussianReal 0 1) (i := k) (f := id)
    ((memLp_id_gaussianReal 1).integrable le_rfl)

lemma integrable_dot {κ : Type} [Fintype κ] (c : κ → ℝ) :
    Integrable (fun ζ : κ → ℝ => c ⬝ᵥ ζ) (stdGauss κ) := by
  simp only [dotProduct]
  exact integrable_finsetSum _ fun k _ => (integrable_coord k).const_mul _

/-- **Stein's identity in one coordinate** of a standard Gaussian vector. -/
lemma stein_coord {n : ℕ} (k : Fin (n + 1)) {Φ Φ' : (Fin (n + 1) → ℝ) → ℝ}
    (hΦ : Measurable Φ) (hΦ' : Measurable Φ')
    (hd : ∀ ζ, HasDerivAt (fun t => Φ (Function.update ζ k t)) (Φ' ζ) (ζ k)) {C : ℝ}
    (hb : ∀ ζ, |Φ ζ| ≤ C) (hb' : ∀ ζ, |Φ' ζ| ≤ C) :
    ∫ ζ, ζ k * Φ ζ ∂stdGauss (Fin (n + 1)) = ∫ ζ, Φ' ζ ∂stdGauss (Fin (n + 1)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k with he
  have hp : MeasurePreserving e (stdGauss (Fin (n + 1)))
      ((gaussianReal 0 1).prod (stdGauss (Fin n))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) k
  have hps := hp.symm
  have hsym : ∀ (z : ℝ) (w : Fin n → ℝ), e.symm (z, w) = k.insertNth z w := fun z w => rfl
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb 0)
  have iG : Integrable (fun ζ => ζ k * Φ ζ) (stdGauss (Fin (n + 1))) := by
    refine Integrable.mono' ((integrable_coord k).norm.const_mul C)
      (((measurable_pi_apply k).mul hΦ).aestronglyMeasurable) (ae_of_all _ fun ζ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb ζ) (abs_nonneg _)
  have iG' : Integrable Φ' (stdGauss (Fin (n + 1))) :=
    Integrable.mono' (integrable_const C) hΦ'.aestronglyMeasurable (ae_of_all _ fun ζ => hb' ζ)
  have E1 := hps.integral_comp' (fun ζ => ζ k * Φ ζ)
  have E2 := hps.integral_comp' Φ'
  have iGp : Integrable (fun x => e.symm x k * Φ (e.symm x))
      ((gaussianReal 0 1).prod (stdGauss (Fin n))) :=
    (hps.integrable_comp_emb e.symm.measurableEmbedding).mpr iG
  have iGp' : Integrable (fun x => Φ' (e.symm x)) ((gaussianReal 0 1).prod (stdGauss (Fin n))) :=
    (hps.integrable_comp_emb e.symm.measurableEmbedding).mpr iG'
  rw [← E1, ← E2, integral_prod_symm _ iGp, integral_prod_symm _ iGp']
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [hsym, Fin.insertNth_apply_same]
  refine stein1 (φ := fun z => Φ (k.insertNth z w)) (φ' := fun z => Φ' (k.insertNth z w))
    (fun z => ?_) (fun z => hb _) (fun z => hb' _)
  have := hd (k.insertNth z w)
  simp only [Fin.update_insertNth, Fin.insertNth_apply_same] at this
  exact this

/-! ## The smooth maximum -/

section soft

variable {S : Type} [Fintype S] [Nonempty S]

/-- The smooth maximum `β⁻¹·log Σ_s exp(β z_s)`. -/
noncomputable def lse (β : ℝ) (z : S → ℝ) : ℝ := β⁻¹ * Real.log (∑ s, Real.exp (β * z s))

/-- The weights of the smooth maximum. -/
noncomputable def smx (β : ℝ) (z : S → ℝ) (s : S) : ℝ :=
  Real.exp (β * z s) / ∑ s', Real.exp (β * z s')

lemma sumexp_pos (β : ℝ) (z : S → ℝ) : 0 < ∑ s, Real.exp (β * z s) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma smx_nonneg (β : ℝ) (z : S → ℝ) (s : S) : 0 ≤ smx β z s :=
  div_nonneg (Real.exp_pos _).le (sumexp_pos β z).le

lemma smx_sum (β : ℝ) (z : S → ℝ) : ∑ s, smx β z s = 1 := by
  unfold smx
  rw [← Finset.sum_div, div_self (sumexp_pos β z).ne']

lemma smx_le_one (β : ℝ) (z : S → ℝ) (s : S) : smx β z s ≤ 1 := by
  rw [← smx_sum β z]
  exact Finset.single_le_sum (fun s _ => smx_nonneg β z s) (Finset.mem_univ s)

lemma lse_hasDerivAt (β : ℝ) {z : ℝ → S → ℝ} {z' : S → ℝ} {t : ℝ}
    (hz : ∀ s, HasDerivAt (fun t => z t s) (z' s) t) :
    HasDerivAt (fun t => lse β (z t)) (β⁻¹ * β * ∑ s, smx β (z t) s * z' s) t := by
  have h1 : ∀ s, HasDerivAt (fun t => Real.exp (β * z t s))
      (Real.exp (β * z t s) * (β * z' s)) t := fun s => ((hz s).const_mul β).exp
  have h2 : HasDerivAt (fun t => ∑ s, Real.exp (β * z t s))
      (∑ s, Real.exp (β * z t s) * (β * z' s)) t := HasDerivAt.fun_sum fun s _ => h1 s
  have h3 : HasDerivAt (fun t => lse β (z t)) _ t :=
    (h2.log (sumexp_pos β (z t)).ne').const_mul β⁻¹
  convert h3 using 1
  unfold smx
  rw [Finset.sum_div, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

lemma smx_hasDerivAt (β : ℝ) {z : ℝ → S → ℝ} {z' : S → ℝ} {t : ℝ}
    (hz : ∀ s, HasDerivAt (fun t => z t s) (z' s) t) (s : S) :
    HasDerivAt (fun t => smx β (z t) s)
      (β * (smx β (z t) s * z' s - smx β (z t) s * ∑ s', smx β (z t) s' * z' s')) t := by
  have h1 : ∀ s, HasDerivAt (fun t => Real.exp (β * z t s))
      (Real.exp (β * z t s) * (β * z' s)) t := fun s => ((hz s).const_mul β).exp
  have h2 : HasDerivAt (fun t => ∑ s, Real.exp (β * z t s))
      (∑ s, Real.exp (β * z t s) * (β * z' s)) t := HasDerivAt.fun_sum fun s _ => h1 s
  have h3 : HasDerivAt (fun t => smx β (z t) s) _ t := (h1 s).div h2 (sumexp_pos β (z t)).ne'
  convert h3 using 1
  have hT := (sumexp_pos β (z t)).ne'
  have eW1 : ∑ s', smx β (z t) s' * z' s' =
      (∑ s', Real.exp (β * z t s') * z' s') / ∑ s', Real.exp (β * z t s') := by
    unfold smx
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have eW2 : ∑ s', Real.exp (β * z t s') * (β * z' s') =
      β * ∑ s', Real.exp (β * z t s') * z' s' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [eW1, eW2]
  unfold smx
  field_simp

omit [Nonempty S] in
/-- `z_s ≤ lse β z`. -/
lemma le_lse {β : ℝ} (hβ : 0 < β) (z : S → ℝ) (s : S) : z s ≤ lse β z := by
  unfold lse
  have h : Real.exp (β * z s) ≤ ∑ s', Real.exp (β * z s') :=
    Finset.single_le_sum (f := fun s' => Real.exp (β * z s')) (fun _ _ => (Real.exp_pos _).le)
      (Finset.mem_univ s)
  have h2 := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp] at h2
  rw [← div_eq_inv_mul, le_div_iff₀ hβ]
  linarith

/-- `lse β z ≤ m + log(card S)/β` if `z_s ≤ m` for every `s`. -/
lemma lse_le {β : ℝ} (hβ : 0 < β) {z : S → ℝ} {m : ℝ} (hm : ∀ s, z s ≤ m) :
    lse β z ≤ m + Real.log (Fintype.card S) / β := by
  unfold lse
  have hN : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have h : ∑ s, Real.exp (β * z s) ≤ (Fintype.card S : ℝ) * Real.exp (β * m) := by
    have : ∑ s : S, Real.exp (β * z s) ≤ ∑ _s : S, Real.exp (β * m) :=
      Finset.sum_le_sum fun s _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm s) hβ.le)
    simpa using this
  have h2 := Real.log_le_log (sumexp_pos β z) h
  rw [Real.log_mul hN.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [← div_eq_inv_mul, div_le_iff₀ hβ]
  have : (m + Real.log (Fintype.card S) / β) * β = β * m + Real.log (Fintype.card S) := by
    field_simp
  linarith

omit [Nonempty S] in
/-- The sign of the quadratic form of the comparison. -/
lemma gram_nonneg {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) {m : S → S → ℝ}
    (hm : ∀ s s', 0 ≤ m s s + m s' s' - 2 * m s s') :
    0 ≤ ∑ s, p s * m s s - ∑ s, ∑ s', p s * p s' * m s s' := by
  have e1 : ∑ s, ∑ s', p s * p s' * m s s = ∑ s, p s * m s s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    have : ∑ s', p s * p s' * m s s = (p s * m s s) * ∑ s', p s' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [this, hs, mul_one]
  have e2 : ∑ s, ∑ s', p s * p s' * m s' s' = ∑ s, p s * m s s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : ∑ s', p s' * p s * m s s = (p s * m s s) * ∑ s', p s' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [this, hs, mul_one]
  have e : ∑ s, ∑ s', p s * p s' * (m s s + m s' s' - 2 * m s s') =
      2 * (∑ s, p s * m s s - ∑ s, ∑ s', p s * p s' * m s s') := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [e1, e2]
    have : ∑ s, ∑ s', p s * p s' * (2 * m s s') = 2 * ∑ s, ∑ s', p s * p s' * m s s' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [this]
    ring
  have h : 0 ≤ ∑ s, ∑ s', p s * p s' * (m s s + m s' s' - 2 * m s s') :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun s' _ =>
      mul_nonneg (mul_nonneg (hp s) (hp s')) (hm s s')
  linarith

end soft

/-! ## The comparison along the path `cos θ · a + sin θ · b` -/

section core

variable {S : Type} [Fintype S] [Nonempty S] {n : ℕ}

/-- The path of the coefficient vectors. -/
noncomputable def cpath (a b : S → Fin (n + 1) → ℝ) (θ : ℝ) (s : S) : Fin (n + 1) → ℝ :=
  fun k => Real.cos θ * a s k + Real.sin θ * b s k

/-- The derivative of the path. -/
noncomputable def cpath' (a b : S → Fin (n + 1) → ℝ) (θ : ℝ) (s : S) : Fin (n + 1) → ℝ :=
  fun k => -Real.sin θ * a s k + Real.cos θ * b s k

omit [Fintype S] [Nonempty S] in
lemma cpath_dot (a b : S → Fin (n + 1) → ℝ) (θ : ℝ) (s : S) (ζ : Fin (n + 1) → ℝ) :
    cpath a b θ s ⬝ᵥ ζ = Real.cos θ * (a s ⬝ᵥ ζ) + Real.sin θ * (b s ⬝ᵥ ζ) := by
  simp only [cpath, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Fintype S] [Nonempty S] in
lemma cpath'_dot (a b : S → Fin (n + 1) → ℝ) (θ : ℝ) (s : S) (ζ : Fin (n + 1) → ℝ) :
    cpath' a b θ s ⬝ᵥ ζ = -Real.sin θ * (a s ⬝ᵥ ζ) + Real.cos θ * (b s ⬝ᵥ ζ) := by
  simp only [cpath', dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma dot_update (c ζ : Fin (n + 1) → ℝ) (k : Fin (n + 1)) (t : ℝ) :
    c ⬝ᵥ Function.update ζ k t = c ⬝ᵥ ζ + c k * (t - ζ k) := by
  simp only [dotProduct]
  have : ∀ j, c j * Function.update ζ k t j =
      c j * ζ j + if j = k then c k * (t - ζ k) else 0 := by
    intro j
    by_cases h : j = k
    · subst h
      simp
      ring
    · simp [h]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma sq_dist_dot (x y : Fin (n + 1) → ℝ) :
    ∑ k, (x k - y k) ^ 2 = x ⬝ᵥ x + y ⬝ᵥ y - 2 * (x ⬝ᵥ y) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Fintype S] [Nonempty S] in
/-- The Gram matrix of the path and its derivative. -/
lemma cpath_gram (a b : S → Fin (n + 1) → ℝ) (horth : ∀ s s', a s ⬝ᵥ b s' = 0) (θ : ℝ)
    (s s' : S) :
    cpath' a b θ s ⬝ᵥ cpath a b θ s' =
      Real.sin θ * Real.cos θ * (b s ⬝ᵥ b s' - a s ⬝ᵥ a s') := by
  have h1 := horth s s'
  have h2 : b s ⬝ᵥ a s' = 0 := by rw [dotProduct_comm]; exact horth s' s
  have e : cpath' a b θ s ⬝ᵥ cpath a b θ s' =
      -Real.sin θ * Real.cos θ * (a s ⬝ᵥ a s') + -Real.sin θ * Real.sin θ * (a s ⬝ᵥ b s') +
        Real.cos θ * Real.cos θ * (b s ⬝ᵥ a s') + Real.cos θ * Real.sin θ * (b s ⬝ᵥ b s') := by
    simp only [cpath, cpath', dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, h1, h2]
  ring

/-- The positivity of the derivative along the path (Stein's identity). -/
lemma path_deriv_nonneg (a b : S → Fin (n + 1) → ℝ) (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hinc : ∀ s s', ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2) {β : ℝ} (hβ : 0 < β)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) :
    0 ≤ ∫ ζ, ∑ s, smx β (fun s => cpath a b θ s ⬝ᵥ ζ) s * (cpath' a b θ s ⬝ᵥ ζ)
      ∂stdGauss (Fin (n + 1)) := by
  set c := cpath a b θ with hc
  set c' := cpath' a b θ with hc'
  set p : (Fin (n + 1) → ℝ) → S → ℝ := fun ζ => smx β (fun s => c s ⬝ᵥ ζ) with hp
  set Φ' : S → Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ :=
    fun s k ζ => β * (p ζ s * c s k - p ζ s * ∑ s', p ζ s' * c s' k) with hΦ'
  have hpm : ∀ s, Measurable fun ζ => p ζ s := by
    intro s
    simp only [hp, smx, dotProduct]
    fun_prop
  have hΦ'm : ∀ s k, Measurable (Φ' s k) := by
    intro s k
    simp only [hΦ']
    have := hpm
    fun_prop
  have hp0 : ∀ ζ s, 0 ≤ p ζ s := fun ζ s => smx_nonneg _ _ _
  have hp1 : ∀ ζ s, p ζ s ≤ 1 := fun ζ s => smx_le_one _ _ _
  have hpabs : ∀ ζ s, |p ζ s| ≤ 1 := fun ζ s => by rw [abs_of_nonneg (hp0 ζ s)]; exact hp1 ζ s
  -- Stein's identity for each pair `(s, k)`
  have hst : ∀ s k, ∫ ζ, ζ k * p ζ s ∂stdGauss (Fin (n + 1)) =
      ∫ ζ, Φ' s k ζ ∂stdGauss (Fin (n + 1)) := by
    intro s k
    refine stein_coord k (hpm s) (hΦ'm s k) (fun ζ => ?_)
      (C := 1 + β * (|c s k| + ∑ s', |c s' k|)) (fun ζ => ?_) (fun ζ => ?_)
    · have hz : ∀ s', HasDerivAt (fun t => c s' ⬝ᵥ Function.update ζ k t) (c s' k) (ζ k) := by
        intro s'
        have h := ((hasDerivAt_id (ζ k)).sub_const (ζ k)).const_mul (c s' k) |>.const_add (c s' ⬝ᵥ ζ)
        simp only [mul_one] at h
        refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        simp only [id]
        exact dot_update _ _ _ _
      have h := smx_hasDerivAt β (z := fun t s' => c s' ⬝ᵥ Function.update ζ k t)
        (z' := fun s' => c s' k) (t := ζ k) hz s
      simp only [Function.update_eq_self] at h
      exact h
    · have hsum : 0 ≤ β * (|c s k| + ∑ s', |c s' k|) :=
        mul_nonneg hβ.le (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      linarith [hpabs ζ s]
    · simp only [hΦ']
      rw [abs_mul, abs_of_pos hβ]
      have h1 : |p ζ s * c s k - p ζ s * ∑ s', p ζ s' * c s' k| ≤ |c s k| + ∑ s', |c s' k| := by
        have t1 : |p ζ s * c s k| ≤ |c s k| := by
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hpabs ζ s)
        have t2 : |p ζ s * ∑ s', p ζ s' * c s' k| ≤ ∑ s', |c s' k| := by
          rw [abs_mul]
          have t3 : |∑ s', p ζ s' * c s' k| ≤ ∑ s', |c s' k| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => by
              rw [abs_mul]
              exact mul_le_of_le_one_left (abs_nonneg _) (hpabs ζ s'))
          calc |p ζ s| * |∑ s', p ζ s' * c s' k| ≤ 1 * ∑ s', |c s' k| :=
            mul_le_mul (hpabs ζ s) t3 (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        exact (abs_sub _ _).trans (add_le_add t1 t2)
      nlinarith [mul_le_mul_of_nonneg_left h1 hβ.le]
  -- integrability
  have i1 : ∀ s k, Integrable (fun ζ => ζ k * p ζ s) (stdGauss (Fin (n + 1))) := by
    intro s k
    refine Integrable.mono' (integrable_coord k).norm
      (((measurable_pi_apply k).mul (hpm s)).aestronglyMeasurable) (ae_of_all _ fun ζ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hpabs ζ s)
  have i2 : ∀ s k, Integrable (Φ' s k) (stdGauss (Fin (n + 1))) := by
    intro s k
    refine Integrable.mono' (integrable_const (β * (|c s k| + ∑ s', |c s' k|)))
      (hΦ'm s k).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    simp only [hΦ']
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    have t1 : |p ζ s * c s k| ≤ |c s k| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hpabs ζ s)
    have t2 : |p ζ s * ∑ s', p ζ s' * c s' k| ≤ ∑ s', |c s' k| := by
      rw [abs_mul]
      have t3 : |∑ s', p ζ s' * c s' k| ≤ ∑ s', |c s' k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => by
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hpabs ζ s'))
      calc |p ζ s| * |∑ s', p ζ s' * c s' k| ≤ 1 * ∑ s', |c s' k| :=
        mul_le_mul (hpabs ζ s) t3 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    exact (abs_sub _ _).trans (add_le_add t1 t2)
  -- the integral as the integral of the quadratic form
  have e1 : ∫ ζ, ∑ s, p ζ s * (c' s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) =
      ∫ ζ, ∑ s, ∑ k, c' s k * Φ' s k ζ ∂stdGauss (Fin (n + 1)) := by
    have l1 : ∀ ζ, ∑ s, p ζ s * (c' s ⬝ᵥ ζ) = ∑ s, ∑ k, c' s k * (ζ k * p ζ s) := by
      intro ζ
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [l1]
    rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun k _ => (i1 s k).const_mul _,
      integral_finsetSum _ fun s _ => integrable_finsetSum _ fun k _ => (i2 s k).const_mul _]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_finsetSum _ fun k _ => (i1 s k).const_mul _,
      integral_finsetSum _ fun k _ => (i2 s k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_const_mul, hst s k]
  rw [e1]
  refine integral_nonneg fun ζ => ?_
  -- the pointwise sign
  set m : S → S → ℝ := fun s s' => c' s ⬝ᵥ c s' with hm
  have per : ∀ s, ∑ k, c' s k * Φ' s k ζ =
      β * (p ζ s * m s s - ∑ s', p ζ s * p ζ s' * m s s') := by
    intro s
    have l2 : ∑ s', p ζ s * p ζ s' * m s s' = ∑ k, c' s k * (p ζ s * ∑ s', p ζ s' * c s' k) := by
      simp only [hm, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s' _ => by ring
    rw [l2]
    simp only [hΦ', hm, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [← Finset.mul_sum]
    ring
  simp_rw [per]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  refine mul_nonneg hβ.le ?_
  refine gram_nonneg (hp0 ζ) (smx_sum _ _) fun s s' => ?_
  simp only [hm, hc, hc', cpath_gram a b horth]
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hi := hinc s s'
  rw [sq_dist_dot, sq_dist_dot] at hi
  have : Real.sin θ * Real.cos θ * (b s ⬝ᵥ b s - a s ⬝ᵥ a s) +
      Real.sin θ * Real.cos θ * (b s' ⬝ᵥ b s' - a s' ⬝ᵥ a s') -
      2 * (Real.sin θ * Real.cos θ * (b s ⬝ᵥ b s' - a s ⬝ᵥ a s')) =
      Real.sin θ * Real.cos θ * ((b s ⬝ᵥ b s + b s' ⬝ᵥ b s' - 2 * (b s ⬝ᵥ b s')) -
        (a s ⬝ᵥ a s + a s' ⬝ᵥ a s' - 2 * (a s ⬝ᵥ a s'))) := by ring
  rw [this]
  exact mul_nonneg (mul_nonneg hs0 hc0) (by linarith)

omit [Nonempty S] in
lemma abs_dot_le_sum (c : S → Fin (n + 1) → ℝ) (ζ : Fin (n + 1) → ℝ) (s : S) :
    |c s ⬝ᵥ ζ| ≤ ∑ s, |c s ⬝ᵥ ζ| :=
  Finset.single_le_sum (f := fun s => |c s ⬝ᵥ ζ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

lemma lse_abs_le {β : ℝ} (hβ : 0 < β) (c : S → Fin (n + 1) → ℝ) (ζ : Fin (n + 1) → ℝ) :
    |lse β (fun s => c s ⬝ᵥ ζ)| ≤ ∑ s, |c s ⬝ᵥ ζ| + Real.log (Fintype.card S) / β := by
  have hN : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card S) / β := div_nonneg (Real.log_nonneg hN) hβ.le
  obtain ⟨s0⟩ := ‹Nonempty S›
  have h1 := le_lse hβ (fun s => c s ⬝ᵥ ζ) s0
  have h2 := lse_le hβ (z := fun s => c s ⬝ᵥ ζ) (m := ∑ s, |c s ⬝ᵥ ζ|)
    (fun s => (le_abs_self _).trans (abs_dot_le_sum c ζ s))
  have h3 := abs_dot_le_sum c ζ s0
  have h4 := neg_abs_le (c s0 ⬝ᵥ ζ)
  rw [abs_le]
  constructor <;> linarith

omit [Nonempty S] in
lemma lse_measurable (β : ℝ) (c : S → Fin (n + 1) → ℝ) :
    Measurable fun ζ : Fin (n + 1) → ℝ => lse β (fun s => c s ⬝ᵥ ζ) := by
  simp only [lse, dotProduct]
  fun_prop

omit [Nonempty S] in
lemma sumabs_integrable (c : S → Fin (n + 1) → ℝ) :
    Integrable (fun ζ : Fin (n + 1) → ℝ => ∑ s, |c s ⬝ᵥ ζ|) (stdGauss (Fin (n + 1))) :=
  integrable_finsetSum _ fun s _ => (integrable_dot (c s)).abs

lemma lse_integrable {β : ℝ} (hβ : 0 < β) (c : S → Fin (n + 1) → ℝ) :
    Integrable (fun ζ : Fin (n + 1) → ℝ => lse β (fun s => c s ⬝ᵥ ζ)) (stdGauss (Fin (n + 1))) :=
  Integrable.mono' ((sumabs_integrable c).add (integrable_const _))
    (lse_measurable β c).aestronglyMeasurable (ae_of_all _ fun ζ => lse_abs_le hβ c ζ)

/-- The comparison for the smooth maximum. -/
lemma sf_step (a b : S → Fin (n + 1) → ℝ) (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hinc : ∀ s s', ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2) {β : ℝ} (hβ : 0 < β) :
    ∫ ζ, lse β (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) ≤
      ∫ ζ, lse β (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) := by
  set F : ℝ → (Fin (n + 1) → ℝ) → ℝ := fun θ ζ => lse β (fun s => cpath a b θ s ⬝ᵥ ζ) with hF
  set D : ℝ → (Fin (n + 1) → ℝ) → ℝ :=
    fun θ ζ => ∑ s, smx β (fun s => cpath a b θ s ⬝ᵥ ζ) s * (cpath' a b θ s ⬝ᵥ ζ) with hD
  set bnd : (Fin (n + 1) → ℝ) → ℝ := fun ζ => ∑ s, (|a s ⬝ᵥ ζ| + |b s ⬝ᵥ ζ|) with hbnd
  have hFd : ∀ ζ θ, HasDerivAt (fun θ => F θ ζ) (D θ ζ) θ := by
    intro ζ θ
    have hz : ∀ s, HasDerivAt (fun θ => cpath a b θ s ⬝ᵥ ζ) (cpath' a b θ s ⬝ᵥ ζ) θ := by
      intro s
      simp only [cpath_dot, cpath'_dot]
      have := ((Real.hasDerivAt_cos θ).mul_const (a s ⬝ᵥ ζ)).add
        ((Real.hasDerivAt_sin θ).mul_const (b s ⬝ᵥ ζ))
      exact this
    have h := lse_hasDerivAt β (z := fun θ s => cpath a b θ s ⬝ᵥ ζ)
      (z' := fun s => cpath' a b θ s ⬝ᵥ ζ) (t := θ) hz
    rw [inv_mul_cancel₀ hβ.ne', one_mul] at h
    exact h
  have hDb : ∀ θ ζ, |D θ ζ| ≤ bnd ζ := by
    intro θ ζ
    simp only [hD, hbnd]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul, abs_of_nonneg (smx_nonneg _ _ _), cpath'_dot]
    have h1 : |-Real.sin θ * (a s ⬝ᵥ ζ) + Real.cos θ * (b s ⬝ᵥ ζ)| ≤ |a s ⬝ᵥ ζ| + |b s ⬝ᵥ ζ| := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_neg]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ)
      · rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)
    exact (mul_le_of_le_one_left (abs_nonneg _) (smx_le_one _ _ _)).trans h1
  have hDm : ∀ θ, Measurable (D θ) := by
    intro θ
    simp only [hD, smx, dotProduct]
    fun_prop
  have ibnd : Integrable bnd (stdGauss (Fin (n + 1))) :=
    integrable_finsetSum _ fun s _ => (integrable_dot (a s)).abs.add (integrable_dot (b s)).abs
  have hφ : ∀ θ, HasDerivAt (fun θ => ∫ ζ, F θ ζ ∂stdGauss (Fin (n + 1)))
      (∫ ζ, D θ ζ ∂stdGauss (Fin (n + 1))) θ := fun θ =>
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ => (lse_measurable β (cpath a b θ)).aestronglyMeasurable)
      (lse_integrable hβ (cpath a b θ)) (hDm θ).aestronglyMeasurable
      (ae_of_all _ fun ζ θ _ => hDb θ ζ) ibnd (ae_of_all _ fun ζ θ _ => hFd ζ θ)).2
  have hpos : ∀ θ ∈ Icc (0 : ℝ) (π / 2), 0 ≤ ∫ ζ, D θ ζ ∂stdGauss (Fin (n + 1)) :=
    fun θ hθ => path_deriv_nonneg a b horth hinc hβ hθ
  have hmono : MonotoneOn (fun θ => ∫ ζ, F θ ζ ∂stdGauss (Fin (n + 1))) (Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
      (continuous_iff_continuousAt.2 fun θ => (hφ θ).continuousAt).continuousOn
      (fun θ _ => (hφ θ).differentiableAt.differentiableWithinAt) fun θ hθ => ?_
    rw [(hφ θ).deriv]
    exact hpos θ (interior_subset hθ)
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have h := hmono (left_mem_Icc.mpr hpi) (right_mem_Icc.mpr hpi) hpi
  simp only [hF, cpath_dot, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
    one_mul, zero_mul, add_zero, zero_add] at h
  exact h

/-- **Sudakov–Fernique** for linear forms of a standard Gaussian vector indexed by `Fin (n + 1)`. -/
theorem sf_fin (a b : S → Fin (n + 1) → ℝ) (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hinc : ∀ s s', ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2) :
    ∫ ζ, Finset.univ.sup' Finset.univ_nonempty (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) ≤
      ∫ ζ, Finset.univ.sup' Finset.univ_nonempty (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) := by
  have msup : ∀ c : S → Fin (n + 1) → ℝ, Measurable fun ζ : Fin (n + 1) → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty (fun s => c s ⬝ᵥ ζ) := by
    intro c
    have := Finset.measurable_sup' (Finset.univ_nonempty (α := S))
      (f := fun s (ζ : Fin (n + 1) → ℝ) => c s ⬝ᵥ ζ) (fun s _ => by
        simp only [dotProduct]; fun_prop)
    convert this using 1
    funext ζ
    simp [Finset.sup'_apply]
  have isup : ∀ c : S → Fin (n + 1) → ℝ, Integrable (fun ζ : Fin (n + 1) → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty (fun s => c s ⬝ᵥ ζ)) (stdGauss (Fin (n + 1))) := by
    intro c
    refine Integrable.mono' (sumabs_integrable c) (msup c).aestronglyMeasurable
      (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨s0⟩ := ‹Nonempty S›
    constructor
    · have h1 := Finset.le_sup' (fun s => c s ⬝ᵥ ζ) (Finset.mem_univ s0)
      have h2 := neg_abs_le (c s0 ⬝ᵥ ζ)
      have h3 := abs_dot_le_sum c ζ s0
      linarith
    · exact Finset.sup'_le _ _ fun s _ => (le_abs_self _).trans (abs_dot_le_sum c ζ s)
  have hN : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set β : ℝ := (Real.log (Fintype.card S) + 1) / ε with hβd
  have hβ : 0 < β := div_pos (by linarith [Real.log_nonneg hN]) hε
  have hle : Real.log (Fintype.card S) / β ≤ ε := by
    rw [hβd, div_div_eq_mul_div, div_le_iff₀ (by linarith [Real.log_nonneg hN])]
    nlinarith [Real.log_nonneg hN]
  calc ∫ ζ, Finset.univ.sup' Finset.univ_nonempty (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1))
      ≤ ∫ ζ, lse β (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) :=
        integral_mono (isup a) (lse_integrable hβ a) fun ζ =>
          Finset.sup'_le _ _ fun s _ => le_lse hβ (fun s => a s ⬝ᵥ ζ) s
    _ ≤ ∫ ζ, lse β (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) := sf_step a b horth hinc hβ
    _ ≤ ∫ ζ, (Finset.univ.sup' Finset.univ_nonempty (fun s => b s ⬝ᵥ ζ) +
          Real.log (Fintype.card S) / β) ∂stdGauss (Fin (n + 1)) :=
        integral_mono (lse_integrable hβ b) ((isup b).add (integrable_const _)) fun ζ =>
          lse_le hβ fun s => Finset.le_sup' (fun s => b s ⬝ᵥ ζ) (Finset.mem_univ s)
    _ = ∫ ζ, Finset.univ.sup' Finset.univ_nonempty (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) +
          Real.log (Fintype.card S) / β := by
        rw [integral_add (isup b) (integrable_const _), integral_const]
        simp
    _ ≤ _ := by linarith

end core

/-- **The Sudakov–Fernique comparison inequality** for two finite families of linear forms of one
standard Gaussian vector `ζ` on `κ → ℝ`: if the families `a`, `b` are orthogonal to each other
(`a_s · b_{s'} = 0`: the two families are independent) and
`E(⟨a_s, ζ⟩ − ⟨a_{s'}, ζ⟩)² ≤ E(⟨b_s, ζ⟩ − ⟨b_{s'}, ζ⟩)²` for all `s`, `s'`, then
`E max_s ⟨a_s, ζ⟩ ≤ E max_s ⟨b_s, ζ⟩`. -/
theorem sudakovFernique {κ S : Type} [Fintype κ] [Fintype S] [Nonempty S] (a b : S → κ → ℝ)
    (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hinc : ∀ s s', ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2) :
    ∫ ζ, Finset.univ.sup' Finset.univ_nonempty (fun s => a s ⬝ᵥ ζ) ∂stdGauss κ ≤
      ∫ ζ, Finset.univ.sup' Finset.univ_nonempty (fun s => b s ⬝ᵥ ζ) ∂stdGauss κ := by
  classical
  rcases h : Fintype.card κ with _ | n
  · have : IsEmpty κ := Fintype.card_eq_zero_iff.mp h
    have h0 : ∀ (c ζ : κ → ℝ), c ⬝ᵥ ζ = 0 := fun c ζ => by simp [dotProduct]
    simp only [h0]
    exact le_rfl
  · set f : Fin (n + 1) ≃ κ := (Fintype.equivFinOfCardEq h).symm with hf
    have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) f)
        (stdGauss (Fin (n + 1))) (stdGauss κ) :=
      measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) f
    have hk : ∀ (Z : Fin (n + 1) → ℝ) (i : κ),
        (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) f) Z i = Z (f.symm i) := by
      intro Z i
      obtain ⟨j, rfl⟩ := f.surjective i
      rw [Equiv.symm_apply_apply]
      exact Equiv.piCongrLeft_apply_apply (P := fun _ : κ => ℝ) f Z j
    have hdot : ∀ (c : κ → ℝ) (Z : Fin (n + 1) → ℝ),
        c ⬝ᵥ (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) f) Z = (fun j => c (f j)) ⬝ᵥ Z := by
      intro c Z
      simp only [dotProduct, hk]
      rw [← Equiv.sum_comp f]
      simp
    rw [← hp.integral_comp' (fun ζ => Finset.univ.sup' Finset.univ_nonempty (fun s => a s ⬝ᵥ ζ)),
      ← hp.integral_comp' (fun ζ => Finset.univ.sup' Finset.univ_nonempty (fun s => b s ⬝ᵥ ζ))]
    simp only [hdot]
    refine sf_fin (fun s j => a s (f j)) (fun s j => b s (f j)) (fun s s' => ?_) (fun s s' => ?_)
    · have := horth s s'
      simp only [dotProduct] at this ⊢
      rw [← Equiv.sum_comp f] at this
      exact this
    · have := hinc s s'
      rw [← Equiv.sum_comp f (fun k => (a s k - a s' k) ^ 2),
        ← Equiv.sum_comp f (fun k => (b s k - b s' k) ^ 2)] at this
      exact this

end BstLean.Part152

open BstLean.Part152 in
#print axioms sudakovFernique
