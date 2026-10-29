import BstLean.Part162Sc
import BstLean.Part162Good
import BstLean.Part162Fld

/-!
# Part 162, item 3: Proposition FL for the paper's split data, from the latitude moments

Role: `delegations/statements/p162-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Proposition `t7:p07:FL` and its
evaluator formulas `t7:p07:FL-formulas` (`ε₀`, `L`, `c_ε`, `c_δ`, `A`, `D`, `ι_k`, `e_k`, `d_k`,
`𝒞`). Input interface: the moments of Proposition `t7:p07:LG` (`V`, `τ_{2p}`), here as
hypotheses on the latitude moments of `λ` and `σ`.

* `jensen_pow`, `int_three`, `int_two`: Jensen and the integration of the weighted bounds.
* `lbar`, `gbar`, `goodP`, `gmP`, **`dPaper`**: the paper's good set
  `{|λ − λ̄| ≤ w_l, |σ − σ̄| ≤ w_s, σ ≥ σ_l}` and split data (`λ₀`, `S₀` the good-set means,
  `λ̄`, `S̄` the latitude means).
* `kept_facts`, `cm_eps`, `cm_del`: identification of the conditional moments.
* `eps0`, `iotaP`, `c2η`, `c3η`, `cEw`, `cVw`: the constants.
* **`fluct_paper`**: `FLUCT_chi_hyp` for `dPaper` from the latitude moments, `B`, `Dd`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

section gen

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- Jensen: `(E Y²)^k ≤ E|Y|^{2k}` for a bounded measurable `Y`. -/
lemma jensen_pow {Y : α → ℝ} (hY : Measurable Y) {M : ℝ} (hM : ∀ a, |Y a| ≤ M) (k : ℕ) :
    (∫ a, Y a ^ 2 ∂μ) ^ k ≤ ∫ a, |Y a| ^ (2 * k) ∂μ := by
  have h := (convexOn_pow k).map_integral_le (μ := μ) (f := fun a => Y a ^ 2)
    (continuous_pow k).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun a => sq_nonneg (Y a))
    (intB (hY.pow_const 2) (sq_bound_of_abs hM))
    (intB ((hY.pow_const 2).pow_const k) (M := (M ^ 2) ^ k) fun a => by
      simp only [Function.comp]
      rw [abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
      exact pow_le_pow_left₀ (sq_nonneg _) (by
        have := sq_bound_of_abs hM a; rwa [abs_of_nonneg (sq_nonneg _)] at this) k)
  refine h.trans (le_of_eq ?_)
  congr 1; funext a
  simp only [Function.comp, pow_mul, sq_abs]

/-- **Integration of the three-term moment bound** over the kept indices. -/
lemma int_three {K : Set α} (mK : MeasurableSet K) {X Mf sd : α → ℝ} (mM : Measurable Mf)
    (msd : Measurable sd) {Kb : ℝ} (bM : ∀ a, |Mf a| ≤ Kb) (bsd : ∀ a, |sd a| ≤ Kb)
    (iX : IntegrableOn X K μ) (hM0 : ∀ a, 0 ≤ Mf a) (hsd0 : ∀ a, 0 ≤ sd a) {p : ℕ}
    (hsdM : ∀ a, sd a ^ p ≤ Mf a) {Kc ι ι' c2 c3 τ : ℝ} (hKc : 0 ≤ Kc) (hι' : 0 < ι')
    (hιp : ι' ^ p = ι) (hc2 : 0 < c2) (hc3 : 0 < c3) (hτ : 0 < τ)
    (hX : ∀ a ∈ K, X a ≤ Kc ^ p * (ι' * τ + c2 * τ + c3 * τ) ^ p *
      (ι' * τ / (ι' * τ + c2 * τ + c3 * τ) * (ι * Mf a / (ι' * τ) ^ p) +
        c2 * τ / (ι' * τ + c2 * τ + c3 * τ) * (c2 * sd a / (c2 * τ)) ^ p +
        c3 * τ / (ι' * τ + c2 * τ + c3 * τ) * (c3 * sd a / (c3 * τ)) ^ p))
    (hMτ : ∫ a, Mf a ∂μ ≤ τ ^ p) :
    ∫ a in K, X a ∂μ ≤ (Kc * ((ι' + c2 + c3) * τ)) ^ p := by
  set B := ι' * τ + c2 * τ + c3 * τ with hB
  have hB0 : 0 < B := by positivity
  have hι0 : 0 < ι := hιp ▸ pow_pos hι' p
  have iM : Integrable Mf μ := intB mM bM
  have isd : Integrable (fun a => sd a ^ p) μ := intB (msd.pow_const p) (M := Kb ^ p) fun a => by
    rw [abs_of_nonneg (pow_nonneg (hsd0 a) p)]
    exact pow_le_pow_left₀ (hsd0 a) ((le_abs_self _).trans (bsd a)) p
  set R : α → ℝ := fun a => Kc ^ p * B ^ p *
      (ι' * τ / B * (ι * Mf a / (ι' * τ) ^ p) + c2 * τ / B * (c2 * sd a / (c2 * τ)) ^ p +
        c3 * τ / B * (c3 * sd a / (c3 * τ)) ^ p) with hR
  have eR : R = fun a => (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * Mf a +
      (Kc ^ p * B ^ p * (c2 * τ / B + c3 * τ / B) / τ ^ p) * sd a ^ p := by
    funext a
    simp only [hR]
    have e2 : c2 * sd a / (c2 * τ) = sd a / τ := by field_simp
    have e3 : c3 * sd a / (c3 * τ) = sd a / τ := by field_simp
    rw [e2, e3, div_pow]
    ring
  have iR : Integrable R μ := by rw [eR]; exact (iM.const_mul _).add (isd.const_mul _)
  have hR0 : ∀ a, 0 ≤ R a := fun a => by
    simp only [hR]
    have := hM0 a; have := hsd0 a
    positivity
  calc ∫ a in K, X a ∂μ ≤ ∫ a in K, R a ∂μ := setIntegral_mono_on iX iR.integrableOn mK hX
    _ ≤ ∫ a, R a ∂μ := setIntegral_le_integral iR (Filter.Eventually.of_forall hR0)
    _ ≤ (Kc * ((ι' + c2 + c3) * τ)) ^ p := by
      rw [eR, integral_add (iM.const_mul _) (isd.const_mul _), integral_const_mul,
        integral_const_mul]
      have hsdI : ∫ a, sd a ^ p ∂μ ≤ τ ^ p :=
        (integral_mono isd iM hsdM).trans hMτ
      have q1 : (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * ∫ a, Mf a ∂μ ≤
          (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * τ ^ p :=
        mul_le_mul_of_nonneg_left hMτ (by positivity)
      have q2 : (Kc ^ p * B ^ p * (c2 * τ / B + c3 * τ / B) / τ ^ p) * ∫ a, sd a ^ p ∂μ ≤
          (Kc ^ p * B ^ p * (c2 * τ / B + c3 * τ / B) / τ ^ p) * τ ^ p :=
        mul_le_mul_of_nonneg_left hsdI (by positivity)
      have e : (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * τ ^ p +
          (Kc ^ p * B ^ p * (c2 * τ / B + c3 * τ / B) / τ ^ p) * τ ^ p =
          (Kc * ((ι' + c2 + c3) * τ)) ^ p := by
        rw [mul_pow (ι') τ, ← hιp, mul_pow Kc]
        have : B = (ι' + c2 + c3) * τ := by rw [hB]; ring
        rw [this]
        have hτp : 0 < τ ^ p := pow_pos hτ p
        have hιp' : 0 < ι' ^ p := pow_pos hι' p
        have hb : 0 < (ι' + c2 + c3) * τ := by positivity
        field_simp
        ring
      linarith

/-- **Integration of the two-term moment bound** over the kept indices. -/
lemma int_two {K : Set α} (mK : MeasurableSet K) {X Mf sd : α → ℝ} (mM : Measurable Mf)
    (msd : Measurable sd) {Kb : ℝ} (bM : ∀ a, |Mf a| ≤ Kb) (bsd : ∀ a, |sd a| ≤ Kb)
    (iX : IntegrableOn X K μ) (hM0 : ∀ a, 0 ≤ Mf a) (hsd0 : ∀ a, 0 ≤ sd a) {p : ℕ}
    (hsdM : ∀ a, sd a ^ p ≤ Mf a) {Kc ι ι' c2 τ : ℝ} (hKc : 0 ≤ Kc) (hι' : 0 < ι')
    (hιp : ι' ^ p = ι) (hc2 : 0 < c2) (hτ : 0 < τ)
    (hX : ∀ a ∈ K, X a ≤ Kc ^ p * (ι' * τ + c2 * τ) ^ p *
      (ι' * τ / (ι' * τ + c2 * τ) * (ι * Mf a / (ι' * τ) ^ p) +
        c2 * τ / (ι' * τ + c2 * τ) * (c2 * sd a / (c2 * τ)) ^ p))
    (hMτ : ∫ a, Mf a ∂μ ≤ τ ^ p) :
    ∫ a in K, X a ∂μ ≤ (Kc * ((ι' + c2) * τ)) ^ p := by
  set B := ι' * τ + c2 * τ with hB
  have hB0 : 0 < B := by positivity
  have hι0 : 0 < ι := hιp ▸ pow_pos hι' p
  have iM : Integrable Mf μ := intB mM bM
  have isd : Integrable (fun a => sd a ^ p) μ := intB (msd.pow_const p) (M := Kb ^ p) fun a => by
    rw [abs_of_nonneg (pow_nonneg (hsd0 a) p)]
    exact pow_le_pow_left₀ (hsd0 a) ((le_abs_self _).trans (bsd a)) p
  set R : α → ℝ := fun a => Kc ^ p * B ^ p *
      (ι' * τ / B * (ι * Mf a / (ι' * τ) ^ p) + c2 * τ / B * (c2 * sd a / (c2 * τ)) ^ p) with hR
  have eR : R = fun a => (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * Mf a +
      (Kc ^ p * B ^ p * (c2 * τ / B) / τ ^ p) * sd a ^ p := by
    funext a
    simp only [hR]
    have e2 : c2 * sd a / (c2 * τ) = sd a / τ := by field_simp
    rw [e2, div_pow]
    ring
  have iR : Integrable R μ := by rw [eR]; exact (iM.const_mul _).add (isd.const_mul _)
  have hR0 : ∀ a, 0 ≤ R a := fun a => by
    simp only [hR]
    have := hM0 a; have := hsd0 a
    positivity
  calc ∫ a in K, X a ∂μ ≤ ∫ a in K, R a ∂μ := setIntegral_mono_on iX iR.integrableOn mK hX
    _ ≤ ∫ a, R a ∂μ := setIntegral_le_integral iR (Filter.Eventually.of_forall hR0)
    _ ≤ (Kc * ((ι' + c2) * τ)) ^ p := by
      rw [eR, integral_add (iM.const_mul _) (isd.const_mul _), integral_const_mul,
        integral_const_mul]
      have hsdI : ∫ a, sd a ^ p ∂μ ≤ τ ^ p :=
        (integral_mono isd iM hsdM).trans hMτ
      have q1 : (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * ∫ a, Mf a ∂μ ≤
          (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * τ ^ p :=
        mul_le_mul_of_nonneg_left hMτ (by positivity)
      have q2 : (Kc ^ p * B ^ p * (c2 * τ / B) / τ ^ p) * ∫ a, sd a ^ p ∂μ ≤
          (Kc ^ p * B ^ p * (c2 * τ / B) / τ ^ p) * τ ^ p :=
        mul_le_mul_of_nonneg_left hsdI (by positivity)
      have e : (Kc ^ p * B ^ p * (ι' * τ / B) * ι / (ι' * τ) ^ p) * τ ^ p +
          (Kc ^ p * B ^ p * (c2 * τ / B) / τ ^ p) * τ ^ p = (Kc * ((ι' + c2) * τ)) ^ p := by
        rw [mul_pow (ι') τ, ← hιp, mul_pow Kc]
        have : B = (ι' + c2) * τ := by rw [hB]; ring
        rw [this]
        have hτp : 0 < τ ^ p := pow_pos hτ p
        have hιp' : 0 < ι' ^ p := pow_pos hι' p
        have hb : 0 < (ι' + c2) * τ := by positivity
        field_simp
      linarith

end gen

section paper

open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161

variable {n : ℕ}

/-- `λ̄(a) = E(λ | a)` (the mean over the latitude sphere). -/
noncomputable def lbar (D : Design n) (c : Ret n) (a : Ix n) : ℝ :=
  ∫ v, lA D c a v ∂stdGauss (Fin (n - 1))

/-- `σ̄(a) = E(σ | a)`. -/
noncomputable def gbar (D : Design n) (c : Ret n) (a : Ix n) : ℝ :=
  ∫ v, sgA D c a v ∂stdGauss (Fin (n - 1))

lemma measurable_lbar (D : Design n) (c : Ret n) : Measurable (lbar D c) :=
  ((measurable_lA D c).stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin (n - 1)))).measurable

lemma measurable_gbar (D : Design n) (c : Ret n) : Measurable (gbar D c) :=
  ((measurable_sgA D c).stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin (n - 1)))).measurable

/-- **The paper's good set** `𝒳 = {|λ − λ̄| ≤ w_l, |σ − σ̄| ≤ w_s, σ ≥ σ_l}` (with
`f = √e_b λ`, `z = σ/√γ_A`: `w_l = d_w/√e_b`, `w_s = √γ_A d_w`, `σ_l = √(γ_A d_low)`). -/
def goodP (D : Design n) (c : Ret n) (wl ws σl : ℝ) : Set (Ix n × (Fin (n - 1) → ℝ)) :=
  {p | |lA D c p.1 p.2 - lbar D c p.1| ≤ wl ∧ |sgA D c p.1 p.2 - gbar D c p.1| ≤ ws ∧
    σl ≤ sgA D c p.1 p.2}

lemma measurableSet_goodP (D : Design n) (c : Ret n) (wl ws σl : ℝ) :
    MeasurableSet (goodP D c wl ws σl) :=
  (measurableSet_le ((measurable_lA D c).sub ((measurable_lbar D c).comp measurable_fst)).abs
    measurable_const).inter
    ((measurableSet_le ((measurable_sgA D c).sub ((measurable_gbar D c).comp measurable_fst)).abs
      measurable_const).inter (measurableSet_le measurable_const (measurable_sgA D c)))

/-- The good-set mean of a field `f(a, v)`. -/
noncomputable def gmP (D : Design n) (c : Ret n) (wl ws σl : ℝ)
    (f : Ix n × (Fin (n - 1) → ℝ) → ℝ) (a : Ix n) : ℝ :=
  (1 - removed (stdGauss (Fin (n - 1))) (goodP D c wl ws σl) a)⁻¹ *
    ∫ v, (goodP D c wl ws σl).indicator f (a, v) ∂stdGauss (Fin (n - 1))

lemma measurable_gmP (D : Design n) (c : Ret n) (wl ws σl : ℝ)
    {f : Ix n × (Fin (n - 1) → ℝ) → ℝ} (hf : Measurable f) : Measurable (gmP D c wl ws σl f) := by
  unfold gmP
  exact ((measurable_const.sub (measurable_removed _ (measurableSet_goodP D c wl ws σl))).inv).mul
    ((hf.indicator (measurableSet_goodP D c wl ws σl)).stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable

/-- **The paper's split data**: good set `goodP`, `λ₀ = E(λ | good)`, `S₀ = E(S | good)`,
`λ̄ = E λ`, `S̄ = E S` (per latitude index). -/
noncomputable def dPaper (D : Design n) (c : Ret n) (wl ws σl η : ℝ) (h0 : 0 < η) (h1 : η < 1) :
    SplitData n where
  good := goodP D c wl ws σl
  mgood := measurableSet_goodP D c wl ws σl
  eta := η
  eta_pos := h0
  eta_lt := h1
  lam0 := gmP D c wl ws σl (fun p => lA D c p.1 p.2)
  S0 := gmP D c wl ws σl (fun p => sA D c p.1 p.2)
  lamb := lbar D c
  Sb := fun a => ∫ v, sA D c a v ∂stdGauss (Fin (n - 1))
  mlam0 := measurable_gmP D c wl ws σl (measurable_lA D c)
  mS0 := measurable_gmP D c wl ws σl (measurable_sA D c)
  mlamb := measurable_lbar D c
  mSb := ((measurable_sA D c).stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin (n - 1)))).measurable

lemma gMeas_eq_nrm (d : SplitData n) (a : Ix n) :
    gMeas d a = nrm (stdGauss (Fin (n - 1))) (slice d a) := by
  unfold gMeas nrm; rw [slice_real]

lemma gmP_eq (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    (f : Ix n × (Fin (n - 1) → ℝ) → ℝ) {a : Ix n}
    (hm : 0 < (stdGauss (Fin (n - 1))).real (slice (dPaper D c wl ws σl η h0 h1) a)) :
    gmP D c wl ws σl f a = ∫ v, f (a, v) ∂nrm (stdGauss (Fin (n - 1)))
      (slice (dPaper D c wl ws σl η h0 h1) a) := by
  rw [integral_nrm _ (measurableSet_slice _ a) hm, slice_real]
  unfold gmP
  congr 1

/-- Facts on one kept index of the paper's split data. -/
lemma kept_facts (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    {a : Ix n} (ha : a ∈ keptIx D c (dPaper D c wl ws σl η h0 h1)) :
    0 < (stdGauss (Fin (n - 1))).real (slice (dPaper D c wl ws σl η h0 h1) a) ∧
    1 - η ≤ (stdGauss (Fin (n - 1))).real (slice (dPaper D c wl ws σl η h0 h1) a) ∧
    (dPaper D c wl ws σl η h0 h1).S0 a = ∫ v, sgA D c a v ^ 2 ∂nrm (stdGauss (Fin (n - 1)))
      (slice (dPaper D c wl ws σl η h0 h1) a) ∧
    (dPaper D c wl ws σl η h0 h1).lam0 a = ∫ v, lA D c a v ∂nrm (stdGauss (Fin (n - 1)))
      (slice (dPaper D c wl ws σl η h0 h1) a) ∧
    (∀ v ∈ slice (dPaper D c wl ws σl η h0 h1) a,
      |sgA D c a v - ∫ w, sgA D c a w ∂stdGauss (Fin (n - 1))| ≤ ws ∧ σl ≤ sgA D c a v) ∧
    (∀ v ∈ slice (dPaper D c wl ws σl η h0 h1) a,
      |lA D c a v - ∫ w, lA D c a w ∂stdGauss (Fin (n - 1))| ≤ wl) := by
  have hr : removed (stdGauss (Fin (n - 1))) (dPaper D c wl ws σl η h0 h1).good a ≤ η := ha.2
  have hreal := slice_real (dPaper D c wl ws σl η h0 h1) a
  have hm1 : 1 - η ≤ (stdGauss (Fin (n - 1))).real (slice (dPaper D c wl ws σl η h0 h1) a) := by
    rw [hreal]; linarith
  have hm : 0 < (stdGauss (Fin (n - 1))).real (slice (dPaper D c wl ws σl η h0 h1) a) := by
    linarith
  refine ⟨hm, hm1, ?_, ?_, fun v hv => ⟨hv.2.1, hv.2.2⟩, fun v hv => hv.1⟩
  · show gmP D c wl ws σl (fun p => sA D c p.1 p.2) a = _
    rw [gmP_eq D c h0 h1 _ hm]; rfl
  · show gmP D c wl ws σl (fun p => lA D c p.1 p.2) a = _
    rw [gmP_eq D c h0 h1 _ hm]

/-- Conditional moments of `ε` for the paper's split data. -/
lemma cm_eps (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    {a : Ix n} (ha : a ∈ keptIx D c (dPaper D c wl ws σl η h0 h1)) {p : ℕ} (hp : p ≠ 0) :
    condMom (dPaper D c wl ws σl η h0 h1) (epsF D c (dPaper D c wl ws σl η h0 h1)) p a =
      ∫ v, |sgA D c a v ^ 2 / (∫ w, sgA D c a w ^ 2 ∂nrm (stdGauss (Fin (n - 1)))
        (slice (dPaper D c wl ws σl η h0 h1) a)) - 1| ^ p ∂nrm (stdGauss (Fin (n - 1)))
        (slice (dPaper D c wl ws σl η h0 h1) a) := by
  obtain ⟨hm, -, hS, -, -, -⟩ := kept_facts hn D c h0 h1 ha
  set d := dPaper D c wl ws σl η h0 h1
  have hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1 := lt_of_le_of_lt ha.2 d.eta_lt
  have hvan : ∀ a v, v ∉ slice d a → epsF D c d a v = 0 := fun a v hv => by
    simp only [epsF, eG, Set.indicator_of_notMem hv]
  rw [condMom_eq d hvan hβ hp, gMeas_eq_nrm]
  refine integral_congr_ae ((nrm_ae_mem _ (measurableSet_slice d a)).mono fun v hv => ?_)
  simp only [epsF, eG, Set.indicator_of_mem hv, sA_eq, ← hS]

/-- Conditional moments of `a_c δ` for the paper's split data. -/
lemma cm_del (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    {a : Ix n} (ha : a ∈ keptIx D c (dPaper D c wl ws σl η h0 h1)) {p : ℕ} (hp : p ≠ 0) :
    condMom (dPaper D c wl ws σl η h0 h1) (delF D c (dPaper D c wl ws σl η h0 h1)) p a =
      ∫ v, |√(normSq c.2.1.2 / (∫ w, sgA D c a w ^ 2 ∂nrm (stdGauss (Fin (n - 1)))
        (slice (dPaper D c wl ws σl η h0 h1) a))) * (lA D c a v - ∫ w, lA D c a w
          ∂nrm (stdGauss (Fin (n - 1))) (slice (dPaper D c wl ws σl η h0 h1) a))| ^ p
        ∂nrm (stdGauss (Fin (n - 1))) (slice (dPaper D c wl ws σl η h0 h1) a) := by
  obtain ⟨hm, -, hS, hl, -, -⟩ := kept_facts hn D c h0 h1 ha
  set d := dPaper D c wl ws σl η h0 h1
  have hβ : removed (stdGauss (Fin (n - 1))) d.good a < 1 := lt_of_le_of_lt ha.2 d.eta_lt
  have hvan : ∀ a v, v ∉ slice d a → delF D c d a v = 0 := fun a v hv => by
    simp only [delF, dG, Set.indicator_of_notMem hv, mul_zero]
  rw [condMom_eq d hvan hβ hp, gMeas_eq_nrm]
  refine integral_congr_ae ((nrm_ae_mem _ (measurableSet_slice d a)).mono fun v hv => ?_)
  simp only [delF, dG, Set.indicator_of_mem hv, ← hS, ← hl]

/-- `ε₀ = (1 + 2w_s/σ_l)² − 1`. -/
noncomputable def eps0 (ws σl : ℝ) : ℝ := (1 + 2 * ws / σl) ^ 2 - 1
/-- `ι = (1 − η)^{−1/p}` (the restriction factor). -/
noncomputable def iotaP (η : ℝ) (p : ℕ) : ℝ := ((1 - η)⁻¹) ^ ((p : ℝ)⁻¹)
/-- `√(η/(1 − η))` (the mean-shift factor). -/
noncomputable def c2η (η : ℝ) : ℝ := √(η / (1 - η))
/-- `w_s/(2σ_l√(1 − η))` (the shift from `E(σ|good)` to `√S₀`). -/
noncomputable def c3η (η ws σl : ℝ) : ℝ := ws / (2 * σl * √(1 - η))
/-- `2(σ_l + w_s)/σ_l²` (the factor from `|σ − √S₀|` to `|ε|`). -/
noncomputable def cEw (ws σl : ℝ) : ℝ := 2 * (σl + ws) / σl ^ 2
/-- `4(1 + w_s/σ_l)²/σ_l²` (the variance factor). -/
noncomputable def cVw (ws σl : ℝ) : ℝ := 4 * (1 + ws / σl) ^ 2 / σl ^ 2

lemma iotaP_pos {η : ℝ} (h1 : η < 1) (p : ℕ) : 0 < iotaP η p := by
  unfold iotaP; exact Real.rpow_pos_of_pos (inv_pos.mpr (by linarith)) _

lemma iotaP_pow {η : ℝ} (h1 : η < 1) {p : ℕ} (hp : p ≠ 0) : iotaP η p ^ p = (1 - η)⁻¹ := by
  unfold iotaP; exact Real.rpow_inv_natCast_pow (inv_nonneg.mpr (by linarith)) hp

lemma measurable_sgA_left (D : Design n) (c : Ret n) (a : Ix n) : Measurable (sgA D c a) :=
  (measurable_sigX D c).comp (measurable_xLat_comp c measurable_const BstLean.Part53.measurable_unitF)

/-- **Proposition FL (chi-square, removal and displacement roots) for the paper's split data,
from the latitude moments of `λ` and `σ` (the interface of Proposition `t7:p07:LG`).**
Parameters: widths `w_l ≥ 0`, `w_s > 0`, floor `σ_l > 0`, `0 < η < 1`, `|c_A|² ≤ C_A`,
`ε₀ = (1 + 2w_s/σ_l)² − 1 < 1`. Latitude moments (over all indices, `μ_I`):
`∫ Var(σ|a)² ≤ V_s²`, `∫ Var(λ|a)² ≤ V_l²`, `∫ E(|σ − σ̄|^8 | a) ≤ τ_{s,8}^8`, the same with
`12`, and for `λ`. With `B ≥ E β`, `Dd ≥ E_K H²(Q_a, Q̄_a)` and the root sum `≤ h_fl`, THEN
`FLUCT_chi_hyp` holds for `dPaper` with window `ε₀`, `δ₀ = 2w_l`, `s_low = σ_l²`. -/
theorem fluct_paper (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (hwl : 0 ≤ wl)
    (hws : 0 < ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1) (hcA : 0 < normSq c.2.1.2)
    {CA : ℝ} (hCA : normSq c.2.1.2 ≤ CA) (hε : eps0 ws σl < 1)
    {Vs Vl ts8 ts12 tl8 tl12 B Dd hfl : ℝ} (hVs0 : 0 ≤ Vs) (hVl0 : 0 ≤ Vl) (hts8 : 0 < ts8)
    (hts12 : 0 < ts12) (htl8 : 0 < tl8) (htl12 : 0 < tl12)
    (hVs : ∫ a, (∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vs ^ 2)
    (hVl : ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vl ^ 2)
    (hs8 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts8 ^ 8)
    (hs12 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts12 ^ 12)
    (hl8 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl8 ^ 8)
    (hl12 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl12 ^ 12)
    (hB : ∫ a, removed (stdGauss (Fin (n - 1))) (goodP D c wl ws σl) a ∂muI n ≤ B)
    (hD : ∫ a in keptIx D c (dPaper D c wl ws σl η h0 h1), hellG2 n
      (((dPaper D c wl ws σl η h0 h1).lam0 a - (dPaper D c wl ws σl η h0 h1).lamb a) ^ 2 *
        normSq c.2.1.2) ((dPaper D c wl ws σl η h0 h1).S0 a) ((dPaper D c wl ws σl η h0 h1).Sb a)
        ∂muI n ≤ Dd)
    (hsum : √(2 * (1 + η⁻¹) * B) + √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
        (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
          (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
        (cVw ws σl * ((1 - η)⁻¹ * Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
        (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * ts8))
        (√CA / σl * ((iotaP η 8 + c2η η) * tl8))
        (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
        (√CA / σl * ((iotaP η 12 + c2η η) * tl12))) + √Dd ≤ hfl) :
    FLUCT_chi_hyp D c (dPaper D c wl ws σl η h0 h1) (eps0 ws σl) (2 * wl) (σl ^ 2) hfl := by
  set ν := stdGauss (Fin (n - 1)) with hν
  set d := dPaper D c wl ws σl η h0 h1 with hd
  set K := keptIx D c d with hK
  have mK : MeasurableSet K := measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hCA0 : 0 ≤ CA := (normSq_nonneg _).trans hCA
  set L := √CA * (2 * wl) / σl with hL
  have hL0 : 0 ≤ L := by positivity
  have hε0 : 0 ≤ eps0 ws σl := by
    unfold eps0; have : 0 ≤ 2 * ws / σl := by positivity
    nlinarith
  have mS : ∀ a, Measurable (fun v => sgA D c a v) := fun a => measurable_sgA_left D c a
  have mLa : ∀ a, Measurable (fun v => lA D c a v) := fun a => measurable_lA_left D c a
  have bS : ∀ a v, |sgA D c a v| ≤ lipSig D c := abs_sgA_le hn D c
  have bLa : ∀ a v, |lA D c a v| ≤ lipLam D c := abs_lA_le hn D c
  -- window
  have hwin : ∀ a ∈ K, σl ^ 2 ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ eps0 ws σl ∧ |lA D c a v - d.lam0 a| ≤ 2 * wl ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ L ^ 2 := by
    intro a ha
    obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
    obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, -, -⟩ :=
      idx_scale (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ
    have hS0 : σl ^ 2 ≤ d.S0 a := by rw [hS]; exact (pow_le_pow_left₀ hσl.le hlo 2).trans s1
    have hφw := idx_phi_window (measurableSet_slice d a) hm (mLa a) (bLa a) hGφ
    refine ⟨hS0, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · rw [sA_eq, hS]
      obtain ⟨x1, x2⟩ := hG' v hv
      exact idx_eps_window hσl hws.le hlo hhi s1 s2 x1 x2
    · rw [hl]; exact hφw v hv
    · have hδ := hφw v hv
      rw [← hl] at hδ
      have h2 : (lA D c a v - d.lam0 a) ^ 2 ≤ (2 * wl) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
      have h3 : normSq c.2.1.2 / d.S0 a ≤ CA / σl ^ 2 :=
        div_le_div₀ hCA0 hCA (by positivity) hS0
      calc normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ CA / σl ^ 2 * (2 * wl) ^ 2 :=
            mul_le_mul h3 h2 (sq_nonneg _) (by positivity)
        _ = L ^ 2 := by rw [hL, div_pow, mul_pow (√CA), Real.sq_sqrt hCA0]; ring
  -- centring
  have hcent : ∀ a ∈ K, ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂ν = 0 ∧
      ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂ν = 0 := by
    intro a ha
    obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
    have ms := measurableSet_slice d a
    have key : ∀ f : (Fin (n - 1) → ℝ) → ℝ, ∫ v in slice d a, f v ∂ν =
        ν.real (slice d a) * ∫ v, f v ∂nrm ν (slice d a) := fun f => by
      rw [integral_nrm ν ms hm, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul, integral_indicator ms]
    obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, -, -⟩ := idx_scale ms hm (mS a) (bS a) hws.le hσl hGψ
    have hS0p : 0 < d.S0 a := by
      rw [hS]; exact lt_of_lt_of_le (by have := lt_of_lt_of_le hσl hlo; positivity) s1
    have iL : IntegrableOn (fun v => lA D c a v) (slice d a) ν := (intB (mLa a) (bLa a)).integrableOn
    have iSA : IntegrableOn (fun v => sA D c a v / d.S0 a) (slice d a) ν :=
      (intB (((mS a).pow_const 2).div_const _) (M := lipSig D c ^ 2 / d.S0 a) fun v => by
        rw [abs_div, abs_of_pos hS0p]
        exact div_le_div_of_nonneg_right (sq_bound_of_abs (bS a) v) hS0p.le).integrableOn
    constructor
    · rw [integral_sub iL (integrableOn_const (by simp)), setIntegral_const, key, hl]
      simp only [smul_eq_mul]; ring
    · rw [integral_sub iSA (integrableOn_const (by simp)), setIntegral_const, key, integral_div]
      simp only [sA_eq, smul_eq_mul]
      rw [← hS]; field_simp; ring
  -- the fields as functions of `(a, v)` and their bounds
  have hvE : ∀ a v, v ∉ slice d a → epsF D c d a v = 0 := fun a v hv => by
    simp only [epsF, eG, Set.indicator_of_notMem hv]
  have hvD : ∀ a v, v ∉ slice d a → delF D c d a v = 0 := fun a v hv => by
    simp only [delF, dG, Set.indicator_of_notMem hv, mul_zero]
  have mE := measurable_epsF D c d
  have mD := measurable_delF D c d
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  have hbE : ∀ a ∈ K, ∀ v, |epsF D c d a v| ≤ eps0 ws σl := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [epsF, eG, Set.indicator_of_mem hv]; exact ((hwin a ha).2 v hv).1
    · rw [hvE a v hv, abs_zero]; exact hε0
  have hbD : ∀ a ∈ K, ∀ v, |delF D c d a v| ≤ L := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [delF, dG, Set.indicator_of_mem hv]
      have h := ((hwin a ha).2 v hv).2.2
      have hS : 0 < d.S0 a := lt_of_lt_of_le (by positivity) (hwin a ha).1
      have h2 : √(normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2) ≤ √(L ^ 2) :=
        Real.sqrt_le_sqrt h
      rwa [Real.sqrt_mul (div_nonneg (normSq_nonneg _) hS.le), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hL0, ← abs_of_nonneg (Real.sqrt_nonneg (normSq c.2.1.2 / d.S0 a)),
        ← abs_mul] at h2
    · rw [hvD a v hv, abs_zero]; exact hL0
  -- the latitude moments as functions of `a`
  have hgb : ∀ a, |gbar D c a| ≤ lipSig D c := fun a => by
    unfold gbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |sgA D c a v| ∂ν ≤ ∫ _v, lipSig D c ∂ν :=
          integral_mono (intB (mS a).abs (M := lipSig D c) fun v => by rw [abs_abs]; exact bS a v)
            (integrable_const _) (bS a)
      _ = lipSig D c := by simp
  have hlb : ∀ a, |lbar D c a| ≤ lipLam D c := fun a => by
    unfold lbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |lA D c a v| ∂ν ≤ ∫ _v, lipLam D c ∂ν :=
          integral_mono (intB (mLa a).abs (M := lipLam D c) fun v => by rw [abs_abs]; exact bLa a v)
            (integrable_const _) (bLa a)
      _ = lipLam D c := by simp
  set Ks := 2 * lipSig D c with hKs
  set Kl := 2 * lipLam D c with hKl
  have hKs0 : 0 ≤ Ks := by have := lipSig_nonneg D c; positivity
  have hKl0 : 0 ≤ Kl := by have := lipLam_nonneg D c; positivity
  have bYs : ∀ a v, |sgA D c a v - gbar D c a| ≤ Ks := fun a v =>
    (abs_sub _ _).trans (by linarith [bS a v, hgb a])
  have bYl : ∀ a v, |lA D c a v - lbar D c a| ≤ Kl := fun a v =>
    (abs_sub _ _).trans (by linarith [bLa a v, hlb a])
  have mYs : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2 - gbar D c p.1) :=
    (measurable_sgA D c).sub ((measurable_gbar D c).comp measurable_fst)
  have mYl : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => lA D c p.1 p.2 - lbar D c p.1) :=
    (measurable_lA D c).sub ((measurable_lbar D c).comp measurable_fst)
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mVs : Measurable (fun a => ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) := mInt (mYs.pow_const 2)
  have mVl : Measurable (fun a => ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) := mInt (mYl.pow_const 2)
  have mMs : ∀ p : ℕ, Measurable (fun a => ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν) := fun p =>
    mInt (mYs.abs.pow_const p)
  have mMl : ∀ p : ℕ, Measurable (fun a => ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν) := fun p =>
    mInt (mYl.abs.pow_const p)
  have bInt : ∀ {f : (Fin (n - 1) → ℝ) → ℝ} {M : ℝ}, Measurable f → (∀ v, 0 ≤ f v) →
      (∀ v, f v ≤ M) → 0 ≤ ∫ v, f v ∂ν ∧ ∫ v, f v ∂ν ≤ M := fun {f} {M} hf h0 hM => by
    refine ⟨integral_nonneg h0, ?_⟩
    calc ∫ v, f v ∂ν ≤ ∫ _v, M ∂ν :=
          integral_mono (intB hf (M := M) fun v => by rw [abs_of_nonneg (h0 v)]; exact hM v)
            (integrable_const _) hM
      _ = M := by simp
  have bVs : ∀ a, 0 ≤ ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν ∧
      ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν ≤ Ks ^ 2 := fun a =>
    bInt (((mS a).sub_const _).pow_const 2) (fun v => sq_nonneg _)
      (fun v => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bYs a v) 2)
  have bVl : ∀ a, 0 ≤ ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν ∧
      ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν ≤ Kl ^ 2 := fun a =>
    bInt (((mLa a).sub_const _).pow_const 2) (fun v => sq_nonneg _)
      (fun v => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bYl a v) 2)
  have bMs : ∀ p : ℕ, ∀ a, 0 ≤ ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν ∧
      ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν ≤ Ks ^ p := fun p a =>
    bInt (((mS a).sub_const _).abs.pow_const p) (fun v => pow_nonneg (abs_nonneg _) _)
      (fun v => pow_le_pow_left₀ (abs_nonneg _) (bYs a v) p)
  have bMl : ∀ p : ℕ, ∀ a, 0 ≤ ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν ∧
      ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν ≤ Kl ^ p := fun p a =>
    bInt (((mLa a).sub_const _).abs.pow_const p) (fun v => pow_nonneg (abs_nonneg _) _)
      (fun v => pow_le_pow_left₀ (abs_nonneg _) (bYl a v) p)
  have hηm : ∀ a ∈ K, (ν.real (slice d a))⁻¹ ≤ (1 - η)⁻¹ := fun a ha =>
    inv_anti₀ (by linarith) (kept_facts hn D c h0 h1 ha).2.1
  have hc2 : 0 < c2η η := Real.sqrt_pos.mpr (div_pos h0 (by linarith))
  have hc3 : 0 < c3η η ws σl := by
    unfold c3η; have := Real.sqrt_pos.mpr (show (0:ℝ) < 1 - η by linarith); positivity
  have hcE : 0 ≤ cEw ws σl := by unfold cEw; positivity
  have hcV : 0 ≤ cVw ws σl := by unfold cVw; positivity
  -- the square-root of the variance and Jensen
  have msd : ∀ (F : Ix n → (Fin (n - 1) → ℝ) → ℝ),
      Measurable (fun a => ∫ v, F a v ^ 2 ∂ν) → Measurable (fun a => √(∫ v, F a v ^ 2 ∂ν)) :=
    fun F h => h.sqrt
  have sd_pow : ∀ {x : ℝ}, 0 ≤ x → ∀ k : ℕ, √x ^ (2 * k) = x ^ k := fun {x} hx k => by
    rw [pow_mul, Real.sq_sqrt hx]
  -- (IA)
  have IA : ∫ a in K, condMom d (epsF D c d) 2 a ^ 2 ∂muI n ≤ (cVw ws σl * ((1 - η)⁻¹ * Vs)) ^ 2 := by
    set q : Ix n → ℝ := fun a => cVw ws σl * ((1 - η)⁻¹ * ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν)
      with hq
    have hqa : ∀ a ∈ K, condMom d (epsF D c d) 2 a ^ 2 ≤ q a ^ 2 := by
      intro a ha
      obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      have h0' := (condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) two_ne_zero).1
      have h2 := idx_eps_sq (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ
      have bd : ∀ v, |sgA D c a v - ∫ w, sgA D c a w ∂ν| ≤ Ks := bYs a
      have h3 := integral_nrm_le (measurableSet_slice d a) hm
        (g := fun v => (sgA D c a v - ∫ w, sgA D c a w ∂ν) ^ 2) (fun v => sq_nonneg _)
        (intB (((mS a).sub_const _).pow_const 2) (sq_bound_of_abs bd))
      have hle : condMom d (epsF D c d) 2 a ≤ q a := by
        rw [cm_eps hn D c h0 h1 ha two_ne_zero]
        simp_rw [sq_abs]
        refine h2.trans ?_
        simp only [hq, cVw]
        refine mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right (hηm a ha)
          (integral_nonneg fun v => sq_nonneg _))) (by positivity)
      exact pow_le_pow_left₀ h0' hle 2
    have iq : Integrable (fun a => q a ^ 2) (muI n) :=
      intB ((mVs.const_mul _ |>.const_mul _).pow_const 2)
        (M := (cVw ws σl * ((1 - η)⁻¹ * Ks ^ 2)) ^ 2) fun a => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have := bVs a
          have hη' : 0 ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
          exact pow_le_pow_left₀ (by positivity) (by
            simp only [hq]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this.2 hη') hcV) 2
    have iC : IntegrableOn (fun a => condMom d (epsF D c d) 2 a ^ 2) K (muI n) := by
      refine Integrable.of_bound ((measurable_condMom d mE 2).pow_const 2).aestronglyMeasurable
        ((eps0 ws σl ^ 2) ^ 2) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) two_ne_zero
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ b0 b1 2
    calc ∫ a in K, condMom d (epsF D c d) 2 a ^ 2 ∂muI n ≤ ∫ a in K, q a ^ 2 ∂muI n :=
          setIntegral_mono_on iC iq.integrableOn mK hqa
      _ ≤ ∫ a, q a ^ 2 ∂muI n :=
          setIntegral_le_integral iq (Filter.Eventually.of_forall fun a => sq_nonneg _)
      _ = (cVw ws σl * (1 - η)⁻¹) ^ 2 *
            ∫ a, (∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) ^ 2 ∂muI n := by
          rw [← integral_const_mul]; congr 1; funext a; simp only [hq]; ring
      _ ≤ (cVw ws σl * (1 - η)⁻¹) ^ 2 * Vs ^ 2 := mul_le_mul_of_nonneg_left hVs (sq_nonneg _)
      _ = _ := by ring
  -- (ID)
  have ID : ∫ a in K, condMom d (delF D c d) 2 a ^ 2 ∂muI n ≤
      (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl)) ^ 2 := by
    set q : Ix n → ℝ := fun a => CA / σl ^ 2 * ((1 - η)⁻¹ * ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν)
      with hq
    have hqa : ∀ a ∈ K, condMom d (delF D c d) 2 a ^ 2 ≤ q a ^ 2 := by
      intro a ha
      obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      have h0' := (condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) two_ne_zero).1
      have hS0 : σl ^ 2 ≤ ∫ w, sgA D c a w ^ 2 ∂nrm ν (slice d a) := hS ▸ (hwin a ha).1
      have h2 := idx_del_sq (measurableSet_slice d a) hm (mLa a) (bLa a) hσl hS0
        (normSq_nonneg c.2.1.2) hm1 h1
      have hle : condMom d (delF D c d) 2 a ≤ q a := by
        rw [cm_del hn D c h0 h1 ha two_ne_zero]
        simp_rw [sq_abs]
        refine h2.trans ?_
        simp only [hq]
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCA (by positivity)) ?_
        have : 0 ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
        have := (bVl a).1
        positivity
      exact pow_le_pow_left₀ h0' hle 2
    have iq : Integrable (fun a => q a ^ 2) (muI n) :=
      intB ((mVl.const_mul _ |>.const_mul _).pow_const 2)
        (M := (CA / σl ^ 2 * ((1 - η)⁻¹ * Kl ^ 2)) ^ 2) fun a => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have := bVl a
          have hη' : 0 ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
          exact pow_le_pow_left₀ (by positivity) (by
            simp only [hq]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this.2 hη') (by positivity)) 2
    have iC : IntegrableOn (fun a => condMom d (delF D c d) 2 a ^ 2) K (muI n) := by
      refine Integrable.of_bound ((measurable_condMom d mD 2).pow_const 2).aestronglyMeasurable
        ((L ^ 2) ^ 2) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) two_ne_zero
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ b0 b1 2
    calc ∫ a in K, condMom d (delF D c d) 2 a ^ 2 ∂muI n ≤ ∫ a in K, q a ^ 2 ∂muI n :=
          setIntegral_mono_on iC iq.integrableOn mK hqa
      _ ≤ ∫ a, q a ^ 2 ∂muI n :=
          setIntegral_le_integral iq (Filter.Eventually.of_forall fun a => sq_nonneg _)
      _ = (CA / σl ^ 2 * (1 - η)⁻¹) ^ 2 *
            ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) ^ 2 ∂muI n := by
          rw [← integral_const_mul]; congr 1; funext a; simp only [hq]; ring
      _ ≤ (CA / σl ^ 2 * (1 - η)⁻¹) ^ 2 * Vl ^ 2 := mul_le_mul_of_nonneg_left hVl (sq_nonneg _)
      _ = _ := by ring
  -- (Ie_k)
  have Ie : ∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ (2 * k) ∂ν ∂muI n ≤ τ ^ (2 * k) →
      ∫ a in K, condMom d (epsF D c d) (2 * k) a ∂muI n ≤
        (cEw ws σl * ((iotaP η (2 * k) + c2η η + c3η η ws σl) * τ)) ^ (2 * k) := by
    intro k hk τ hτ hMτ
    have hp : 2 * k ≠ 0 := by omega
    refine int_three (muI n) mK (mMs (2 * k)) (msd (fun a v => sgA D c a v - gbar D c a) mVs)
      (Kb := Ks ^ (2 * k) + Ks) (fun a => ?_) (fun a => ?_) ?_ (fun a => (bMs _ a).1)
      (fun a => Real.sqrt_nonneg _) (fun a => ?_) hcE (iotaP_pos h1 _) (iotaP_pow h1 hp) hc2 hc3
      hτ (fun a ha => ?_) hMτ
    · rw [abs_of_nonneg (bMs _ a).1]; linarith [(bMs (2 * k) a).2]
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have : √(∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) ≤ Ks := by
        rw [show Ks = √(Ks ^ 2) from (Real.sqrt_sq hKs0).symm]; exact Real.sqrt_le_sqrt (bVs a).2
      have : 0 ≤ Ks ^ (2 * k) := pow_nonneg hKs0 _
      linarith
    · refine Integrable.of_bound (measurable_condMom d mE _).aestronglyMeasurable
        (eps0 ws σl ^ (2 * k)) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) hp
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    · rw [sd_pow (bVs a).1]
      have := jensen_pow ν (((mS a).sub_const (gbar D c a))) (bYs a) k
      simpa using this
    · obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      rw [cm_eps hn D c h0 h1 ha hp]
      exact idx_eps_mom (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ hm1 h1 (2 * k)
        (mul_pos (iotaP_pos h1 _) hτ) (mul_pos hc2 hτ) (mul_pos hc3 hτ)
  -- (Id_k)
  have Id : ∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ (2 * k) ∂ν ∂muI n ≤ τ ^ (2 * k) →
      ∫ a in K, condMom d (delF D c d) (2 * k) a ∂muI n ≤
        (√CA / σl * ((iotaP η (2 * k) + c2η η) * τ)) ^ (2 * k) := by
    intro k hk τ hτ hMτ
    have hp : 2 * k ≠ 0 := by omega
    refine int_two (muI n) mK (mMl (2 * k)) (msd (fun a v => lA D c a v - lbar D c a) mVl)
      (Kb := Kl ^ (2 * k) + Kl) (fun a => ?_) (fun a => ?_) ?_ (fun a => (bMl _ a).1)
      (fun a => Real.sqrt_nonneg _) (fun a => ?_) (by positivity) (iotaP_pos h1 _)
      (iotaP_pow h1 hp) hc2 hτ (fun a ha => ?_) hMτ
    · rw [abs_of_nonneg (bMl _ a).1]; linarith [(bMl (2 * k) a).2]
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have : √(∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) ≤ Kl := by
        rw [show Kl = √(Kl ^ 2) from (Real.sqrt_sq hKl0).symm]; exact Real.sqrt_le_sqrt (bVl a).2
      have : 0 ≤ Kl ^ (2 * k) := pow_nonneg hKl0 _
      linarith
    · refine Integrable.of_bound (measurable_condMom d mD _).aestronglyMeasurable
        (L ^ (2 * k)) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) hp
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    · rw [sd_pow (bVl a).1]
      have := jensen_pow ν (((mLa a).sub_const (lbar D c a))) (bYl a) k
      simpa using this
    · obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      have hS0 : σl ^ 2 ≤ ∫ w, sgA D c a w ^ 2 ∂nrm ν (slice d a) := hS ▸ (hwin a ha).1
      rw [cm_del hn D c h0 h1 ha hp]
      have h := idx_del_mom (measurableSet_slice d a) hm (mLa a) (bLa a) hσl hS0
        (normSq_nonneg c.2.1.2) hm1 h1 (2 * k) (mul_pos (iotaP_pos h1 (2 * k)) hτ) (mul_pos hc2 hτ)
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt hCA) hσl.le) _)
          (pow_nonneg (add_pos (mul_pos (iotaP_pos h1 (2 * k)) hτ) (mul_pos hc2 hτ)).le _)) ?_)
      have := (bMl (2 * k) a).1
      have : 0 < iotaP η (2 * k) * τ := mul_pos (iotaP_pos h1 _) hτ
      have : 0 < c2η η * τ := mul_pos hc2 hτ
      have : (0 : ℝ) ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
      positivity
  have hi8 := iotaP_pos h1 8
  have hi12 := iotaP_pos h1 12
  exact fluct_of_moments D c d hε0 hε (by positivity) hL0 (by positivity) hcA
    (fun a ha => ⟨(hwin a ha).1, fun v hv => ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.1,
      ((hwin a ha).2 v hv).2.2⟩⟩) hcent
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hB hD IA ID (Ie 4 (by norm_num) ts8 hts8 hs8) (Id 4 (by norm_num) tl8 htl8 hl8)
    (Ie 6 (by norm_num) ts12 hts12 hs12) (Id 6 (by norm_num) tl12 htl12 hl12) hsum

end paper

end BstLean.Part162

open BstLean.Part162 in
#print axioms fluct_paper
