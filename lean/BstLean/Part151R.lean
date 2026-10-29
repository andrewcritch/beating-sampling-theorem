import BstLean.Part149LemmaC
import BstLean.Part135Dir
import BstLean.Part131Block

/-!
# Part 151, item 4 (a): Lemma R (ReLU contraction), parts (ii) and (iii)

Role: `delegations/statements/p151-spec.md`, item 4 (a). Paper source:
`proofs/option-n/theorem5-04-standin-structure.tex`, Lemma R. Part (i) is `relu_lip_sq`
(Part 149).

The Gaussian row is `w = √v • ξ`, `ξ` a standard Gaussian vector of `ℝ^d` (`stdGauss (Fin d)`),
`v ≥ 0`: the distribution `N(0, v·I_d)`.

* `lemmaR_ii`: `E (relu(w·h) − relu(w·h'))² ≤ (v/2)·|h − h'|²`.
* Setting of (iii): a probability space `(Ω', P)`, measurable `h h' : Ω' → ℝ^d` with
  `E|h − h'|² < ∞` (`Integrable (fun ω => normSq (h ω - h' ω)) P`).
  `XR P h h' w = (E_ω[relu(w·h) − relu(w·h')])²`, `QR P h h' w = E_ω (w·(h − h'))²`
  (the quadratic form `wᵀMw`, `M = E (h − h')(h − h')ᵀ`), `TR P h h' = E_ω |h − h'|²` (`tr M`).
* `lemmaR_iii_le`: `XR w ≤ QR w`.
* `lemmaR_iii_mean`: `E_w XR ≤ (v/2)·T`.
* `lemmaR_iii_sq`: `E_w XR² ≤ 3v²T²`.
* `lemmaR_iii_four`: `E_w XR⁴ ≤ 105v⁴T⁴`.
* `QR_mean`, `QR_sq`, `QR_four`: the same moment bounds for the quadratic form `QR` itself
  (constants `1`, `3`, `105`).
* `row_map`: a row of a Gaussian matrix has the distribution of `√v • ξ`; `lemmaR_row_mean`,
  `lemmaR_row_sq`, `lemmaR_row_four`: the bounds of (iii) for row `i` of `M ∼ gaussMat m d v`.

The expectations over `w` are written with `∫⁻` and `ENNReal.ofReal`, so no integrability over
`w` is assumed or needed.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130
open BstLean.Part131 (stdGauss_dot)
open BstLean.Part149 (relu_lip_sq)

variable {d : ℕ}

/-! ## Scalar facts -/

lemma dot_sq_le (w δ : Fin d → ℝ) : (w ⬝ᵥ δ) ^ 2 ≤ normSq w * normSq δ := by
  unfold dotProduct normSq
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma dot_self_eq (δ : Fin d → ℝ) : δ ⬝ᵥ δ = normSq δ := by
  simp [dotProduct, normSq, pow_two]

lemma gaussMom_even_pos (p : ℕ) : 0 < gaussMom (2 * p) := by
  simp only [gaussMom, even_two_mul, ↓reduceIte]
  exact_mod_cast Nat.doubleFactorial_pos _

lemma gaussMom_two : gaussMom (2 * 1) = 1 := by
  simp [gaussMom]

lemma gaussMom_four : gaussMom (2 * 2) = 3 := by
  simp only [gaussMom, even_two_mul, ↓reduceIte]
  norm_num [Nat.doubleFactorial]

lemma gaussMom_eight : gaussMom (2 * 4) = 105 := by
  simp only [gaussMom, even_two_mul, ↓reduceIte]
  norm_num [Nat.doubleFactorial]

lemma mom_int (p : ℕ) : Integrable (fun x : ℝ => x ^ (2 * p)) (gaussianReal 0 1) := by
  by_contra h
  have h1 := gaussMom_eq (2 * p)
  rw [integral_undef h] at h1
  exact absurd h1 (gaussMom_even_pos p).ne

lemma even_pow_nonneg (p : ℕ) (x : ℝ) : 0 ≤ x ^ (2 * p) := by
  rw [pow_mul]; positivity

lemma mom_lint (p : ℕ) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * p)) ∂gaussianReal 0 1 = ENNReal.ofReal (gaussMom (2 * p)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (mom_int p)
    (Filter.Eventually.of_forall fun x => even_pow_nonneg p x), gaussMom_eq]

lemma measurable_dot_left (δ : Fin d → ℝ) : Measurable (fun ξ : Fin d → ℝ => ξ ⬝ᵥ δ) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul measurable_const

/-- **The even moments of a linear form of a standard Gaussian vector**:
`E (ξ·δ)^{2p} = (2p − 1)!!·|δ|^{2p}`. -/
lemma dot_mom (p : ℕ) (δ : Fin d → ℝ) :
    ∫⁻ ξ, ENNReal.ofReal ((ξ ⬝ᵥ δ) ^ (2 * p)) ∂stdGauss (Fin d) =
      ENNReal.ofReal (gaussMom (2 * p) * normSq δ ^ p) := by
  have hs : 0 ≤ normSq δ := normSq_nonneg δ
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (2 * p))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have h1 := lintegral_map (μ := stdGauss (Fin d)) hf (measurable_dot_left δ)
  rw [stdGauss_dot, dot_self_eq] at h1
  have hmap : gaussianReal 0 (normSq δ).toNNReal =
      (gaussianReal 0 1).map (fun x => √(normSq δ) * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hs, Real.coe_toNNReal _ hs]
  rw [← h1, hmap, lintegral_map hf (by fun_prop)]
  have e : ∀ x : ℝ, ENNReal.ofReal ((√(normSq δ) * x) ^ (2 * p)) =
      ENNReal.ofReal (normSq δ ^ p) * ENNReal.ofReal (x ^ (2 * p)) := by
    intro x
    rw [← ENNReal.ofReal_mul (pow_nonneg hs _)]
    congr 1
    rw [mul_pow, pow_mul, Real.sq_sqrt hs]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mom_lint,
    ← ENNReal.ofReal_mul (pow_nonneg hs _), mul_comm]

lemma sdot_sq {v : ℝ} (hv : 0 ≤ v) (ξ δ : Fin d → ℝ) :
    ((√v • ξ) ⬝ᵥ δ) ^ 2 = v * (ξ ⬝ᵥ δ) ^ 2 := by
  rw [smul_dotProduct, smul_eq_mul, mul_pow, Real.sq_sqrt hv]

lemma measurable_sdot {Ω' : Type*} [MeasurableSpace Ω'] {δ : Ω' → Fin d → ℝ} (hδ : Measurable δ)
    (v : ℝ) : Measurable (fun q : (Fin d → ℝ) × Ω' => (√v • q.1) ⬝ᵥ δ q.2) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).mul
    ((measurable_pi_apply i).comp (hδ.comp measurable_snd))

lemma measurable_dot_right {Ω' : Type*} [MeasurableSpace Ω'] {δ : Ω' → Fin d → ℝ}
    (hδ : Measurable δ) (w : Fin d → ℝ) : Measurable (fun ω => w ⬝ᵥ δ ω) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul ((measurable_pi_apply i).comp hδ)

/-! ## Lemma R (ii) -/

/-- **Lemma R (ii)**: for `w ∼ N(0, v·I_d)` (`w = √v • ξ`) and `h, h' ∈ ℝ^d`:
`E (relu(w·h) − relu(w·h'))² ≤ (v/2)·|h − h'|²`. -/
theorem lemmaR_ii {v : ℝ} (hv : 0 ≤ v) (h h' : Fin d → ℝ) :
    ∫⁻ ξ, ENNReal.ofReal ((relu ((√v • ξ) ⬝ᵥ h) - relu ((√v • ξ) ⬝ᵥ h')) ^ 2)
        ∂stdGauss (Fin d) ≤ ENNReal.ofReal (v / 2 * normSq (h - h')) := by
  set f : (Fin d → ℝ) → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((relu ((√v • ξ) ⬝ᵥ h) - relu ((√v • ξ) ⬝ᵥ h')) ^ 2) with hf
  have hdm : ∀ u : Fin d → ℝ, Measurable (fun ξ : Fin d → ℝ => (√v • ξ) ⬝ᵥ u) := by
    intro u
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_const.mul (measurable_pi_apply i)).mul measurable_const
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp
    (((measurable_relu.comp (hdm h)).sub (measurable_relu.comp (hdm h'))).pow_const 2)
  have hneg : ∫⁻ ξ, f (-ξ) ∂stdGauss (Fin d) = ∫⁻ ξ, f ξ ∂stdGauss (Fin d) := by
    have h1 := lintegral_map (μ := stdGauss (Fin d)) hfm
      (measurable_neg : Measurable fun ξ : Fin d → ℝ => -ξ)
    rw [BstLean.Part135.stdGauss_neg] at h1
    exact h1.symm
  have hpt : ∀ ξ, f ξ + f (-ξ) ≤
      ENNReal.ofReal v * ENNReal.ofReal ((ξ ⬝ᵥ (h - h')) ^ (2 * 1)) := by
    intro ξ
    simp only [hf]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_mul hv]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := relu_lip_sq ((√v • ξ) ⬝ᵥ h) ((√v • ξ) ⬝ᵥ h')
    have e1 : (√v • -ξ) ⬝ᵥ h = -((√v • ξ) ⬝ᵥ h) := by rw [smul_neg, neg_dotProduct]
    have e2 : (√v • -ξ) ⬝ᵥ h' = -((√v • ξ) ⬝ᵥ h') := by rw [smul_neg, neg_dotProduct]
    rw [e1, e2]
    refine h0.trans (le_of_eq ?_)
    rw [← dotProduct_sub, sdot_sq hv, mul_one]
  have hsum : ∫⁻ ξ, (f ξ + f (-ξ)) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (v * normSq (h - h')) := by
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, dot_mom 1, gaussMom_two,
      ← ENNReal.ofReal_mul hv]
    congr 1
    ring
  rw [lintegral_add_left hfm, hneg] at hsum
  have e : ENNReal.ofReal (v * normSq (h - h')) =
      ENNReal.ofReal (v / 2 * normSq (h - h')) + ENNReal.ofReal (v / 2 * normSq (h - h')) := by
    have := normSq_nonneg (h - h')
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  by_contra hc
  push Not at hc
  rw [e] at hsum
  exact absurd hsum (not_le.mpr (ENNReal.add_lt_add hc hc))

/-! ## The weighted Cauchy–Schwarz inequality -/

section iii

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- `(∫ f)² ≤ (∫ D)·(∫ g)` if `f² ≤ D·g` pointwise, `D, g ≥ 0`. -/
lemma wcs {P : Measure Ω'} {f D g : Ω' → ℝ} (hf : Integrable f P) (hD : Integrable D P)
    (hg : Integrable g P) (hD0 : ∀ ω, 0 ≤ D ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfg : ∀ ω, f ω ^ 2 ≤ D ω * g ω) :
    (∫ ω, f ω ∂P) ^ 2 ≤ (∫ ω, D ω ∂P) * ∫ ω, g ω ∂P := by
  have hT0 : 0 ≤ ∫ ω, D ω ∂P := integral_nonneg hD0
  have pos : ∀ t : ℝ, 0 ≤ t ^ 2 * (∫ ω, D ω ∂P) - 2 * t * (∫ ω, f ω ∂P) + ∫ ω, g ω ∂P := by
    intro t
    have hpt : ∀ ω, 0 ≤ t ^ 2 * D ω - 2 * t * f ω + g ω := by
      intro ω
      rcases (hD0 ω).eq_or_lt with h0 | hpos
      · have h2 := hfg ω
        rw [← h0, zero_mul] at h2
        have hf0 : f ω = 0 := by
          have : f ω ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
          exact pow_eq_zero_iff (two_ne_zero) |>.mp this
        rw [← h0, hf0]
        simpa using hg0 ω
      · have h1 : 0 ≤ (t * D ω - f ω) ^ 2 := sq_nonneg _
        have h2 := hfg ω
        have h3 : 0 ≤ D ω * (t ^ 2 * D ω - 2 * t * f ω + g ω) := by nlinarith
        by_contra hneg
        push Not at hneg
        nlinarith
    have h : 0 ≤ ∫ ω, (t ^ 2 * D ω - 2 * t * f ω + g ω) ∂P :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall hpt)
    rw [integral_add (f := fun ω => t ^ 2 * D ω - 2 * t * f ω) (g := g)
        ((hD.const_mul _).sub (hf.const_mul _)) hg,
      integral_sub (f := fun ω => t ^ 2 * D ω) (g := fun ω => 2 * t * f ω)
        (hD.const_mul _) (hf.const_mul _), integral_const_mul, integral_const_mul] at h
    exact h
  rcases hT0.eq_or_lt with h0 | hTpos
  · have hF : ∫ ω, f ω ∂P = 0 := by
      by_contra hne
      have h1 := pos ((∫ ω, g ω ∂P + 1) / (2 * ∫ ω, f ω ∂P))
      rw [← h0] at h1
      have e : 2 * ((∫ ω, g ω ∂P + 1) / (2 * ∫ ω, f ω ∂P)) * (∫ ω, f ω ∂P) =
          ∫ ω, g ω ∂P + 1 := by field_simp
      nlinarith
    rw [hF, ← h0]
    simp
  · have h1 := pos ((∫ ω, f ω ∂P) / ∫ ω, D ω ∂P)
    have e : ((∫ ω, f ω ∂P) / ∫ ω, D ω ∂P) ^ 2 * (∫ ω, D ω ∂P) -
        2 * ((∫ ω, f ω ∂P) / ∫ ω, D ω ∂P) * (∫ ω, f ω ∂P) + ∫ ω, g ω ∂P =
        ∫ ω, g ω ∂P - (∫ ω, f ω ∂P) ^ 2 / ∫ ω, D ω ∂P := by
      field_simp
      ring
    rw [e] at h1
    have h2 : (∫ ω, f ω ∂P) ^ 2 / ∫ ω, D ω ∂P ≤ ∫ ω, g ω ∂P := by linarith
    rw [div_le_iff₀ hTpos] at h2
    linarith

/-! ## The weights -/

/-- `x^p / D^{p−1}`. With `x = (w·δ)²` and `D = |δ|²`: the integrand of the weighted Hölder
bound. -/
noncomputable def gfun (p : ℕ) (x D : ℝ) : ℝ := x ^ p / D ^ (p - 1)

lemma gfun_nonneg (p : ℕ) {x D : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D) : 0 ≤ gfun p x D := by
  unfold gfun; positivity

lemma gfun_one (x D : ℝ) : gfun 1 x D = x := by simp [gfun]

lemma gfun_le {p : ℕ} (hp : 1 ≤ p) {x D N : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hxD : x ≤ N * D) : gfun p x D ≤ N ^ p * D := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [gfun, Nat.add_sub_cancel]
  rcases hD.eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by
      rw [← h0, mul_zero] at hxD
      exact le_antisymm hxD hx
    rw [hx0, ← h0]
    simp
  · rw [div_le_iff₀ (pow_pos hpos _)]
    calc x ^ (q + 1) ≤ (N * D) ^ (q + 1) := pow_le_pow_left₀ hx hxD _
      _ = N ^ (q + 1) * D * D ^ q := by ring

lemma gfun_sq {p : ℕ} (hp : 1 ≤ p) {x D : ℝ} (hxD : D = 0 → x = 0) :
    gfun p x D ^ 2 = D * gfun (2 * p) x D := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  simp only [gfun, Nat.add_sub_cancel, e]
  by_cases hD0 : D = 0
  · rw [hxD hD0, hD0]
    simp
  · field_simp
    ring

/-! ## The setting of Lemma R (iii) -/

/-- `X(w) = (E_ω[relu(w·h) − relu(w·h')])²`. -/
noncomputable def XR (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) (w : Fin d → ℝ) : ℝ :=
  (∫ ω, (relu (w ⬝ᵥ h ω) - relu (w ⬝ᵥ h' ω)) ∂P) ^ 2

/-- The quadratic form `wᵀMw = E_ω (w·(h − h'))²`, `M = E (h − h')(h − h')ᵀ`. -/
noncomputable def QR (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) (w : Fin d → ℝ) : ℝ :=
  ∫ ω, (w ⬝ᵥ (h ω - h' ω)) ^ 2 ∂P

/-- `T = tr M = E_ω |h − h'|²`. -/
noncomputable def TR (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) : ℝ :=
  ∫ ω, normSq (h ω - h' ω) ∂P

/-- `E_ω (w·δ)^{2p}/|δ|^{2(p−1)}`, `δ = h − h'`. -/
noncomputable def IR (p : ℕ) (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) (w : Fin d → ℝ) : ℝ :=
  ∫ ω, gfun p ((w ⬝ᵥ (h ω - h' ω)) ^ 2) (normSq (h ω - h' ω)) ∂P

lemma XR_nonneg (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) (w : Fin d → ℝ) : 0 ≤ XR P h h' w :=
  sq_nonneg _

lemma QR_nonneg (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) (w : Fin d → ℝ) : 0 ≤ QR P h h' w :=
  integral_nonneg fun _ => sq_nonneg _

lemma TR_nonneg (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) : 0 ≤ TR P h h' :=
  integral_nonneg fun _ => normSq_nonneg _

lemma IR_nonneg (p : ℕ) (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) (w : Fin d → ℝ) :
    0 ≤ IR p P h h' w :=
  integral_nonneg fun _ => gfun_nonneg p (sq_nonneg _) (normSq_nonneg _)

lemma IR_one (P : Measure Ω') (h h' : Ω' → Fin d → ℝ) (w : Fin d → ℝ) :
    IR 1 P h h' w = QR P h h' w := by
  simp [IR, QR, gfun_one]

variable {P : Measure Ω'} {h h' : Ω' → Fin d → ℝ}

lemma gfun_meas (hh : Measurable h) (hh' : Measurable h') (p : ℕ) (w : Fin d → ℝ) :
    Measurable (fun ω => gfun p ((w ⬝ᵥ (h ω - h' ω)) ^ 2) (normSq (h ω - h' ω))) := by
  unfold gfun
  exact (((measurable_dot_right (hh.sub hh') w).pow_const 2).pow_const p).div
    ((measurable_normSq.comp (hh.sub hh')).pow_const _)

lemma gfun_int (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {p : ℕ} (hp : 1 ≤ p) (w : Fin d → ℝ) :
    Integrable (fun ω => gfun p ((w ⬝ᵥ (h ω - h' ω)) ^ 2) (normSq (h ω - h' ω))) P := by
  refine (hT.const_mul (normSq w ^ p)).mono' (gfun_meas hh hh' p w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gfun_nonneg p (sq_nonneg _) (normSq_nonneg _))]
  exact gfun_le hp (sq_nonneg _) (normSq_nonneg _) (dot_sq_le _ _)

/-- The Hölder step: `IR_p² ≤ T·IR_{2p}`. -/
lemma IR_step (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {p : ℕ} (hp : 1 ≤ p) (w : Fin d → ℝ) :
    IR p P h h' w ^ 2 ≤ TR P h h' * IR (2 * p) P h h' w := by
  unfold IR TR
  refine wcs (gfun_int hh hh' hT hp w) hT (gfun_int hh hh' hT (by omega) w)
    (fun ω => normSq_nonneg _) (fun ω => gfun_nonneg _ (sq_nonneg _) (normSq_nonneg _))
    (fun ω => le_of_eq (gfun_sq hp ?_))
  intro h0
  have h1 := dot_sq_le w (h ω - h' ω)
  rw [h0, mul_zero] at h1
  exact le_antisymm h1 (sq_nonneg _)

lemma relu_diff_sq_le (w a b : Fin d → ℝ) :
    (relu (w ⬝ᵥ a) - relu (w ⬝ᵥ b)) ^ 2 ≤ (w ⬝ᵥ (a - b)) ^ 2 := by
  have h0 := relu_lip_sq (w ⬝ᵥ a) (w ⬝ᵥ b)
  rw [dotProduct_sub]
  nlinarith [sq_nonneg (relu (-(w ⬝ᵥ a)) - relu (-(w ⬝ᵥ b)))]

lemma rdiff_meas (hh : Measurable h) (hh' : Measurable h') (w : Fin d → ℝ) :
    Measurable (fun ω => (relu (w ⬝ᵥ h ω) - relu (w ⬝ᵥ h' ω)) ^ 2) :=
  ((measurable_relu.comp (measurable_dot_right hh w)).sub
    (measurable_relu.comp (measurable_dot_right hh' w))).pow_const 2

lemma qint (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) (w : Fin d → ℝ) :
    Integrable (fun ω => (w ⬝ᵥ (h ω - h' ω)) ^ 2) P := by
  have := gfun_int hh hh' hT (le_refl 1) w
  simpa only [gfun_one] using this

lemma rdiff_int (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) (w : Fin d → ℝ) :
    Integrable (fun ω => (relu (w ⬝ᵥ h ω) - relu (w ⬝ᵥ h' ω)) ^ 2) P := by
  refine (qint hh hh' hT w).mono' (rdiff_meas hh hh' w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact relu_diff_sq_le _ _ _

/-- Jensen: `X(w) ≤ E_ω (relu(w·h) − relu(w·h'))²`. -/
lemma XR_le_sq [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) (w : Fin d → ℝ) :
    XR P h h' w ≤ ∫ ω, (relu (w ⬝ᵥ h ω) - relu (w ⬝ᵥ h' ω)) ^ 2 ∂P :=
  BstLean.Part133.sq_integral_le (rdiff_int hh hh' hT w)

/-- **Lemma R (iii), second bound**: `X(w) ≤ wᵀMw`, for every `w`. -/
theorem lemmaR_iii_le [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) (w : Fin d → ℝ) :
    XR P h h' w ≤ QR P h h' w :=
  (XR_le_sq hh hh' hT w).trans
    (integral_mono (rdiff_int hh hh' hT w) (qint hh hh' hT w) fun _ => relu_diff_sq_le _ _ _)

/-! ## The means over the Gaussian row -/

/-- `E_w IR_p(w) ≤ (2p − 1)!!·v^p·T` for `w = √v • ξ`. -/
lemma EI_le [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) {p : ℕ}
    (hp : 1 ≤ p) :
    ∫⁻ ξ, ENNReal.ofReal (IR p P h h' (√v • ξ)) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (gaussMom (2 * p) * v ^ p * TR P h h') := by
  have hmom := (gaussMom_even_pos p).le
  have e : ∀ ξ : Fin d → ℝ, ENNReal.ofReal (IR p P h h' (√v • ξ)) =
      ∫⁻ ω, ENNReal.ofReal (gfun p (((√v • ξ) ⬝ᵥ (h ω - h' ω)) ^ 2) (normSq (h ω - h' ω))) ∂P :=
    fun ξ => ofReal_integral_eq_lintegral_ofReal (gfun_int hh hh' hT hp _)
      (Filter.Eventually.of_forall fun ω => gfun_nonneg p (sq_nonneg _) (normSq_nonneg _))
  simp_rw [e]
  have hmeas : Measurable (fun q : (Fin d → ℝ) × Ω' =>
      ENNReal.ofReal (gfun p (((√v • q.1) ⬝ᵥ (h q.2 - h' q.2)) ^ 2)
        (normSq (h q.2 - h' q.2)))) := by
    unfold gfun
    refine ENNReal.measurable_ofReal.comp (Measurable.div ?_ ?_)
    · exact ((measurable_sdot (hh.sub hh') v).pow_const 2).pow_const p
    · exact ((measurable_normSq.comp (hh.sub hh')).comp measurable_snd).pow_const _
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hin : ∀ ω, ∫⁻ ξ, ENNReal.ofReal (gfun p (((√v • ξ) ⬝ᵥ (h ω - h' ω)) ^ 2)
      (normSq (h ω - h' ω))) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (gaussMom (2 * p) * v ^ p * normSq (h ω - h' ω)) := by
    intro ω
    set D := normSq (h ω - h' ω) with hD
    have hD0 : 0 ≤ D := normSq_nonneg _
    have e2 : ∀ ξ : Fin d → ℝ, ENNReal.ofReal (gfun p (((√v • ξ) ⬝ᵥ (h ω - h' ω)) ^ 2) D) =
        ENNReal.ofReal (v ^ p / D ^ (p - 1)) *
          ENNReal.ofReal ((ξ ⬝ᵥ (h ω - h' ω)) ^ (2 * p)) := by
      intro ξ
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold gfun
      rw [sdot_sq hv, mul_pow, ← pow_mul]
      ring
    simp_rw [e2]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, dot_mom, ← hD,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases hD0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · refine le_of_eq ?_
      field_simp
      ring
  refine (lintegral_mono hin).trans (le_of_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (hT.const_mul _)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (by positivity) (normSq_nonneg _)),
    integral_const_mul]
  rfl

/-- `E_w [c·IR_p(w)] ≤ c·(2p − 1)!!·v^p·T` for `c ≥ 0`. -/
lemma EI_mul_le [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) {p : ℕ}
    (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ ξ, ENNReal.ofReal (c * IR p P h h' (√v • ξ)) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (c * (gaussMom (2 * p) * v ^ p * TR P h h')) := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl (EI_le hh hh' hT hv hp)

/-- **Lemma R (iii), first bound**: `E_w X(w) ≤ (v/2)·T`. -/
theorem lemmaR_iii_mean [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (XR P h h' (√v • ξ)) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (v / 2 * TR P h h') := by
  have h1 : ∀ ξ : Fin d → ℝ, ENNReal.ofReal (XR P h h' (√v • ξ)) ≤
      ∫⁻ ω, ENNReal.ofReal ((relu ((√v • ξ) ⬝ᵥ h ω) - relu ((√v • ξ) ⬝ᵥ h' ω)) ^ 2) ∂P := by
    intro ξ
    rw [← ofReal_integral_eq_lintegral_ofReal (rdiff_int hh hh' hT _)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (XR_le_sq hh hh' hT _)
  refine (lintegral_mono h1).trans ?_
  have hmeas : Measurable (fun q : (Fin d → ℝ) × Ω' =>
      ENNReal.ofReal ((relu ((√v • q.1) ⬝ᵥ h q.2) - relu ((√v • q.1) ⬝ᵥ h' q.2)) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_relu.comp (measurable_sdot hh v)).sub
      (measurable_relu.comp (measurable_sdot hh' v))).pow_const 2)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine (lintegral_mono fun ω => lemmaR_ii hv (h ω) (h' ω)).trans (le_of_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (hT.const_mul _)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (by positivity) (normSq_nonneg _)),
    integral_const_mul]
  rfl

/-- The mean of the quadratic form: `E_w wᵀMw ≤ v·T` (equality holds). -/
theorem QR_mean [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (QR P h h' (√v • ξ)) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (v * TR P h h') := by
  have h1 := EI_le hh hh' hT hv (le_refl 1)
  simp_rw [IR_one] at h1
  rw [gaussMom_two] at h1
  simpa using h1

/-- The second moment of the quadratic form: `E_w (wᵀMw)² ≤ 3v²T²`. -/
theorem QR_sq [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (QR P h h' (√v • ξ) ^ 2) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (3 * v ^ 2 * TR P h h' ^ 2) := by
  have hT0 := TR_nonneg P h h'
  have h1 : ∀ ξ : Fin d → ℝ, ENNReal.ofReal (QR P h h' (√v • ξ) ^ 2) ≤
      ENNReal.ofReal (TR P h h' * IR (2 * 1) P h h' (√v • ξ)) := by
    intro ξ
    rw [← IR_one]
    exact ENNReal.ofReal_le_ofReal (IR_step hh hh' hT (le_refl 1) _)
  refine (lintegral_mono h1).trans ((EI_mul_le hh hh' hT hv (by norm_num) hT0).trans
    (le_of_eq ?_))
  rw [gaussMom_four]
  congr 1
  ring

/-- The fourth moment of the quadratic form: `E_w (wᵀMw)⁴ ≤ 105v⁴T⁴`. -/
theorem QR_four [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (QR P h h' (√v • ξ) ^ 4) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (105 * v ^ 4 * TR P h h' ^ 4) := by
  have hT0 := TR_nonneg P h h'
  have h1 : ∀ ξ : Fin d → ℝ, ENNReal.ofReal (QR P h h' (√v • ξ) ^ 4) ≤
      ENNReal.ofReal (TR P h h' ^ 3 * IR (2 * 2) P h h' (√v • ξ)) := by
    intro ξ
    refine ENNReal.ofReal_le_ofReal ?_
    have s1 := IR_step hh hh' hT (le_refl 1) (√v • ξ)
    have s2 := IR_step hh hh' hT (p := 2) (by norm_num) (√v • ξ)
    rw [IR_one] at s1
    have hI2 := IR_nonneg (2 * 1) P h h' (√v • ξ)
    have hQ := QR_nonneg P h h' (√v • ξ)
    calc QR P h h' (√v • ξ) ^ 4 = (QR P h h' (√v • ξ) ^ 2) ^ 2 := by ring
      _ ≤ (TR P h h' * IR (2 * 1) P h h' (√v • ξ)) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) s1 2
      _ = TR P h h' ^ 2 * IR 2 P h h' (√v • ξ) ^ 2 := by ring
      _ ≤ TR P h h' ^ 2 * (TR P h h' * IR (2 * 2) P h h' (√v • ξ)) :=
          mul_le_mul_of_nonneg_left s2 (sq_nonneg _)
      _ = _ := by ring
  refine (lintegral_mono h1).trans ((EI_mul_le hh hh' hT hv (by norm_num)
    (pow_nonneg hT0 3)).trans (le_of_eq ?_))
  rw [gaussMom_eight]
  congr 1
  ring

/-- **Lemma R (iii), third bound**: `E_w X(w)² ≤ 3v²T²`. -/
theorem lemmaR_iii_sq [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (XR P h h' (√v • ξ) ^ 2) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (3 * v ^ 2 * TR P h h' ^ 2) :=
  (lintegral_mono fun _ => ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (XR_nonneg P h h' _) (lemmaR_iii_le hh hh' hT _) 2)).trans
    (QR_sq hh hh' hT hv)

/-- **Lemma R (iii), fourth bound**: `E_w X(w)⁴ ≤ 105v⁴T⁴`. -/
theorem lemmaR_iii_four [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (XR P h h' (√v • ξ) ^ 4) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (105 * v ^ 4 * TR P h h' ^ 4) :=
  (lintegral_mono fun _ => ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (XR_nonneg P h h' _) (lemmaR_iii_le hh hh' hT _) 4)).trans
    (QR_four hh hh' hT hv)

/-! ## A row of a Gaussian matrix -/

lemma measurable_dot_joint (hδ : Measurable h) :
    Measurable (fun q : (Fin d → ℝ) × Ω' => q.1 ⬝ᵥ h q.2) := by
  simp only [dotProduct]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply i).comp (hδ.comp measurable_snd))

lemma XR_meas [SFinite P] (hh : Measurable h) (hh' : Measurable h') :
    Measurable (XR P h h') := by
  unfold XR
  refine Measurable.pow_const (StronglyMeasurable.measurable ?_) 2
  refine StronglyMeasurable.integral_prod_right'
    (f := fun q : (Fin d → ℝ) × Ω' => relu (q.1 ⬝ᵥ h q.2) - relu (q.1 ⬝ᵥ h' q.2)) ?_
  exact ((measurable_relu.comp (measurable_dot_joint hh)).sub
    (measurable_relu.comp (measurable_dot_joint hh'))).stronglyMeasurable

lemma QR_meas [SFinite P] (hh : Measurable h) (hh' : Measurable h') :
    Measurable (QR P h h') := by
  unfold QR
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right'
    (f := fun q : (Fin d → ℝ) × Ω' => (q.1 ⬝ᵥ (h q.2 - h' q.2)) ^ 2) ?_
  exact ((measurable_dot_joint (hh.sub hh')).pow_const 2).stronglyMeasurable

/-- **A row of a Gaussian matrix has the distribution of `√v • ξ`** (transfer of a nonnegative
integral; from `gaussMat_row` of Part 130). -/
lemma row_map {m : ℕ} (i : Fin m) (v : ℝ) {F : (Fin d → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ M, F (rowOf i M) ∂gaussMat m d v = ∫⁻ ξ, F (√v • ξ) ∂stdGauss (Fin d) := by
  rw [← lintegral_map hF (measurable_rowOf i), gaussMat_row,
    lintegral_map hF (measurable_const_smul _)]

/-- **Lemma R (iii) for row `i` of a Gaussian matrix `M` (`m × d`, entry variance `v`)**:
`E_M X(row_i M) ≤ (v/2)·T`. -/
theorem lemmaR_row_mean [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) {m : ℕ}
    (i : Fin m) :
    ∫⁻ M, ENNReal.ofReal (XR P h h' (rowOf i M)) ∂gaussMat m d v ≤
      ENNReal.ofReal (v / 2 * TR P h h') := by
  rw [row_map i v (F := fun w => ENNReal.ofReal (XR P h h' w))
    (ENNReal.measurable_ofReal.comp (XR_meas hh hh'))]
  exact lemmaR_iii_mean hh hh' hT hv

/-- `E_M X(row_i M)² ≤ 3v²T²`. -/
theorem lemmaR_row_sq [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) {m : ℕ}
    (i : Fin m) :
    ∫⁻ M, ENNReal.ofReal (XR P h h' (rowOf i M) ^ 2) ∂gaussMat m d v ≤
      ENNReal.ofReal (3 * v ^ 2 * TR P h h' ^ 2) := by
  rw [row_map i v (F := fun w => ENNReal.ofReal (XR P h h' w ^ 2))
    (ENNReal.measurable_ofReal.comp ((XR_meas hh hh').pow_const 2))]
  exact lemmaR_iii_sq hh hh' hT hv

/-- `E_M X(row_i M)⁴ ≤ 105v⁴T⁴`. -/
theorem lemmaR_row_four [IsProbabilityMeasure P] (hh : Measurable h) (hh' : Measurable h')
    (hT : Integrable (fun ω => normSq (h ω - h' ω)) P) {v : ℝ} (hv : 0 ≤ v) {m : ℕ}
    (i : Fin m) :
    ∫⁻ M, ENNReal.ofReal (XR P h h' (rowOf i M) ^ 4) ∂gaussMat m d v ≤
      ENNReal.ofReal (105 * v ^ 4 * TR P h h' ^ 4) := by
  rw [row_map i v (F := fun w => ENNReal.ofReal (XR P h h' w ^ 4))
    (ENNReal.measurable_ofReal.comp ((XR_meas hh hh').pow_const 4))]
  exact lemmaR_iii_four hh hh' hT hv

end iii

end BstLean.Part151
