import BstLean.Part151Poinc
import BstLean.Part53Polar
import BstLean.Part161Lat

/-!
# Part 162, item 1: Lemma LS for `p = 1` (moments on the latitude sphere)

Role: `delegations/statements/p162-spec.md`, item 1. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:LS` (`p = 1`).

Route (different from the paper's cutoff of the singular lift `φ(su + √(1−s²)H/|H|)`): apply the
Gaussian Poincaré inequality of Part 151 (`poincare_lip`) to the Lipschitz function
`H(v) = H₁(v) − m|v|`, where `H₁` is the positively 1-homogeneous extension and `m = E H₁(v/|v|)`.
Radius and direction are independent (`polar_map`, from Part 53's `gauss_polar_gen`), so
`E H = 0`, `E H² = k·Var G`; Euler's identity gives `|∇H|² = |∇H₁|² − 2mG + m²`.

* `polar_map`, `polar_integral_mul`: radius and direction of a standard Gaussian vector are
  independent.
* `euler`: `DH₁(v) v = H₁(v)` for a positively 1-homogeneous `H₁`.
* **`ls_var`**: `(k − 1)·Var G ≤ E[|∇H₁|² − G²]`, `G = H₁(Z/|Z|)`, `Z` standard Gaussian in `ℝ^k`.
* `xLatH`: the 1-homogeneous extension `|v|·xLat c s (v/|v|)` of the latitude parametrization.
* **`ls_lat`**: on the latitude sphere at `s`, for a Lipschitz positively 1-homogeneous `Φ` on
  `ℝⁿ`: `(n − 2)·Var(Φ(x) | s) ≤ E[|∇(Φ ∘ xLatH c s)|² − Φ(x)²]`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF gauss_polar_gen)
open BstLean.Part148 (EuLip)

variable {ι : Type} [Fintype ι]

/-- **Radius and direction of a standard Gaussian vector are independent** (measure form). -/
theorem polar_map :
    (stdGauss ι).map (fun Z => (unitF53 Z, radF53 Z)) =
      ((stdGauss ι).map unitF53).prod ((stdGauss ι).map radF53) := by
  ext s hs
  rw [Measure.map_apply (measurable_unitF.prodMk measurable_radF) hs, Measure.prod_apply hs,
    lintegral_map (measurable_measure_prodMk_left hs) measurable_unitF]
  have hF : Measurable (Function.uncurry fun (v : ι → ℝ) (r : ℝ) => s.indicator (1 : (ι → ℝ) × ℝ → ℝ≥0∞) (v, r)) := by
    have : (Function.uncurry fun (v : ι → ℝ) (r : ℝ) => s.indicator (1 : (ι → ℝ) × ℝ → ℝ≥0∞) (v, r)) =
        s.indicator 1 := by funext p; rfl
    rw [this]; exact measurable_one.indicator hs
  have h := gauss_polar_gen (fun v r => s.indicator (1 : (ι → ℝ) × ℝ → ℝ≥0∞) (v, r)) hF
  have e1 : (stdGauss ι) ((fun Z => (unitF53 Z, radF53 Z)) ⁻¹' s) =
      ∫⁻ Z, s.indicator (1 : (ι → ℝ) × ℝ → ℝ≥0∞) (unitF53 Z, radF53 Z) ∂stdGauss ι := by
    rw [← lintegral_indicator_one ((measurable_unitF.prodMk measurable_radF) hs)]
    rfl
  rw [e1, h]
  refine lintegral_congr fun Z => ?_
  rw [Measure.map_apply measurable_radF (measurable_prodMk_left hs),
    ← lintegral_indicator_one (measurable_radF (measurable_prodMk_left hs))]
  rfl

/-- The product formula `E[f(Z/|Z|) g(|Z|)] = E f(Z/|Z|) · E g(|Z|)`. -/
theorem polar_integral_mul (f : (ι → ℝ) → ℝ) (g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    ∫ Z, f (unitF53 Z) * g (radF53 Z) ∂stdGauss ι =
      (∫ Z, f (unitF53 Z) ∂stdGauss ι) * ∫ Z, g (radF53 Z) ∂stdGauss ι := by
  have m := measurable_unitF.prodMk (measurable_radF (ι := ι))
  have h1 : ∫ Z, f (unitF53 Z) * g (radF53 Z) ∂stdGauss ι =
      ∫ p, f p.1 * g p.2 ∂(stdGauss ι).map (fun Z => (unitF53 Z, radF53 Z)) := by
    rw [integral_map m.aemeasurable (f := fun p : (ι → ℝ) × ℝ => f p.1 * g p.2)
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable]
  rw [h1, polar_map, integral_prod_mul, integral_map measurable_unitF.aemeasurable
    hf.aestronglyMeasurable, integral_map measurable_radF.aemeasurable hg.aestronglyMeasurable]


/-! ## The 1-homogeneous lift -/

lemma radF_sq (v : ι → ℝ) : radF53 v ^ 2 = ∑ i, v i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma radF_nonneg (v : ι → ℝ) : 0 ≤ radF53 v := Real.sqrt_nonneg _

lemma radF_pos {v : ι → ℝ} (hv : v ≠ 0) : 0 < radF53 v := by
  unfold radF53
  apply Real.sqrt_pos.mpr
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => v i ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

lemma radF_eq_norm (v : ι → ℝ) : radF53 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold radF53
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

lemma radF_lip (x y : ι → ℝ) : |radF53 x - radF53 y| ≤ √(∑ i, (x i - y i) ^ 2) := by
  rw [radF_eq_norm, radF_eq_norm]
  have h := abs_norm_sub_norm_le (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y)
  refine h.trans (le_of_eq ?_)
  rw [← WithLp.toLp_sub, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

lemma unitF_smul (v : ι → ℝ) : radF53 v • unitF53 v = v := by
  by_cases hv : v = 0
  · subst hv; simp [unitF53]
  · have h := (radF_pos hv).ne'
    unfold radF53 at h ⊢
    unfold unitF53
    rw [smul_smul, one_div, mul_inv_cancel₀ h, one_smul]

lemma radF_unitF_le (v : ι → ℝ) : radF53 (unitF53 v) ≤ 1 := by
  by_cases hv : v = 0
  · subst hv; simp [unitF53, radF53]
  · have h : radF53 (unitF53 v) = 1 := by
      have e : unitF53 v = (radF53 v)⁻¹ • v := by unfold unitF53; rw [one_div]; rfl
      rw [e, radF_eq_norm, WithLp.toLp_smul, norm_smul, ← radF_eq_norm, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (radF_pos hv)), inv_mul_cancel₀ (radF_pos hv).ne']
    exact h.le

variable {H₁ : (ι → ℝ) → ℝ} {L : ℝ}

lemma hom_zero (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) : H₁ 0 = 0 := by
  have h := hhom 2 0 two_pos
  rw [smul_zero] at h
  linarith

lemma hom_rad (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) (v : ι → ℝ) :
    H₁ v = radF53 v * H₁ (unitF53 v) := by
  by_cases hv : v = 0
  · subst hv; rw [hom_zero hhom]; simp [radF53]
  · conv_lhs => rw [← unitF_smul v]
    exact hhom _ _ (radF_pos hv)

lemma hom_unit_bound (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) (v : ι → ℝ) :
    |H₁ (unitF53 v)| ≤ L := by
  have h := hL (unitF53 v) 0
  rw [hom_zero hhom, sub_zero] at h
  refine h.trans ?_
  have : √(∑ i, (unitF53 v i - (0 : ι → ℝ) i) ^ 2) = radF53 (unitF53 v) := by
    simp [radF53]
  rw [this]
  calc L * radF53 (unitF53 v) ≤ L * 1 := mul_le_mul_of_nonneg_left (radF_unitF_le v) hL0
    _ = L := mul_one L

/-- **Euler's identity** for a positively 1-homogeneous function at a point of
differentiability: `DH₁(v) v = H₁(v)`. -/
lemma euler (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {v : ι → ℝ}
    (hd : DifferentiableAt ℝ H₁ v) : fderiv ℝ H₁ v v = H₁ v := by
  have h1 : HasDerivAt (fun t : ℝ => H₁ (t • v)) (fderiv ℝ H₁ v v) 1 := by
    have hf : HasFDerivAt H₁ (fderiv ℝ H₁ v) ((1 : ℝ) • v) := by rw [one_smul]; exact hd.hasFDerivAt
    have := hf.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const v)
    rw [one_smul] at this
    exact this
  have h2 : HasDerivAt (fun t : ℝ => t * H₁ v) (H₁ v) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (H₁ v)
  have h3 : (fun t : ℝ => H₁ (t • v)) =ᶠ[𝓝 1] (fun t : ℝ => t * H₁ v) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 from one_pos)] with t ht
    exact hhom t v ht
  exact h1.unique (h2.congr_of_eventuallyEq h3)

/-- The derivative of the radius at `v ≠ 0`. -/
lemma hasFDerivAt_radF {v : ι → ℝ} (hv : v ≠ 0) :
    HasFDerivAt (radF53 (ι := ι)) ((1 / (2 * radF53 v)) •
      ∑ i, (2 * v i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) v := by
  have hs : HasFDerivAt (fun w : ι → ℝ => ∑ i, w i ^ 2)
      (∑ i, (2 * v i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) v := by
    have : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun w : ι → ℝ => w i ^ 2)
        ((2 * v i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) v := by
      intro i _
      have h0 : HasFDerivAt (fun w : ι → ℝ => w i) (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) v :=
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
      have := h0.pow 2
      convert this using 1
      ext w
      simp [mul_comm]
    have h := HasFDerivAt.sum this
    convert h using 1
    funext w; simp
  have hne : (∑ i, v i ^ 2) ≠ 0 := by rw [← radF_sq]; exact (pow_pos (radF_pos hv) 2).ne'
  exact hs.sqrt hne

lemma fderiv_radF_single [DecidableEq ι] {v : ι → ℝ} (hv : v ≠ 0) (i : ι) :
    fderiv ℝ (radF53 (ι := ι)) v (Pi.single i 1) = v i / radF53 v := by
  rw [(hasFDerivAt_radF hv).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := (radF_pos hv).ne'
  field_simp


lemma clm_apply_sum [DecidableEq ι] (f : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    f v = ∑ i, v i * f (Pi.single i 1) := by
  conv_lhs => rw [show v = ∑ i, v i • Pi.single i (1 : ℝ) from by
    ext j; simp [Pi.single_apply]]
  simp [map_sum, map_smul]

open BstLean.Part151 (gradSq gradSq_integrable gradSq_nonneg gradSq_le poincare_lip) in
/-- The squared gradient of `H₁ − m·|v|` at `v ≠ 0`, where `H₁` is differentiable. -/
lemma gradSq_sub_rad [DecidableEq ι]
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) (m : ℝ) {v : ι → ℝ}
    (hv : v ≠ 0) (hd : DifferentiableAt ℝ H₁ v) :
    gradSq (fun w => H₁ w - m * radF53 w) v = gradSq H₁ v - 2 * m * H₁ (unitF53 v) + m ^ 2 := by
  have hr := (hasFDerivAt_radF hv).differentiableAt
  have hD : fderiv ℝ (fun w => H₁ w - m * radF53 w) v = fderiv ℝ H₁ v - m • fderiv ℝ radF53 v := by
    have := hd.hasFDerivAt.sub (hr.hasFDerivAt.const_mul m)
    exact this.fderiv
  have rp := radF_pos hv
  have he : ∑ i, fderiv ℝ H₁ v (Pi.single i 1) * v i = radF53 v * H₁ (unitF53 v) := by
    rw [← hom_rad hhom v, ← euler hhom hd, clm_apply_sum (fderiv ℝ H₁ v) v]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hs : ∑ i, v i ^ 2 = radF53 v ^ 2 := (radF_sq v).symm
  unfold gradSq
  rw [hD]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_radF_single hv]
  set r := radF53 v
  have e1 : ∑ i, (fderiv ℝ H₁ v (Pi.single i 1) - m * (v i / r)) ^ 2 =
      ∑ i, (fderiv ℝ H₁ v (Pi.single i 1)) ^ 2 - 2 * m / r * ∑ i, fderiv ℝ H₁ v (Pi.single i 1) * v i +
        m ^ 2 / r ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  rw [e1, he, hs]
  field_simp

open BstLean.Part151 (gradSq gradSq_integrable gradSq_nonneg gradSq_le poincare_lip) in
/-- **Lemma LS for `p = 1` (sharp spherical Poincaré inequality via the Gaussian lift).**
Let `H₁` be Lipschitz (constant `L`) and positively 1-homogeneous on `ℝ^k`, `k ≥ 1`, and let
`G = H₁(Z/|Z|)` (the restriction of `H₁` to the unit sphere, evaluated at a uniform direction).
THEN `(k − 1)·Var G ≤ E[|∇H₁(Z)|² − G(Z)²]`, `Z` standard Gaussian. The integrand on the right is
the squared tangential gradient: at a point of differentiability, `G = ⟨∇H₁, Z/|Z|⟩` (Euler). -/
theorem ls_var [DecidableEq ι] [Nonempty ι] (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) :
    ((Fintype.card ι : ℝ) - 1) *
        ∫ v, (H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      ∫ v, (gradSq H₁ v - H₁ (unitF53 v) ^ 2) ∂stdGauss ι := by
  set γ := stdGauss ι
  have hc := hL.continuous hL0
  set G : (ι → ℝ) → ℝ := fun v => H₁ (unitF53 v) with hGd
  have mG : Measurable G := hc.measurable.comp measurable_unitF
  have bG : ∀ v, |G v| ≤ L := hom_unit_bound hL0 hL hhom
  have iG : Integrable G γ := Integrable.of_bound mG.aestronglyMeasurable L
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact bG v)
  have bG2 : ∀ v, |G v ^ 2| ≤ L ^ 2 := fun v => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have := bG v
    nlinarith [abs_nonneg (G v), sq_abs (G v)]
  have iG2 : Integrable (fun v => G v ^ 2) γ := Integrable.of_bound (mG.pow_const 2).aestronglyMeasurable
    (L ^ 2) (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact bG2 v)
  set m := ∫ v, G v ∂γ with hm
  set H : (ι → ℝ) → ℝ := fun w => H₁ w - m * radF53 w with hHd
  have hHL : EuLip H (L + |m|) := by
    intro x y
    have h1 := hL x y
    have h2 := radF_lip x y
    have e : H x - H y = (H₁ x - H₁ y) - m * (radF53 x - radF53 y) := by simp only [hHd]; ring
    rw [e]
    calc |(H₁ x - H₁ y) - m * (radF53 x - radF53 y)| ≤ |H₁ x - H₁ y| + |m * (radF53 x - radF53 y)| :=
          abs_sub _ _
      _ = |H₁ x - H₁ y| + |m| * |radF53 x - radF53 y| := by rw [abs_mul]
      _ ≤ L * √(∑ i, (x i - y i) ^ 2) + |m| * √(∑ i, (x i - y i) ^ 2) := by
          gcongr
      _ = (L + |m|) * √(∑ i, (x i - y i) ^ 2) := by ring
  have hHeq : ∀ v, H v = (H₁ (unitF53 v) - m) * radF53 v := fun v => by
    simp only [hHd]; rw [hom_rad hhom v]; ring
  have hP := poincare_lip (add_nonneg hL0 (abs_nonneg m)) hHL
  -- the mean of `H` is zero
  have hH0 : ∫ v, H v ∂γ = 0 := by
    simp_rw [hHeq]
    rw [polar_integral_mul (fun u => H₁ u - m) (fun r => r) (hc.measurable.sub_const m) measurable_id]
    have : ∫ Z, (H₁ (unitF53 Z) - m) ∂γ = 0 := by
      rw [integral_sub iG (integrable_const m)]
      simp [hm, G]
    rw [this, zero_mul]
  -- the second moment of `H`
  have hrad2 : ∫ Z, radF53 Z ^ 2 ∂γ = Fintype.card ι := by
    simp_rw [radF_sq]
    rw [integral_finset_sum _ fun i _ => by
      simpa [sq] using BstLean.Part107.gauss_pair_integrable107 (ι := ι) i i]
    have : ∀ i : ι, ∫ Z, Z i ^ 2 ∂γ = 1 := fun i => by
      have := BstLean.Part107.gauss_pair107 (ι := ι) i i
      simpa [sq] using this
    simp [this]
  have hH2 : ∫ v, H v ^ 2 ∂γ = (Fintype.card ι : ℝ) * ∫ v, (G v - m) ^ 2 ∂γ := by
    have e : ∀ v, H v ^ 2 = (H₁ (unitF53 v) - m) ^ 2 * radF53 v ^ 2 := fun v => by
      rw [hHeq]; ring
    simp_rw [e]
    rw [polar_integral_mul (fun u => (H₁ u - m) ^ 2) (fun r => r ^ 2)
      ((hc.measurable.sub_const m).pow_const 2) (measurable_id.pow_const 2), hrad2, mul_comm]
  -- the gradient
  have hnz : ∀ᵐ v ∂γ, v ≠ 0 := by
    have h0 : γ {(0 : ι → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (0 : ι → ℝ))
    rw [ae_iff]
    simpa using h0
  have hgr : ∀ᵐ v ∂γ, ∑ i, (fderiv ℝ H v (Pi.single i 1)) ^ 2 =
      gradSq H₁ v - 2 * m * G v + m ^ 2 := by
    filter_upwards [hnz, hL.ae_diff hL0] with v hv hd
    exact gradSq_sub_rad hhom m hv hd
  have iI := gradSq_integrable hL0 hL (f := H₁)
  have hgrI : ∫ v, ∑ i, (fderiv ℝ H v (Pi.single i 1)) ^ 2 ∂γ =
      ∫ v, gradSq H₁ v ∂γ - m ^ 2 := by
    rw [integral_congr_ae hgr, integral_add (f := fun v => gradSq H₁ v - 2 * m * G v)
      (g := fun _ => m ^ 2) (iI.sub (iG.const_mul (2 * m))) (integrable_const _),
      integral_sub (f := fun v => gradSq H₁ v) (g := fun v => 2 * m * G v) iI (iG.const_mul (2 * m)),
      integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
    rw [← hm]; ring
  rw [hH0] at hP
  simp only [sub_zero] at hP
  rw [hH2, hgrI] at hP
  have hV : ∫ v, (G v - m) ^ 2 ∂γ = ∫ v, G v ^ 2 ∂γ - m ^ 2 := by
    have e : ∀ v, (G v - m) ^ 2 = G v ^ 2 - 2 * m * G v + m ^ 2 := fun v => by ring
    simp_rw [e]
    rw [integral_add (f := fun v => G v ^ 2 - 2 * m * G v) (g := fun _ => m ^ 2)
      (iG2.sub (iG.const_mul (2 * m))) (integrable_const _),
      integral_sub (f := fun v => G v ^ 2) (g := fun v => 2 * m * G v) iG2 (iG.const_mul (2 * m)),
      integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, smul_eq_mul]
    rw [← hm]; ring
  rw [integral_sub iI iG2]
  change ((Fintype.card ι : ℝ) - 1) * ∫ v, (G v - m) ^ 2 ∂γ ≤ _
  rw [sub_mul, one_mul]
  have := hV
  linarith


/-! ## The latitude form -/

lemma radF_unitF {v : ι → ℝ} (hv : v ≠ 0) : radF53 (unitF53 v) = 1 := by
  have e : unitF53 v = (radF53 v)⁻¹ • v := by unfold unitF53; rw [one_div]; rfl
  rw [e, radF_eq_norm, WithLp.toLp_smul, norm_smul, ← radF_eq_norm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (radF_pos hv)), inv_mul_cancel₀ (radF_pos hv).ne']

lemma unitF_unitF {v : ι → ℝ} (hv : v ≠ 0) : unitF53 (unitF53 v) = unitF53 v := by
  have e : ∀ w : ι → ℝ, unitF53 w = (1 / radF53 w) • w := fun w => rfl
  rw [e (unitF53 v), radF_unitF hv, div_one, one_smul]

lemma radF_smul {t : ℝ} (ht : 0 < t) (v : ι → ℝ) : radF53 (t • v) = t * radF53 v := by
  rw [radF_eq_norm, radF_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]

open BstLean.Part161 (xLat hhMat uHat consV hh_normSq normSq_consV consV_smul consV_add hh_smul)
open BstLean.Part130 (normSq)
open BstLean.Part157 (Ret)

variable {n : ℕ}

/-- The 1-homogeneous extension of the latitude parametrization:
`xLatH c s v = |v|·xLat c s (v/|v|) = H(s|v|, √(1 − s²) v)`. -/
noncomputable def xLatH (c : Ret n) (s : ℝ) (v : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  (hhMat (uHat c)).mulVec (consV (s * radF53 v) (√(1 - s ^ 2) • v))

lemma xLatH_eq (c : Ret n) (s : ℝ) (v : Fin (n - 1) → ℝ) :
    xLatH c s v = radF53 v • xLat c s (unitF53 v) := by
  unfold xLatH xLat
  rw [← hh_smul, ← consV_smul, smul_comm, unitF_smul, mul_comm]

lemma xLatH_smul (c : Ret n) (s : ℝ) {t : ℝ} (ht : 0 < t) (v : Fin (n - 1) → ℝ) :
    xLatH c s (t • v) = t • xLatH c s v := by
  unfold xLatH
  rw [← hh_smul, ← consV_smul, radF_smul ht, smul_comm t]
  congr 2
  ring

lemma consV_sub (z z' : ℝ) (g g' : Fin (n - 1) → ℝ) :
    consV z g - consV z' g' = consV (n := n) (z - z') (g - g') := by
  funext i
  unfold consV
  by_cases h : (i : ℕ) = 0 <;> simp [h]

lemma xLatH_dist (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) (v w : Fin (n - 1) → ℝ) :
    ∑ i, (xLatH c s v i - xLatH c s w i) ^ 2 ≤ ∑ i, (v i - w i) ^ 2 := by
  have e : (fun i => xLatH c s v i - xLatH c s w i) =
      (hhMat (uHat c)).mulVec (consV (s * (radF53 v - radF53 w)) (√(1 - s ^ 2) • (v - w))) := by
    funext i
    unfold xLatH
    rw [← Pi.sub_apply, ← Matrix.mulVec_sub, consV_sub, smul_sub, mul_sub]
  have h1 : ∑ i, (xLatH c s v i - xLatH c s w i) ^ 2 =
      normSq (fun i => xLatH c s v i - xLatH c s w i) := rfl
  rw [h1, e, hh_normSq, normSq_consV hn]
  have h2 : normSq (√(1 - s ^ 2) • (v - w)) = (1 - s ^ 2) * ∑ i, (v i - w i) ^ 2 := by
    unfold normSq
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow]
    rw [Real.sq_sqrt (by linarith), Finset.mul_sum]
  rw [h2]
  have h3 := radF_lip v w
  have h4 : (radF53 v - radF53 w) ^ 2 ≤ ∑ i, (v i - w i) ^ 2 := by
    have h5 : |radF53 v - radF53 w| ^ 2 ≤ (√(∑ i, (v i - w i) ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h3 2
    rwa [sq_abs, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h5
  have h6 : 0 ≤ s ^ 2 := sq_nonneg s
  calc (s * (radF53 v - radF53 w)) ^ 2 + (1 - s ^ 2) * ∑ i, (v i - w i) ^ 2
      = s ^ 2 * (radF53 v - radF53 w) ^ 2 + (1 - s ^ 2) * ∑ i, (v i - w i) ^ 2 := by ring
    _ ≤ s ^ 2 * ∑ i, (v i - w i) ^ 2 + (1 - s ^ 2) * ∑ i, (v i - w i) ^ 2 := by gcongr
    _ = ∑ i, (v i - w i) ^ 2 := by ring

open BstLean.Part151 (gradSq) in
/-- **Lemma LS (`p = 1`) on a latitude sphere.** Fix the retained data `c`, a latitude `s` with
`s² ≤ 1`, and a function `Φ` on `ℝⁿ` that is Lipschitz (constant `L`) and positively
1-homogeneous (as `λ(x)` and `σ(x)` are). Let `V` be uniform on the unit sphere of `ℝ^{n−1}`
(here `V = G/|G|`, `G` standard Gaussian), so that `x = xLat c s V` has the conditional
distribution of the input given the latitude `s` (`nuStand_latitude`). THEN
`(n − 2)·Var(Φ(x) | s) ≤ E[|∇H₁(G)|² − Φ(x)²]`, `H₁ = Φ ∘ xLatH c s` (the 1-homogeneous lift);
the integrand is the squared tangential gradient, `(1 − s²)|P_lat ∇Φ(x)|²` where `Φ` is
differentiable at `x`. The paper has the constant `1/(n − 3)`; this is `1/(n − 2)`. -/
theorem ls_lat (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {Φ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : EuLip Φ L) (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) :
    ((n : ℝ) - 2) * ∫ v, (Φ (xLat c s (unitF53 v)) -
        ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 ∂stdGauss (Fin (n - 1)) ≤
      ∫ v, (gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLat c s (unitF53 v)) ^ 2)
        ∂stdGauss (Fin (n - 1)) := by
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  set H₁ : (Fin (n - 1) → ℝ) → ℝ := fun w => Φ (xLatH c s w) with hH₁
  have hHL : EuLip H₁ L := by
    intro v w
    refine (hL _ _).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hL0)
    exact xLatH_dist (by omega) c hs v w
  have hHh : ∀ (t : ℝ) (v : Fin (n - 1) → ℝ), 0 < t → H₁ (t • v) = t * H₁ v := fun t v ht => by
    simp only [hH₁]; rw [xLatH_smul c s ht, hhom _ _ ht]
  have h := ls_var hL0 hHL hHh
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (0 : Fin (n - 1) → ℝ))
    rw [ae_iff]
    simpa using h0
  have hG : ∀ᵐ v ∂stdGauss (Fin (n - 1)), H₁ (unitF53 v) = Φ (xLat c s (unitF53 v)) := by
    filter_upwards [hnz] with v hv
    simp only [hH₁]
    rw [xLatH_eq, radF_unitF hv, unitF_unitF hv, one_smul]
  have hm : ∫ w, H₁ (unitF53 w) ∂stdGauss (Fin (n - 1)) =
      ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1)) := integral_congr_ae hG
  have e1 : ∫ v, (H₁ (unitF53 v) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1)) = ∫ v, (Φ (xLat c s (unitF53 v)) -
        ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 ∂stdGauss (Fin (n - 1)) :=
    integral_congr_ae (hG.mono fun v hv => by beta_reduce; rw [hv])
  have e2 : ∫ v, (gradSq H₁ v - H₁ (unitF53 v) ^ 2) ∂stdGauss (Fin (n - 1)) =
      ∫ v, (gradSq H₁ v - Φ (xLat c s (unitF53 v)) ^ 2) ∂stdGauss (Fin (n - 1)) :=
    integral_congr_ae (hG.mono fun v hv => by beta_reduce; rw [hv])
  rw [hm, e1, e2] at h
  have hc : ((Fintype.card (Fin (n - 1)) : ℕ) : ℝ) - 1 = (n : ℝ) - 2 := by
    rw [Fintype.card_fin, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc] at h
  exact h

end BstLean.Part162

open BstLean.Part162 in
#print axioms ls_var
open BstLean.Part162 in
#print axioms ls_lat
