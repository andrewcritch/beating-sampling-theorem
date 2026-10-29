import BstLean.Part158Approx1

/-!
# Part 158 (file `Approx2`): from differentiable `f` to measurable `f`

Do not use `sorry`, `native_decide` or `axiom`.

* `gp_meas_of_smooth`: if the inequality (GP) holds for functions with a bounded gradient
  (`GPSmoothStmt`), then it holds for every measurable `f` with `0 < a ≤ f ≤ b`, for a finite
  measure `μ` on `ℝ^N` and unit vectors `e(x)`. Proof: `log f = K·arctan(mm)` with `mm` bounded;
  `mm` is a limit in `L¹(μ ⊗ γ)` of smooth functions `g` with compact support; apply the
  inequality to `exp(K·arctan g)` and use `gp_compare`.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ContDiff
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134

lemma abs_arctan_sub_le (x y : ℝ) : |arctan x - arctan y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := arctan) (s := Set.univ) (C := 1)
    (fun x _ => (Real.hasDerivAt_arctan x).differentiableAt)
    (fun x _ => by
      rw [(Real.hasDerivAt_arctan x).deriv, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg x])
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

lemma abs_tan_le {t : ℝ} (ht : |t| ≤ 1) : |tan t| ≤ tan 1 := by
  have hpi : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have m1 : (1 : ℝ) ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, hpi⟩
  have mt : t ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have mn : (-1 : ℝ) ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  rw [abs_le]
  constructor
  · rw [← Real.tan_neg]
    exact Real.strictMonoOn_tan.monotoneOn mn mt h1
  · exact Real.strictMonoOn_tan.monotoneOn mt m1 h2

/-- **(GP) for measurable `f` from (GP) for differentiable `f`**, finite measure on `ℝ^N`, unit
vectors `e(x)`. -/
theorem gp_meas_of_smooth (h : GPSmoothStmt) {N q m : ℕ} (μ : Measure (Fin N → ℝ))
    [IsFiniteMeasure μ] (e : (Fin N → ℝ) → Fin m → ℝ) (he : Measurable e)
    (hunit : ∀ x, normSq (e x) = 1) (f : (Fin N → ℝ) × (Fin q → ℝ) → ℝ) (hf : Measurable f)
    {a b : ℝ} (ha : 0 < a) (hfa : ∀ y, a ≤ f y) (hfb : ∀ y, f y ≤ b) {L : ℝ} (hL : 0 < L)
    (hframe : ∀ w : Fin m → ℝ, ∫ x, (∑ j, e x j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫ G, exp (1 / L * ∫ x, log (f (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 ≤
      exp (1 / L * ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ) := by
  have hpi : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  set K := |log a| + |log b| + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith [abs_nonneg (log a), abs_nonneg (log b)]
  have hK0 : 0 < K := by linarith
  have fpos : ∀ y, 0 < f y := fun y => lt_of_lt_of_le ha (hfa y)
  have hℓ : ∀ y, |log (f y)| ≤ K - 1 := by
    intro y
    have g1 := Real.log_le_log ha (hfa y)
    have g2 := Real.log_le_log (fpos y) (hfb y)
    rw [abs_le, hK]
    constructor
    · linarith [neg_abs_le (log a), abs_nonneg (log b)]
    · linarith [le_abs_self (log b), abs_nonneg (log a)]
  have ht : ∀ y, |log (f y) / K| ≤ 1 := by
    intro y
    rw [abs_div, abs_of_pos hK0, div_le_one hK0]
    linarith [hℓ y]
  set mm : (Fin N → ℝ) × (Fin q → ℝ) → ℝ := fun y => tan (log (f y) / K) with hmm
  have mmm : Measurable mm := by
    have : mm = fun y => sin (log (f y) / K) / cos (log (f y) / K) := by
      funext y; simp only [hmm, Real.tan_eq_sin_div_cos]
    rw [this]
    exact ((hf.log.div_const K).sin).div ((hf.log.div_const K).cos)
  have mmb : ∀ y, |mm y| ≤ tan 1 := fun y => abs_tan_le (ht y)
  have harc : ∀ y, K * arctan (mm y) = log (f y) := by
    intro y
    obtain ⟨h1, h2⟩ := abs_le.mp (ht y)
    simp only [hmm]
    rw [Real.arctan_tan (by linarith) (by linarith)]
    field_simp
  have hmem : MemLp mm 1 (μ.prod (stdGauss (Fin q))) :=
    MemLp.of_bound mmm.aestronglyMeasurable (tan 1)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact mmb y)
  set B := K * (π / 2) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  have hKB : K ≤ B := by rw [hB]; nlinarith
  have step : ∀ ε : ℝ, 0 < ε →
      ∫ G, exp (1 / L * ∫ x, log (f (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 ≤
        exp (1 / L * ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ) *
          exp (1 / L * (exp B / exp (-B)) * (K * ε)) +
        exp (1 / L * (B * μ.real Set.univ)) * (1 / L) * (K * ε) := by
    intro ε hε
    obtain ⟨g, hgc, hgs, hgn⟩ := hmem.exist_eLpNorm_sub_le (by simp) le_rfl hε
    have gcont : Continuous g := hgs.continuous
    have iint : Integrable (mm - g) (μ.prod (stdGauss (Fin q))) :=
      memLp_one_iff_integrable.mp (hmem.sub (gcont.memLp_of_hasCompactSupport hgc))
    have hint : ∫ y, |g y - mm y| ∂(μ.prod (stdGauss (Fin q))) ≤ ε := by
      have e1 : ∫ y, |g y - mm y| ∂(μ.prod (stdGauss (Fin q))) =
          ∫ y, ‖(mm - g) y‖ ∂(μ.prod (stdGauss (Fin q))) :=
        integral_congr_ae (Eventually.of_forall fun y => by
          simp only [Pi.sub_apply, Real.norm_eq_abs]; rw [abs_sub_comm])
      rw [e1, integral_norm_eq_lintegral_enorm iint.aestronglyMeasurable,
        ← eLpNorm_one_eq_lintegral_enorm iint.aestronglyMeasurable]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgn
      rwa [ENNReal.toReal_ofReal hε.le] at this
    set fg : (Fin N → ℝ) × (Fin q → ℝ) → ℝ := fun y => exp (K * arctan (g y)) with hfg
    have mfg : Measurable fg := (gcont.measurable.arctan.const_mul K).exp
    have arcB : ∀ y, |K * arctan (g y)| ≤ B := by
      intro y
      have h1 := Real.arctan_lt_pi_div_two (g y)
      have h2 := Real.neg_pi_div_two_lt_arctan (g y)
      rw [abs_le, hB]
      constructor <;> nlinarith
    have lfg : ∀ y, log (fg y) = K * arctan (g y) := fun y => Real.log_exp _
    have lo : ∀ y, exp (-B) ≤ fg y := fun y =>
      exp_le_exp.mpr (abs_le.mp (arcB y)).1
    have hi : ∀ y, fg y ≤ exp B := fun y => exp_le_exp.mpr (abs_le.mp (arcB y)).2
    have Bfg : ∀ y, |log (fg y)| ≤ B := fun y => by rw [lfg]; exact arcB y
    have Bf : ∀ y, |log (f y)| ≤ B := fun y => by linarith [hℓ y]
    have flo : ∀ y, exp (-B) ≤ f y := fun y => by
      rw [← Real.exp_log (fpos y)]; exact exp_le_exp.mpr (abs_le.mp (Bf y)).1
    have fhi : ∀ y, f y ≤ exp B := fun y => by
      rw [← Real.exp_log (fpos y)]; exact exp_le_exp.mpr (abs_le.mp (Bf y)).2
    have hδ : ∫ y, |log (fg y) - log (f y)| ∂(μ.prod (stdGauss (Fin q))) ≤ K * ε := by
      have i2 : Integrable (fun y => K * |g y - mm y|) (μ.prod (stdGauss (Fin q))) := by
        refine (iint.norm.const_mul K).congr (Eventually.of_forall fun y => ?_)
        simp only [Pi.sub_apply, Real.norm_eq_abs]; rw [abs_sub_comm]
      have i1 : Integrable (fun y => |log (fg y) - log (f y)|) (μ.prod (stdGauss (Fin q))) :=
        integrable_of_bdd (B := 2 * B) (mfg.log.sub hf.log).abs fun y => by
          rw [abs_abs]
          have := abs_sub (log (fg y)) (log (f y))
          linarith [Bfg y, Bf y]
      have := integral_mono i1 i2 fun y => by
        change |log (fg y) - log (f y)| ≤ K * |g y - mm y|
        rw [lfg, ← harc y, ← mul_sub, abs_mul, abs_of_pos hK0]
        exact mul_le_mul_of_nonneg_left (abs_arctan_sub_le _ _) hK0.le
      rw [integral_const_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left hint hK0.le)
    -- the smooth data
    have cfg : ContDiff ℝ ∞ fg :=
      Real.contDiff_exp.comp (contDiff_const.mul (Real.contDiff_arctan.comp hgs))
    have dfg : Differentiable ℝ fg := cfg.differentiable (by simp)
    have cD : Continuous (fderiv ℝ fg) := cfg.continuous_fderiv (by simp)
    have sD : HasCompactSupport (fderiv ℝ fg) := by
      have h1 : HasCompactSupport (fun y => fg y - 1) := by
        refine hgc.mono ?_
        intro y hy
        simp only [Function.mem_support, ne_eq] at hy ⊢
        intro h0
        apply hy
        simp [hfg, h0]
      have h2 := h1.fderiv (𝕜 := ℝ)
      have e2 : fderiv ℝ (fun y => fg y - 1) = fderiv ℝ fg := by
        funext y; rw [fderiv_sub_const]
      rwa [e2] at h2
    obtain ⟨C, hC⟩ := cD.bounded_above_of_compact_support sD
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    set vv : Fin q → (Fin N → ℝ) × (Fin q → ℝ) :=
      fun i => ((0 : Fin N → ℝ), fun j => if i = j then (1 : ℝ) else 0) with hvv
    set f' : (Fin N → ℝ) × (Fin q → ℝ) → Fin q → ℝ := fun y i => fderiv ℝ fg y (vv i) with hf'
    have mf' : Measurable f' :=
      measurable_pi_iff.mpr fun i => (cD.clm_apply continuous_const).measurable
    have hC' : ∀ y i, |f' y i| ≤ C * ∑ i, ‖vv i‖ := by
      intro y i
      have h1 : |f' y i| ≤ ‖fderiv ℝ fg y‖ * ‖vv i‖ := by
        rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      have h2 : ‖vv i‖ ≤ ∑ i, ‖vv i‖ :=
        Finset.single_le_sum (f := fun i => ‖vv i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
      calc |f' y i| ≤ ‖fderiv ℝ fg y‖ * ‖vv i‖ := h1
        _ ≤ C * ‖vv i‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
        _ ≤ C * ∑ i, ‖vv i‖ := mul_le_mul_of_nonneg_left h2 hC0
    have hd : ∀ x z, HasFDerivAt (fun z => fg (x, z)) (dotL (f' (x, z))) z := by
      intro x z
      have h1 : HasFDerivAt fg (fderiv ℝ fg (x, z)) (x, z) := (dfg (x, z)).hasFDerivAt
      have h2 : HasFDerivAt (fun z : Fin q → ℝ => (x, z))
          (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin q → ℝ)) z := hasFDerivAt_prodMk_right x z
      have h3 := h1.comp z h2
      have e3 : (fderiv ℝ fg (x, z)).comp (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin q → ℝ)) =
          dotL (f' (x, z)) := by
        ext v
        rw [dotL_apply]
        have := LinearMap.pi_apply_eq_sum_univ
          (((fderiv ℝ fg (x, z)).comp
            (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin q → ℝ))).toLinearMap) v
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inr_apply, smul_eq_mul] at this
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, this]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e3] at h3
      exact h3
    have key := h μ e he hunit fg mfg f' mf' hd (exp (-B)) (exp B) (C * ∑ i, ‖vv i‖)
      (exp_pos _) lo hi hC' L hL hframe
    exact gp_compare μ e he hunit fg f mfg hf (exp_pos _) (exp_le_exp.mpr (by linarith))
      lo hi flo fhi Bfg Bf hL hδ key
  set R := exp (1 / L * ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ) with hR
  have tend : Tendsto (fun ε : ℝ => R * exp (1 / L * (exp B / exp (-B)) * (K * ε)) +
      exp (1 / L * (B * μ.real Set.univ)) * (1 / L) * (K * ε)) (𝓝[>] 0) (𝓝 R) := by
    have hc : Continuous (fun ε : ℝ => R * exp (1 / L * (exp B / exp (-B)) * (K * ε)) +
      exp (1 / L * (B * μ.real Set.univ)) * (1 / L) * (K * ε)) := by fun_prop
    exact (hc.tendsto' 0 R (by simp)).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto tend (eventually_mem_nhdsWithin.mono fun ε hε => step ε hε)

end BstLean.Part158

open BstLean.Part158 in
#print axioms gp_meas_of_smooth
