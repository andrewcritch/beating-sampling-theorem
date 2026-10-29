import BstLean.Part148Tools
import BstLean.Part53Polar
import BstLean.Part131Block
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Convex.Integral

/-!
# Part 148 (file `GC`): the Gaussian concentration inequality for Lipschitz functions

Role: `delegations/statements/p148-spec.md`, a tool for item 1 (the paper route of round onW23c
needs Gaussian concentration; Mathlib does not have it). The proof is the argument of Maurey and
Pisier; the constant is `π²/8` in the place of the sharp `1/2`.

`f : (ι → ℝ) → ℝ` is Lipschitz for the EUCLIDEAN norm with constant `L`:
`|f x − f y| ≤ L·√(Σ_i (x_i − y_i)²)`. `γ = stdGauss ι`.

* `gaussConc_pair`: `E exp(λ(f(X) − f(Y))) ≤ exp(λ²(π²/8)L²)`, `X`, `Y` independent with
  distribution `γ`.
* `gaussConc_mgf`: `f` and `exp(λf)` are integrable, and
  `E exp(λ(f − E f)) ≤ exp(λ²(π²/8)L²)`.
* **`gaussConc_lower`**, **`gaussConc_upper`**: `Pr(f ≤ E f − t) ≤ exp(−2t²/(π²L²))` and
  `Pr(f ≥ E f + t) ≤ exp(−2t²/(π²L²))` for `t ≥ 0`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part148

open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal NNReal Topology
open BstLean.Part29 (stdGauss)

section GC

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Euclidean norm on `ι → ℝ`, written by hand. -/
noncomputable def en (x : ι → ℝ) : ℝ := √(∑ i, x i ^ 2)

omit [DecidableEq ι] in
lemma en_nonneg (x : ι → ℝ) : 0 ≤ en x := Real.sqrt_nonneg _

omit [DecidableEq ι] in
lemma en_smul (c : ℝ) (x : ι → ℝ) : en (c • x) = |c| * en x := by
  unfold en
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

omit [DecidableEq ι] in
lemma en_le_sup (x : ι → ℝ) : en x ≤ √(Fintype.card ι) * ‖x‖ := by
  unfold en
  have h : ∑ i, x i ^ 2 ≤ (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
    have : ∀ i ∈ (Finset.univ : Finset ι), x i ^ 2 ≤ ‖x‖ ^ 2 := by
      intro i _
      have h1 : |x i| ≤ ‖x‖ := by
        have := norm_le_pi_norm x i
        rwa [Real.norm_eq_abs] at this
      calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
        _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have := Finset.sum_le_sum this
    simpa using this
  calc √(∑ i, x i ^ 2) ≤ √((Fintype.card ι : ℝ) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = √(Fintype.card ι) * ‖x‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The Lipschitz hypothesis for the Euclidean norm. -/
def EuLip (f : (ι → ℝ) → ℝ) (L : ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ L * √(∑ i, (x i - y i) ^ 2)

variable {f : (ι → ℝ) → ℝ} {L : ℝ}

omit [DecidableEq ι] in
lemma EuLip.lipschitz (hL0 : 0 ≤ L) (hL : EuLip f L) :
    LipschitzWith (L * √(Fintype.card ι)).toNNReal f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  have h := hL x y
  have h2 := en_le_sup (x - y)
  unfold en at h2
  simp only [Pi.sub_apply] at h2
  calc |f x - f y| ≤ L * √(∑ i, (x i - y i) ^ 2) := h
    _ ≤ L * (√(Fintype.card ι) * ‖x - y‖) := mul_le_mul_of_nonneg_left h2 hL0
    _ = _ := by ring

omit [DecidableEq ι] in
lemma EuLip.continuous (hL0 : 0 ≤ L) (hL : EuLip f L) : Continuous f :=
  (hL.lipschitz hL0).continuous

omit [DecidableEq ι] in
lemma stdGauss_ac : stdGauss ι ≪ (volume : Measure (ι → ℝ)) := by
  rw [BstLean.Part53.stdGauss_density]
  exact withDensity_absolutelyContinuous _ _

omit [DecidableEq ι] in
/-- Rademacher: `f` is differentiable almost everywhere for the Gaussian measure. -/
lemma EuLip.ae_diff (hL0 : 0 ≤ L) (hL : EuLip f L) :
    ∀ᵐ u ∂stdGauss ι, DifferentiableAt ℝ f u :=
  stdGauss_ac ((hL.lipschitz hL0).ae_differentiableAt (μ := volume))

/-- The derivative as a dot product, and the bound of the gradient. -/
lemma EuLip.grad (hL0 : 0 ≤ L) (hL : EuLip f L) {u : ι → ℝ} (hu : DifferentiableAt ℝ f u) :
    ∃ g : ι → ℝ, (∀ w : ι → ℝ, fderiv ℝ f u w = w ⬝ᵥ g) ∧ g ⬝ᵥ g ≤ L ^ 2 := by
  set g : ι → ℝ := fun i => fderiv ℝ f u (Pi.single i 1) with hg
  have hlin : ∀ w : ι → ℝ, fderiv ℝ f u w = w ⬝ᵥ g := by
    intro w
    have h := (fderiv ℝ f u).toLinearMap.pi_apply_eq_sum_univ w
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
    rw [h]
    simp only [dotProduct, hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨g, hlin, ?_⟩
  -- the directional derivative along `g`
  have hd : HasDerivAt (fun t : ℝ => f (u + t • g)) (fderiv ℝ f u g) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => u + t • g) g 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add u
      simpa using this
    have h2 : HasFDerivAt f (fderiv ℝ f u) (u + (0 : ℝ) • g) := by
      simpa using hu.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have ht := hd.tendsto_slope_zero_right
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f (u + (0 + t) • g) - f (u + (0 : ℝ) • g)) ≤
      L * en g := by
    filter_upwards [self_mem_nhdsWithin] with t ht0
    have ht0' : (0 : ℝ) < t := ht0
    have h := hL (u + t • g) u
    have e : √(∑ i, ((u + t • g) i - u i) ^ 2) = t * en g := by
      have : (fun i => ((u + t • g) i - u i) ^ 2) = fun i => (t • g) i ^ 2 := by
        funext i; simp
      rw [this]
      have := en_smul t g
      unfold en at this ⊢
      rw [this, abs_of_pos ht0']
    rw [e] at h
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have h3 : f (u + t • g) - f u ≤ L * (t * en g) := (le_abs_self _).trans h
    rw [inv_mul_le_iff₀ ht0']
    linarith
  have hle : fderiv ℝ f u g ≤ L * en g := le_of_tendsto ht hbound
  rw [hlin g] at hle
  have hgg : g ⬝ᵥ g = en g ^ 2 := by
    unfold en
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hgg] at hle ⊢
  have hen := en_nonneg g
  have : en g ≤ L := by
    by_contra h
    push Not at h
    nlinarith
  exact pow_le_pow_left₀ hen this 2

/-! ## Rotation invariance of a pair of independent Gaussian vectors -/

/-- The rotation `(x, y) ↦ (s·x + c·y, c·x − s·y)`. -/
def rotP (s c : ℝ) (p : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (s • p.1 + c • p.2, c • p.1 - s • p.2)

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_rotP (s c : ℝ) : Measurable (rotP (ι := ι) s c) := by
  unfold rotP
  fun_prop

lemma rotP_preserving {s c : ℝ} (hsc : s ^ 2 + c ^ 2 = 1) :
    MeasurePreserving (rotP (ι := ι) s c) ((stdGauss ι).prod (stdGauss ι))
      ((stdGauss ι).prod (stdGauss ι)) := by
  refine ⟨measurable_rotP s c, ?_⟩
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ) with he
  have hmp : MeasurePreserving e (stdGauss (ι ⊕ ι)) ((stdGauss ι).prod (stdGauss ι)) := by
    unfold stdGauss
    exact measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)
  set V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
    Matrix.fromBlocks (s • (1 : Matrix ι ι ℝ)) (c • 1) (c • 1) (-s • 1) with hV
  have hVV : V * Vᵀ = 1 := by
    rw [hV, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul]
    rw [← Matrix.fromBlocks_one]
    congr 1
    · rw [← add_smul]
      have : s * s + c * c = 1 := by nlinarith
      rw [this, one_smul]
    · rw [← add_smul]
      have : c * s + -s * c = 0 := by ring
      rw [this, zero_smul]
    · rw [← add_smul]
      have : s * c + c * -s = 0 := by ring
      rw [this, zero_smul]
    · rw [← add_smul]
      have : c * c + -s * -s = 1 := by nlinarith
      rw [this, one_smul]
  have hcomm : rotP s c ∘ e = e ∘ fun ξ => V.mulVec ξ := by
    funext ξ
    have hξ : ξ = Sum.elim (fun i => ξ (Sum.inl i)) (fun i => ξ (Sum.inr i)) := by
      funext j; cases j <;> rfl
    simp only [Function.comp_apply]
    conv_rhs => rw [hξ, hV, Matrix.fromBlocks_mulVec]
    refine Prod.ext ?_ ?_
    · funext i
      simp [rotP, he, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
        Matrix.smul_mulVec]
    · funext i
      simp [rotP, he, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
        Matrix.smul_mulVec, Matrix.neg_mulVec, sub_eq_add_neg]
  have hVm : Measurable fun ξ : ι ⊕ ι → ℝ => V.mulVec ξ := by fun_prop
  rw [← hmp.map_eq, Measure.map_map (measurable_rotP s c) e.measurable, hcomm,
    ← Measure.map_map e.measurable hVm, BstLean.Part109.stdGauss_map_orth V hVV]

/-! ## The path -/

omit [DecidableEq ι] in
lemma pth_hasDerivAt (x y : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin t • x + Real.cos t • y)
      (Real.cos θ • x - Real.sin θ • y) θ := by
  have h := ((Real.hasDerivAt_sin θ).smul_const x).add ((Real.hasDerivAt_cos θ).smul_const y)
  convert h using 1
  rw [neg_smul, sub_eq_add_neg]

omit [DecidableEq ι] in
lemma pth_lipschitz (x y : ι → ℝ) :
    LipschitzWith (‖x‖₊ + ‖y‖₊) (fun t : ℝ => Real.sin t • x + Real.cos t • y) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm, Real.dist_eq]
  have e : Real.sin a • x + Real.cos a • y - (Real.sin b • x + Real.cos b • y) =
      (Real.sin a - Real.sin b) • x + (Real.cos a - Real.cos b) • y := by
    rw [sub_smul, sub_smul]; abel
  rw [e]
  have h1 := Real.abs_sin_sub_sin_le a b
  have h2 := Real.abs_cos_sub_cos_le a b
  calc ‖(Real.sin a - Real.sin b) • x + (Real.cos a - Real.cos b) • y‖
      ≤ ‖(Real.sin a - Real.sin b) • x‖ + ‖(Real.cos a - Real.cos b) • y‖ := norm_add_le _ _
    _ = |Real.sin a - Real.sin b| * ‖x‖ + |Real.cos a - Real.cos b| * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |a - b| * ‖x‖ + |a - b| * ‖y‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = _ := by push_cast; ring

/-- The function along the path. -/
noncomputable def phiP (f : (ι → ℝ) → ℝ) (p : (ι → ℝ) × (ι → ℝ)) (t : ℝ) : ℝ :=
  f (Real.sin t • p.1 + Real.cos t • p.2)

omit [DecidableEq ι] in
lemma phiP_lipschitz (hL0 : 0 ≤ L) (hL : EuLip f L) (p : (ι → ℝ) × (ι → ℝ)) :
    LipschitzWith ((L * √(Fintype.card ι)).toNNReal * (‖p.1‖₊ + ‖p.2‖₊)) (phiP f p) :=
  (hL.lipschitz hL0).comp (pth_lipschitz p.1 p.2)

omit [DecidableEq ι] in
lemma phiP_deriv_bound (hL0 : 0 ≤ L) (hL : EuLip f L) (p : (ι → ℝ) × (ι → ℝ)) (θ : ℝ) :
    |deriv (phiP f p) θ| ≤
      (((L * √(Fintype.card ι)).toNNReal * (‖p.1‖₊ + ‖p.2‖₊) : ℝ≥0) : ℝ) := by
  have := norm_deriv_le_of_lipschitz (x₀ := θ) (phiP_lipschitz hL0 hL p)
  rwa [Real.norm_eq_abs] at this

omit [DecidableEq ι] in
lemma phiP_ftc (hL0 : 0 ≤ L) (hL : EuLip f L) (p : (ι → ℝ) × (ι → ℝ)) :
    ∫ θ in (0 : ℝ)..(π / 2), deriv (phiP f p) θ = f p.1 - f p.2 := by
  have hac : AbsolutelyContinuousOnInterval (phiP f p) 0 (π / 2) :=
    ((phiP_lipschitz hL0 hL p).lipschitzOnWith).absolutelyContinuousOnInterval
  rw [hac.integral_deriv_eq_sub]
  simp [phiP]

lemma ii_of_bdd {g : ℝ → ℝ} (hm : Measurable g) {C : ℝ} (hb : ∀ θ, |g θ| ≤ C) (a b : ℝ) :
    IntervalIntegrable g volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun' hm.aestronglyMeasurable
    (ae_of_all _ fun θ => by simpa using hb θ)

omit [DecidableEq ι] in
/-- Jensen's inequality along the path. -/
lemma phiP_jensen (hL0 : 0 ≤ L) (hL : EuLip f L) (p : (ι → ℝ) × (ι → ℝ)) (lam : ℝ) :
    Real.exp (lam * (f p.1 - f p.2)) ≤
      2 / π * ∫ θ in (0 : ℝ)..(π / 2), Real.exp (lam * (π / 2) * deriv (phiP f p) θ) := by
  have hpi := Real.pi_pos
  set C : ℝ := (((L * √(Fintype.card ι)).toNNReal * (‖p.1‖₊ + ‖p.2‖₊) : ℝ≥0) : ℝ) with hC
  have hC0 : 0 ≤ C := NNReal.coe_nonneg _
  have hb := phiP_deriv_bound hL0 hL p
  have md : Measurable (deriv (phiP f p)) := measurable_deriv _
  set F : ℝ → ℝ := fun θ => lam * (π / 2) * deriv (phiP f p) θ with hF
  have mF : Measurable F := md.const_mul _
  have bF : ∀ θ, |F θ| ≤ |lam * (π / 2)| * C := fun θ => by
    rw [hF]
    simp only
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb θ) (abs_nonneg _)
  have iF : IntervalIntegrable F volume 0 (π / 2) := ii_of_bdd mF bF _ _
  have bE : ∀ θ, |Real.exp (F θ)| ≤ Real.exp (|lam * (π / 2)| * C) := fun θ => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (bF θ))
  have iE : IntervalIntegrable (fun θ => Real.exp (F θ)) volume 0 (π / 2) :=
    ii_of_bdd mF.exp bE _ _
  set a : ℝ := lam * (f p.1 - f p.2) with ha
  have hint : ∫ θ in (0 : ℝ)..(π / 2), F θ = π / 2 * a := by
    rw [hF]
    simp only
    rw [intervalIntegral.integral_const_mul, phiP_ftc hL0 hL p, ha]
    ring
  have iG : IntervalIntegrable (fun θ => Real.exp a * (1 + (F θ - a))) volume 0 (π / 2) :=
    ((intervalIntegrable_const (c := (1 : ℝ))).add (iF.sub intervalIntegrable_const)).const_mul _
  have hmono : ∫ θ in (0 : ℝ)..(π / 2), Real.exp a * (1 + (F θ - a)) ≤
      ∫ θ in (0 : ℝ)..(π / 2), Real.exp (F θ) := by
    refine intervalIntegral.integral_mono_on (by positivity) iG iE fun θ _ => ?_
    have h := Real.add_one_le_exp (F θ - a)
    have e : Real.exp (F θ) = Real.exp a * Real.exp (F θ - a) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hval : ∫ θ in (0 : ℝ)..(π / 2), Real.exp a * (1 + (F θ - a)) = Real.exp a * (π / 2) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const (iF.sub intervalIntegrable_const),
      intervalIntegral.integral_sub iF intervalIntegrable_const, hint]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hval] at hmono
  have : Real.exp a = 2 / π * (Real.exp a * (π / 2)) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-! ## A fixed angle -/

/-- For a fixed angle: `E exp(μ·φ′(θ)) ≤ exp(μ²L²/2)`. -/
lemma fixed_angle (hL0 : 0 ≤ L) (hL : EuLip f L) (θ μ : ℝ) :
    ∫⁻ p : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal (Real.exp (μ * deriv (phiP f p) θ))
      ∂((stdGauss ι).prod (stdGauss ι)) ≤ ENNReal.ofReal (Real.exp (μ ^ 2 * L ^ 2 / 2)) := by
  have hcont := hL.continuous hL0
  have hdiff := hL.ae_diff hL0
  have hR := rotP_preserving (ι := ι) (s := Real.sin θ) (c := Real.cos θ)
    (Real.sin_sq_add_cos_sq θ)
  set G : (ι → ℝ) × (ι → ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (Real.exp (μ * lineDeriv ℝ f q.1 q.2)) with hG
  have mG : Measurable G :=
    ENNReal.measurable_ofReal.comp (((measurable_lineDeriv_uncurry hcont).const_mul μ).exp)
  -- almost everywhere the derivative along the path is the line derivative at the rotated pair
  have hae : ∀ᵐ p ∂((stdGauss ι).prod (stdGauss ι)),
      ENNReal.ofReal (Real.exp (μ * deriv (phiP f p) θ)) = G (rotP (Real.sin θ) (Real.cos θ) p) := by
    have h1 : ∀ᵐ q ∂((stdGauss ι).prod (stdGauss ι)), DifferentiableAt ℝ f q.1 :=
      Measure.quasiMeasurePreserving_fst.ae hdiff
    have h2 := hR.quasiMeasurePreserving.ae h1
    filter_upwards [h2] with p hp
    have hp' : DifferentiableAt ℝ f (Real.sin θ • p.1 + Real.cos θ • p.2) := hp
    have hd : HasDerivAt (phiP f p)
        (fderiv ℝ f (Real.sin θ • p.1 + Real.cos θ • p.2)
          (Real.cos θ • p.1 - Real.sin θ • p.2)) θ :=
      hp'.hasFDerivAt.comp_hasDerivAt θ (pth_hasDerivAt p.1 p.2 θ)
    rw [hd.deriv, hG]
    simp only [rotP]
    rw [hp'.lineDeriv_eq_fderiv]
  rw [lintegral_congr_ae hae, hR.lintegral_comp mG, lintegral_prod _ mG.aemeasurable]
  have hinner : ∀ᵐ u ∂stdGauss ι, ∫⁻ w, G (u, w) ∂stdGauss ι ≤
      ENNReal.ofReal (Real.exp (μ ^ 2 * L ^ 2 / 2)) := by
    filter_upwards [hdiff] with u hu
    obtain ⟨g, hlin, hgg⟩ := hL.grad hL0 hu
    have hgg0 : 0 ≤ g ⬝ᵥ g := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have e1 : ∀ w : ι → ℝ, G (u, w) =
        (fun t : ℝ => ENNReal.ofReal (Real.exp (μ * t))) (w ⬝ᵥ g) := by
      intro w
      simp only [hG]
      rw [hu.lineDeriv_eq_fderiv, hlin w]
    simp_rw [e1]
    have hm : Measurable fun w : ι → ℝ => w ⬝ᵥ g := by
      simp only [dotProduct]; fun_prop
    rw [← lintegral_map (f := fun t : ℝ => ENNReal.ofReal (Real.exp (μ * t)))
      (by fun_prop) hm, BstLean.Part131.stdGauss_dot,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal μ)
        (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm2 := mgf_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (g ⬝ᵥ g).toNNReal)
    have hm3 := congrFun hm2 μ
    unfold mgf at hm3
    rw [hm3]
    refine Real.exp_le_exp.mpr ?_
    rw [Real.coe_toNNReal _ hgg0]
    nlinarith [sq_nonneg μ]
  calc ∫⁻ u, ∫⁻ w, G (u, w) ∂stdGauss ι ∂stdGauss ι
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (μ ^ 2 * L ^ 2 / 2)) ∂stdGauss ι :=
        lintegral_mono_ae hinner
    _ = ENNReal.ofReal (Real.exp (μ ^ 2 * L ^ 2 / 2)) := by simp

/-! ## The pair inequality -/

/-- **Maurey–Pisier**: `E exp(λ(f(X) − f(Y))) ≤ exp(λ²(π²/8)L²)` for independent standard
Gaussian vectors `X`, `Y` and `f` Lipschitz for the Euclidean norm with constant `L`. -/
theorem gaussConc_pair (hL0 : 0 ≤ L) (hL : EuLip f L) (lam : ℝ) :
    ∫⁻ p : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal (Real.exp (lam * (f p.1 - f p.2)))
      ∂((stdGauss ι).prod (stdGauss ι)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (π ^ 2 / 8) * L ^ 2)) := by
  have hpi := Real.pi_pos
  have hcont := hL.continuous hL0
  set μ : ℝ := lam * (π / 2) with hμ
  set H : (ι → ℝ) × (ι → ℝ) → ℝ → ℝ≥0∞ :=
    fun p θ => ENNReal.ofReal (Real.exp (μ * deriv (phiP f p) θ)) with hH
  have hcu : Continuous (Function.uncurry (phiP f)) := by
    unfold phiP Function.uncurry
    exact hcont.comp (by fun_prop)
  have mD : Measurable (fun q : ((ι → ℝ) × (ι → ℝ)) × ℝ => deriv (phiP f q.1) q.2) :=
    measurable_deriv_with_param hcu
  have mH : Measurable (Function.uncurry H) :=
    ENNReal.measurable_ofReal.comp ((mD.const_mul μ).exp)
  -- pointwise
  have hpt : ∀ p : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal (Real.exp (lam * (f p.1 - f p.2))) ≤
      ENNReal.ofReal (2 / π) * ∫⁻ θ in Ioc (0 : ℝ) (π / 2), H p θ := by
    intro p
    have hj := phiP_jensen hL0 hL p lam
    have hb := phiP_deriv_bound hL0 hL p
    have md : Measurable (deriv (phiP f p)) := measurable_deriv _
    have iE : IntervalIntegrable (fun θ => Real.exp (μ * deriv (phiP f p) θ)) volume 0 (π / 2) := by
      refine ii_of_bdd (md.const_mul μ).exp (C := Real.exp (|μ| *
        (((L * √(Fintype.card ι)).toNNReal * (‖p.1‖₊ + ‖p.2‖₊) : ℝ≥0) : ℝ))) (fun θ => ?_) _ _
      rw [abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb θ) (abs_nonneg _)
    have e : ∫⁻ θ in Ioc (0 : ℝ) (π / 2), H p θ =
        ENNReal.ofReal (∫ θ in (0 : ℝ)..(π / 2), Real.exp (μ * deriv (phiP f p) θ)) := by
      rw [intervalIntegral.integral_of_le (by positivity),
        ofReal_integral_eq_lintegral_ofReal iE.1 (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    rw [e, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hj
  calc ∫⁻ p : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal (Real.exp (lam * (f p.1 - f p.2)))
        ∂((stdGauss ι).prod (stdGauss ι))
      ≤ ∫⁻ p : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal (2 / π) *
          (∫⁻ θ in Ioc (0 : ℝ) (π / 2), H p θ) ∂((stdGauss ι).prod (stdGauss ι)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 / π) * ∫⁻ p : (ι → ℝ) × (ι → ℝ),
          (∫⁻ θ in Ioc (0 : ℝ) (π / 2), H p θ) ∂((stdGauss ι).prod (stdGauss ι)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 / π) * ∫⁻ θ in Ioc (0 : ℝ) (π / 2),
          ∫⁻ p : (ι → ℝ) × (ι → ℝ), H p θ ∂((stdGauss ι).prod (stdGauss ι)) := by
        rw [lintegral_lintegral_swap mH.aemeasurable]
    _ ≤ ENNReal.ofReal (2 / π) * ∫⁻ _ in Ioc (0 : ℝ) (π / 2),
          ENNReal.ofReal (Real.exp (μ ^ 2 * L ^ 2 / 2)) :=
        mul_le_mul' le_rfl (lintegral_mono fun θ => fixed_angle hL0 hL θ μ)
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * (π ^ 2 / 8) * L ^ 2)) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have e : μ ^ 2 * L ^ 2 / 2 = lam ^ 2 * (π ^ 2 / 8) * L ^ 2 := by rw [hμ]; ring
        rw [e]
        field_simp

/-! ## The moment generating function -/

/-- **The moment generating function of a Lipschitz function of a Gaussian vector.** -/
theorem gaussConc_mgf (hL0 : 0 ≤ L) (hL : EuLip f L) (lam : ℝ) :
    Integrable f (stdGauss ι) ∧ Integrable (fun x => Real.exp (lam * f x)) (stdGauss ι) ∧
    ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂stdGauss ι)) ∂stdGauss ι ≤
      Real.exp (lam ^ 2 * (π ^ 2 / 8) * L ^ 2) := by
  have hcont := hL.continuous hL0
  have hmf : Measurable f := hcont.measurable
  -- the product form of the pair inequality
  have hprod : ∀ l : ℝ, (∫⁻ x, ENNReal.ofReal (Real.exp (l * f x)) ∂stdGauss ι) *
      (∫⁻ y, ENNReal.ofReal (Real.exp (-l * f y)) ∂stdGauss ι) ≤
      ENNReal.ofReal (Real.exp (l ^ 2 * (π ^ 2 / 8) * L ^ 2)) := by
    intro l
    have h := gaussConc_pair hL0 hL l
    have e : (fun p : (ι → ℝ) × (ι → ℝ) => ENNReal.ofReal (Real.exp (l * (f p.1 - f p.2)))) =
        fun p => ENNReal.ofReal (Real.exp (l * f p.1)) *
          ENNReal.ofReal (Real.exp (-l * f p.2)) := by
      funext p
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    rw [e, lintegral_prod_mul (μ := stdGauss ι) (ν := stdGauss ι)
      (f := fun x => ENNReal.ofReal (Real.exp (l * f x)))
      (g := fun y => ENNReal.ofReal (Real.exp (-l * f y)))
      (ENNReal.measurable_ofReal.comp (hmf.const_mul l).exp).aemeasurable
      (ENNReal.measurable_ofReal.comp (hmf.const_mul (-l)).exp).aemeasurable] at h
    exact h
  have hpos : ∀ l : ℝ, (∫⁻ y, ENNReal.ofReal (Real.exp (l * f y)) ∂stdGauss ι) ≠ 0 := by
    intro l h
    rw [lintegral_eq_zero_iff (by fun_prop)] at h
    have : ∀ᵐ y ∂stdGauss ι, False := by
      filter_upwards [h] with y hy
      have : ENNReal.ofReal (Real.exp (l * f y)) = 0 := hy
      rw [ENNReal.ofReal_eq_zero] at this
      exact absurd this (not_le.mpr (Real.exp_pos _))
    obtain ⟨y, hy⟩ := this.exists
    exact hy
  have hfin : ∀ l : ℝ, (∫⁻ x, ENNReal.ofReal (Real.exp (l * f x)) ∂stdGauss ι) ≠ ⊤ := by
    intro l htop
    have h := hprod l
    rw [htop, ENNReal.top_mul (hpos (-l))] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  have hint : ∀ l : ℝ, Integrable (fun x => Real.exp (l * f x)) (stdGauss ι) := by
    intro l
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact lt_top_iff_ne_top.mpr (hfin l)
  have hfint : Integrable f (stdGauss ι) := by
    refine Integrable.mono' ((hint 1).add (hint (-1))) hmf.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply, one_mul, neg_mul]
    have h1 := Real.add_one_le_exp (f x)
    have h2 := Real.add_one_le_exp (-f x)
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos (f x), Real.exp_pos (-f x)]
  refine ⟨hfint, hint lam, ?_⟩
  set m : ℝ := ∫ y, f y ∂stdGauss ι with hm
  -- Jensen in `y`
  have hJ : Real.exp (-lam * m) ≤ ∫ y, Real.exp (-lam * f y) ∂stdGauss ι := by
    have h := (convexOn_exp).map_integral_le (μ := stdGauss ι) (f := fun y => -lam * f y)
      Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _)
      (hfint.const_mul _) (hint (-lam))
    rw [integral_const_mul] at h
    exact h
  have e1 : ∫ x, Real.exp (lam * (f x - m)) ∂stdGauss ι =
      Real.exp (-lam * m) * ∫ x, Real.exp (lam * f x) ∂stdGauss ι := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e1]
  have hI1 : 0 ≤ ∫ x, Real.exp (lam * f x) ∂stdGauss ι :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have h3 := hprod lam
  rw [← ofReal_integral_eq_lintegral_ofReal (hint lam) (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal (hint (-lam))
      (ae_of_all _ fun _ => (Real.exp_pos _).le), ← ENNReal.ofReal_mul hI1,
    ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at h3
  calc Real.exp (-lam * m) * ∫ x, Real.exp (lam * f x) ∂stdGauss ι
      ≤ (∫ y, Real.exp (-lam * f y) ∂stdGauss ι) * ∫ x, Real.exp (lam * f x) ∂stdGauss ι :=
        mul_le_mul_of_nonneg_right hJ hI1
    _ = (∫ x, Real.exp (lam * f x) ∂stdGauss ι) * ∫ y, Real.exp (-lam * f y) ∂stdGauss ι :=
        mul_comm _ _
    _ ≤ _ := h3

/-! ## The tails -/

/-- **Gaussian concentration, lower tail**: `Pr(f ≤ E f − t) ≤ exp(−2t²/(π²L²))`. -/
theorem gaussConc_lower (hL0 : 0 ≤ L) (hL : EuLip f L) {t : ℝ} (ht : 0 ≤ t) :
    (stdGauss ι).real {x | f x ≤ ∫ y, f y ∂stdGauss ι - t} ≤
      Real.exp (-2 * t ^ 2 / (π ^ 2 * L ^ 2)) := by
  have hpi := Real.pi_pos
  rcases hL0.eq_or_lt with h0 | hLpos
  · rw [← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero,
      Real.exp_zero]
    exact measureReal_le_one
  set m : ℝ := ∫ y, f y ∂stdGauss ι with hm
  set s : ℝ := 4 * t / (π ^ 2 * L ^ 2) with hs
  have hs0 : 0 ≤ s := by positivity
  obtain ⟨_, hI, hM⟩ := gaussConc_mgf hL0 hL (-s)
  have hI' : Integrable (fun x => Real.exp (-s * (f x - m))) (stdGauss ι) := by
    have e : (fun x => Real.exp (-s * (f x - m))) =
        fun x => Real.exp (s * m) * Real.exp (-s * f x) := by
      funext x
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact hI.const_mul _
  have h := measure_le_le_exp_mul_mgf (μ := stdGauss ι) (X := fun x => f x - m) (t := -s)
    (-t) (by linarith) hI'
  have hset : {x : ι → ℝ | f x - m ≤ -t} = {x | f x ≤ m - t} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  refine h.trans ?_
  unfold mgf
  calc Real.exp (- -s * -t) * ∫ x, Real.exp (-s * (f x - m)) ∂stdGauss ι
      ≤ Real.exp (- -s * -t) * Real.exp ((-s) ^ 2 * (π ^ 2 / 8) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = Real.exp (-2 * t ^ 2 / (π ^ 2 * L ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hs]
        field_simp
        ring

/-- **Gaussian concentration, upper tail**: `Pr(f ≥ E f + t) ≤ exp(−2t²/(π²L²))`. -/
theorem gaussConc_upper (hL0 : 0 ≤ L) (hL : EuLip f L) {t : ℝ} (ht : 0 ≤ t) :
    (stdGauss ι).real {x | ∫ y, f y ∂stdGauss ι + t ≤ f x} ≤
      Real.exp (-2 * t ^ 2 / (π ^ 2 * L ^ 2)) := by
  have hLn : EuLip (fun x => -f x) L := by
    intro x y
    have := hL x y
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    exact this
  have h := gaussConc_lower hL0 hLn ht
  rw [integral_neg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

end GC

/-! ## The matrix form -/

section mat

open BstLean.Part130

variable {m k : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L : ℝ}

lemma matLip_continuous
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro M0
  have hij : ∀ i j, Continuous fun M : Matrix (Fin m) (Fin k) ℝ => M i j :=
    fun i j => continuous_id.matrix_elem i j
  have hc : Continuous fun M : Matrix (Fin m) (Fin k) ℝ =>
      L * √(∑ i, ∑ j, (M i j - M0 i j) ^ 2) := by
    refine continuous_const.mul (Real.continuous_sqrt.comp ?_)
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hij i j).sub continuous_const).pow 2
  have h0 := hc.tendsto M0
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, Real.sqrt_zero, mul_zero] at h0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) h0
  rw [Real.norm_eq_abs]
  exact hL M M0

/-- **Gaussian concentration for a Lipschitz function of a Gaussian matrix, lower tail.** If
`|g M − g M′| ≤ L·√(Σ_{ij}(M_{ij} − M′_{ij})²)` and the entries are independent `N(0, v)`:
`Pr(g ≤ E g − t) ≤ exp(−2t²/(π²·v·L²))`. -/
theorem gaussConc_mat_lower (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat m k v).real {M | g M ≤ ∫ M, g M ∂gaussMat m k v - t} ≤
      Real.exp (-2 * t ^ 2 / (π ^ 2 * (v * L ^ 2))) := by
  have hgc := matLip_continuous hL
  set T : (Fin m × Fin k → ℝ) → Matrix (Fin m) (Fin k) ℝ :=
    fun ξ => Matrix.of fun i j => Real.sqrt v * ξ (i, j) with hT
  have mT : Measurable T := measurable_ofFlat _
  have hf : EuLip (fun ξ => g (T ξ)) (√v * L) := by
    intro ξ η
    have h := hL (T ξ) (T η)
    have e : ∑ i, ∑ j, (T ξ i j - T η i j) ^ 2 = v * ∑ p, (ξ p - η p) ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hT, Matrix.of_apply]
      rw [← mul_sub, mul_pow, Real.sq_sqrt hv]
    rw [e, Real.sqrt_mul hv] at h
    refine h.trans (le_of_eq ?_)
    ring
  have h := gaussConc_lower (mul_nonneg (Real.sqrt_nonneg v) hL0) hf ht
  have eI : ∫ M, g M ∂gaussMat m k v = ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) := by
    unfold gaussMat
    exact integral_map mT.aemeasurable hgc.measurable.aestronglyMeasurable
  have mS : MeasurableSet {M : Matrix (Fin m) (Fin k) ℝ | g M ≤ ∫ M, g M ∂gaussMat m k v - t} :=
    measurableSet_le hgc.measurable measurable_const
  have eS : (gaussMat m k v).real {M | g M ≤ ∫ M, g M ∂gaussMat m k v - t} =
      (stdGauss (Fin m × Fin k)).real
        {ξ | g (T ξ) ≤ ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) - t} := by
    have e1 := map_measureReal_apply (μ := stdGauss (Fin m × Fin k)) mT mS
    rw [← eI]
    exact e1
  rw [eS]
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hv]

/-- **Gaussian concentration for a Lipschitz function of a Gaussian matrix, upper tail.** -/
theorem gaussConc_mat_upper (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat m k v).real {M | ∫ M, g M ∂gaussMat m k v + t ≤ g M} ≤
      Real.exp (-2 * t ^ 2 / (π ^ 2 * (v * L ^ 2))) := by
  have hLn : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |(fun M => -g M) M - (fun M => -g M) M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
    intro M M'
    have := hL M M'
    simp only
    rw [show -g M - -g M' = -(g M - g M') by ring, abs_neg]
    exact this
  have h := gaussConc_mat_lower hL0 hLn hv ht
  rw [integral_neg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

end mat

end BstLean.Part148

open BstLean.Part148 in
#print axioms gaussConc_mat_lower
open BstLean.Part148 in
#print axioms gaussConc_mat_upper
open BstLean.Part148 in
#print axioms gaussConc_pair
open BstLean.Part148 in
#print axioms gaussConc_mgf
open BstLean.Part148 in
#print axioms gaussConc_lower
open BstLean.Part148 in
#print axioms gaussConc_upper
