import BstLean.Part144Block2

/-!
# Part 144, the two-sided tangent form of the block bound

Role: `delegations/statements/p144-spec.md` (tools for the sharper form of item 2).
`Φ̄(t) = (gaussianReal 0 1).real (Ioi t)`, `φ = gaussianPDFReal 0 1`.

* `mills_upper`: `Φ̄(t) ≤ φ(t)/t` for `t > 0`.
* `tail_two_sided`: `Φ̄(x1) + Φ̄(x2) ≥ 2Φ̄(t)` for `x1·x2 = t²`, `t ≥ 1`, `x1, x2 > 0`.
* `gauss_block_tangent2`: twice the bound of `gauss_block_tangent` (both signs of the Gaussian
  coordinate along `v`), if `2(Φ̄(t0) + κ·t0²) ≤ Φ̄(1)`, `κ = φ(t0)/(2t0)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144
open MeasureTheory ProbabilityTheory Set Matrix Filter
open scoped Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part131 BstLean.Part135

/-- **The Mills upper bound**: `Φ̄(t) ≤ φ(t)/t` for `t > 0`. -/
theorem mills_upper {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real (Ioi t) ≤ gaussianPDFReal 0 1 t / t := by
  have hint := integrable_gaussianPDFReal 0 1
  rw [gauss_real_eq]
  set K : ℝ := 1 + 1 / t ^ 2 with hK
  let f : ℝ → ℝ := fun x => -(gaussianPDFReal 0 1 x / x)
  let f' : ℝ → ℝ := fun x => gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)
  have hderiv : ∀ x ∈ Ici t, HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ht hx).ne'
    have h3 := ((pdf_hasDerivAt x).div (hasDerivAt_id x) hx0).neg
    have h4 : HasDerivAt f
        (-((gaussianPDFReal 0 1 x * -x * id x - gaussianPDFReal 0 1 x * 1) / id x ^ 2)) x := h3
    have e4 : f' x =
        -((gaussianPDFReal 0 1 x * -x * id x - gaussianPDFReal 0 1 x * 1) / id x ^ 2) := by
      simp only [f', id]
      field_simp
      ring
    rw [e4]; exact h4
  have hbd : ∀ x : ℝ, t < x → 1 + 1 / x ^ 2 ≤ K := by
    intro x hx
    have h1 : t ^ 2 ≤ x ^ 2 := by nlinarith
    have h2 : 1 / x ^ 2 ≤ 1 / t ^ 2 := one_div_le_one_div_of_le (by positivity) h1
    rw [hK]; linarith
  have hf'int : IntegrableOn f' (Ioi t) := by
    refine Integrable.mono' (hint.const_mul K).integrableOn
      ((hint.aestronglyMeasurable.mul (measurable_const.add
        (measurable_const.div (measurable_id.pow_const 2))).aestronglyMeasurable).restrict) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : t < x := hx
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h2 := hbd x hx1
    have h3 : 0 ≤ 1 / x ^ 2 := by positivity
    simp only [f', Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have htend : Tendsto f atTop (𝓝 0) := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖f x‖ ≤ phi1 * Real.exp (1 / 2) * x⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [f, norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) hx.le), pdf_eq_phi1,
        div_eq_mul_inv]
      have : Real.exp ((1 - x ^ 2) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      have h2 := phi1_pos
      have h3 : 0 < x⁻¹ := inv_pos.mpr hx
      gcongr
    have h0 : Tendsto (fun x : ℝ => phi1 * Real.exp (1 / 2) * x⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (phi1 * Real.exp (1 / 2))
    exact squeeze_zero_norm' hb h0
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hf'int htend
  have hle : ∫ x in Ioi t, gaussianPDFReal 0 1 x ≤ ∫ x in Ioi t, f' x := by
    refine setIntegral_mono_on hint.integrableOn hf'int measurableSet_Ioi ?_
    intro x hx
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h3 : 0 ≤ 1 / x ^ 2 := by positivity
    simp only [f']
    nlinarith
  rw [hI] at hle
  have hft : f t = -(gaussianPDFReal 0 1 t / t) := rfl
  rw [hft, zero_sub, neg_neg] at hle
  exact hle

/-- The primitive `x ↦ ∫_0^x φ` of the standard Gaussian density. -/
noncomputable def gPrim (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, gaussianPDFReal 0 1 y

lemma pdf_continuous : Continuous fun x : ℝ => gaussianPDFReal 0 1 x := by
  have e : (fun x : ℝ => gaussianPDFReal 0 1 x) =
      fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := funext pdf_eq
  rw [e]; fun_prop

lemma gPrim_hasDerivAt (x : ℝ) : HasDerivAt gPrim (gaussianPDFReal 0 1 x) x :=
  intervalIntegral.integral_hasDerivAt_right (pdf_continuous.intervalIntegrable _ _)
    pdf_continuous.stronglyMeasurable.stronglyMeasurableAtFilter pdf_continuous.continuousAt

/-- `Φ̄(x) = Φ̄(0) − ∫_0^x φ` for `x ≥ 0`. -/
lemma tail_eq_gPrim {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 1).real (Ioi x) = (gaussianReal 0 1).real (Ioi 0) - gPrim x := by
  have hu : Ioi (0 : ℝ) = Ioc 0 x ∪ Ioi x := (Ioc_union_Ioi_eq_Ioi hx).symm
  have hd : Disjoint (Ioc 0 x) (Ioi x) := by
    rw [Set.disjoint_left]; intro y hy hy'; exact absurd hy.2 (not_le.mpr hy')
  have h0 : (gaussianReal 0 1).real (Ioi 0) =
      (gaussianReal 0 1).real (Ioc 0 x) + (gaussianReal 0 1).real (Ioi x) := by
    conv_lhs => rw [hu]
    exact measureReal_union hd measurableSet_Ioi
  rw [gauss_real_eq (Ioc 0 x), ← intervalIntegral.integral_of_le hx] at h0
  unfold gPrim
  linarith

/-- `φ(t²/x)·t²/x² ≤ φ(x)` for `0 < x ≤ t`, `t ≥ 1`. -/
lemma pdf_reflect_le {t x : ℝ} (ht : 1 ≤ t) (hx0 : 0 < x) (hxt : x ≤ t) :
    gaussianPDFReal 0 1 (t ^ 2 / x) * (t ^ 2 / x ^ 2) ≤ gaussianPDFReal 0 1 x := by
  have ht0 : 0 < t := by linarith
  set r : ℝ := t ^ 2 / x ^ 2 with hr
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ (by positivity)]; nlinarith
  have hr0 : 0 < r := by linarith
  set w : ℝ := Real.log r with hw
  have hw0 : 0 ≤ w := Real.log_nonneg hr1
  have hexp : Real.exp w = r := Real.exp_log hr0
  have hsinh : w ≤ (r - r⁻¹) / 2 := by
    have h1 := Real.self_le_sinh_iff.mpr hw0
    rw [Real.sinh_eq, Real.exp_neg, hexp] at h1
    exact h1
  have hrr : 0 ≤ r - r⁻¹ := by
    have : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
    linarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have h2 : (r - r⁻¹) / 2 ≤ t ^ 2 * (r - r⁻¹) / 2 := by nlinarith
  have e3 : t ^ 2 * (r - r⁻¹) / 2 = (t ^ 2 / x) ^ 2 / 2 - x ^ 2 / 2 := by
    rw [hr]; field_simp
  have h4 : r ≤ Real.exp ((t ^ 2 / x) ^ 2 / 2 - x ^ 2 / 2) := by
    rw [← hexp]; exact Real.exp_le_exp.mpr (by linarith)
  rw [pdf_eq, pdf_eq]
  have hC : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  have h5 : Real.exp (-((t ^ 2 / x) ^ 2 / 2)) * r ≤ Real.exp (-(x ^ 2 / 2)) := by
    have h6 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos (-((t ^ 2 / x) ^ 2 / 2))).le
    rw [← Real.exp_add] at h6
    refine h6.trans (le_of_eq ?_)
    congr 1; ring
  calc (√(2 * Real.pi))⁻¹ * Real.exp (-((t ^ 2 / x) ^ 2 / 2)) * r
      = (√(2 * Real.pi))⁻¹ * (Real.exp (-((t ^ 2 / x) ^ 2 / 2)) * r) := by ring
    _ ≤ (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := mul_le_mul_of_nonneg_left h5 hC

/-- **Two tails with a fixed geometric mean `t ≥ 1`**: `Φ̄(x1) + Φ̄(x2) ≥ 2Φ̄(t)` for
`x1·x2 = t²`, `x1, x2 > 0`. -/
theorem tail_two_sided {t x1 x2 : ℝ} (ht : 1 ≤ t) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hx : x1 * x2 = t ^ 2) :
    2 * (gaussianReal 0 1).real (Ioi t) ≤
      (gaussianReal 0 1).real (Ioi x1) + (gaussianReal 0 1).real (Ioi x2) := by
  have ht0 : 0 < t := by linarith
  -- the case `x1 ≤ t`
  have key : ∀ y1 y2 : ℝ, 0 < y1 → y1 ≤ t → y1 * y2 = t ^ 2 →
      gPrim y1 + gPrim y2 ≤ 2 * gPrim t := by
    intro y1 y2 hy1 hy1t hy
    have hy2 : y2 = t ^ 2 / y1 := by rw [eq_div_iff hy1.ne']; linarith
    let H : ℝ → ℝ := fun x => gPrim x + gPrim (t ^ 2 / x)
    have hH : ∀ x : ℝ, 0 < x → HasDerivAt H
        (gaussianPDFReal 0 1 x + gaussianPDFReal 0 1 (t ^ 2 / x) * (-(t ^ 2) / x ^ 2)) x := by
      intro x hx0
      have h1 : HasDerivAt (fun x : ℝ => t ^ 2 / x) (-(t ^ 2) / x ^ 2) x := by
        have := (hasDerivAt_inv hx0.ne').const_mul (t ^ 2)
        convert this using 1
        · funext y; rw [div_eq_mul_inv]
        · ring
      have h2 := (gPrim_hasDerivAt (t ^ 2 / x)).comp x h1
      exact (gPrim_hasDerivAt x).add h2
    have hmono : MonotoneOn H (Icc y1 t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc y1 t) ?_ ?_ ?_
      · intro x hx
        exact (hH x (lt_of_lt_of_le hy1 hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hH x (lt_trans hy1 hx.1)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := lt_trans hy1 hx.1
        rw [(hH x hx0).deriv]
        have h := pdf_reflect_le ht hx0 hx.2.le
        have e : gaussianPDFReal 0 1 (t ^ 2 / x) * (-(t ^ 2) / x ^ 2) =
            -(gaussianPDFReal 0 1 (t ^ 2 / x) * (t ^ 2 / x ^ 2)) := by ring
        rw [e]; linarith
    have h := hmono (left_mem_Icc.mpr hy1t) (right_mem_Icc.mpr hy1t) hy1t
    have eH1 : H y1 = gPrim y1 + gPrim y2 := by simp only [H]; rw [hy2]
    have eH2 : H t = 2 * gPrim t := by
      simp only [H]
      have : t ^ 2 / t = t := by field_simp
      rw [this]; ring
    rw [eH1, eH2] at h
    exact h
  have hfin : gPrim x1 + gPrim x2 ≤ 2 * gPrim t := by
    rcases le_total x1 t with h | h
    · exact key x1 x2 hx1 h hx
    · have h2 : x2 ≤ t := by
        by_contra hcon
        have : t < x2 := not_le.mp hcon
        nlinarith
      have := key x2 x1 hx2 h2 (by rw [mul_comm]; exact hx)
      linarith
  rw [tail_eq_gPrim ht0.le, tail_eq_gPrim hx1.le, tail_eq_gPrim hx2.le]
  linarith

/-- Both tails of a quadratic: for `δ > 0`, `q ≥ δ`:
`γ{x | δx² − bx − q > 0} ≥ 2Φ̄(√(q/δ))`. -/
lemma two_roots {δ b q : ℝ} (hδpos : 0 < δ) (hqd : δ ≤ q) :
    2 * (gaussianReal 0 1).real (Ioi (√(q / δ))) ≤
      (gaussianReal 0 1).real {x : ℝ | 0 < δ * x ^ 2 - b * x - q} := by
  have hqpos : 0 < q := by linarith
  set t : ℝ := √(q / δ) with ht
  have htt : t ^ 2 = q / δ := Real.sq_sqrt (div_nonneg hqpos.le hδpos.le)
  have h1q : 1 ≤ q / δ := by rw [le_div_iff₀ hδpos]; linarith
  have ht1 : 1 ≤ t := by
    rw [ht]; exact Real.one_le_sqrt.mpr h1q
  set s : ℝ := √(b ^ 2 + 4 * δ * q) with hsd
  have hpos : 0 < δ * q := mul_pos hδpos hqpos
  have hs2 : s ^ 2 = b ^ 2 + 4 * δ * q := Real.sq_sqrt (by nlinarith [sq_nonneg b])
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsb : |b| < s := by
    apply abs_lt_of_sq_lt_sq _ hs0
    rw [hs2]; nlinarith
  obtain ⟨hsb1, hsb2⟩ := abs_lt.mp hsb
  set rp : ℝ := (b + s) / (2 * δ) with hrp
  set rm : ℝ := (s - b) / (2 * δ) with hrm
  have hrp0 : 0 < rp := by rw [hrp]; apply div_pos <;> linarith
  have hrm0 : 0 < rm := by rw [hrm]; apply div_pos <;> linarith
  have e0 : (s ^ 2 - b ^ 2) / (4 * δ) = q := by rw [hs2]; field_simp; ring
  have hprod : rp * rm = t ^ 2 := by
    have e1 : rp * rm = (s ^ 2 - b ^ 2) / (4 * δ) / δ := by rw [hrp, hrm]; field_simp; ring
    rw [e1, e0, htt]
  have hid : ∀ x : ℝ, δ * (x - rp) * (x + rm) = δ * x ^ 2 - b * x - q := by
    intro x
    have e1 : δ * (x - rp) * (x + rm) = δ * x ^ 2 - b * x - (s ^ 2 - b ^ 2) / (4 * δ) := by
      rw [hrp, hrm]; field_simp; ring
    rw [e1, e0]
  have hsub1 : Ioi rp ⊆ {x : ℝ | 0 < δ * x ^ 2 - b * x - q} := by
    intro x hx
    have hx' : rp < x := hx
    rw [mem_ofPred_eq, ← hid]
    have h1 : 0 < δ * (x - rp) := mul_pos hδpos (by linarith)
    exact mul_pos h1 (by linarith)
  have hsub2 : Iio (-rm) ⊆ {x : ℝ | 0 < δ * x ^ 2 - b * x - q} := by
    intro x hx
    have hx' : x < -rm := hx
    rw [mem_ofPred_eq, ← hid]
    have h1 : δ * (x - rp) < 0 := mul_neg_of_pos_of_neg hδpos (by linarith)
    exact mul_pos_of_neg_of_neg h1 (by linarith)
  have hdis : Disjoint (Ioi rp) (Iio (-rm)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : rp < x := hx
    have h2 : x < -rm := hx'
    linarith
  have hun : (gaussianReal 0 1).real (Ioi rp ∪ Iio (-rm)) ≤
      (gaussianReal 0 1).real {x : ℝ | 0 < δ * x ^ 2 - b * x - q} :=
    measureReal_mono (union_subset hsub1 hsub2)
  rw [measureReal_union hdis measurableSet_Iio, tail_neg rm] at hun
  have h2 := tail_two_sided ht1 hrp0 hrm0 hprod
  linarith

/-- **The two-sided tangent form of the block bound.** With `D = |v|² > 0`, `a = vᵀMv/D < D`,
a level `t0 > 0` with `2(Φ̄(t0) + κ·t0²) ≤ Φ̄(1)`, `κ = φ(t0)/(2t0)`:
`Pr(gᵀMg < (g·v)²) ≥ 2·(Φ̄(t0) + κ·(t0² − (tr M − a)/(D − a)))`. -/
theorem gauss_block_tangent2 {ι : Type} [Fintype ι] (v : ι → ℝ) (M : Matrix ι ι ℝ)
    (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y) {t0 : ℝ} (ht0 : 0 < t0)
    (hD0 : 0 < v ⬝ᵥ v) (hδ0 : v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v) < v ⬝ᵥ v)
    (hA1 : 2 * ((gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2) ≤
      (gaussianReal 0 1).real (Ioi 1)) :
    2 * ((gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) *
        (t0 ^ 2 - (M.trace - v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v)) /
          (v ⬝ᵥ v - v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v)))) ≤
      (stdGauss ι).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} := by
  classical
  set D : ℝ := v ⬝ᵥ v with hD
  have hDpos : 0 < D := hD0
  set s : ℝ := √D with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hDpos
  have hss : s ^ 2 = D := Real.sq_sqrt hDpos.le
  set e : ι → ℝ := s⁻¹ • v with he_def
  have hve : v = s • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
  have he : e ⬝ᵥ e = 1 := by
    rw [he_def, smul_dotProduct, dotProduct_smul, ← hD, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  set P := projMat e with hP
  set a : ℝ := e ⬝ᵥ M *ᵥ e with ha
  have ha0 : 0 ≤ a := hM e
  let q : (ι → ℝ) → ℝ := fun h => (P *ᵥ h) ⬝ᵥ M *ᵥ (P *ᵥ h)
  let β : (ι → ℝ) → ℝ := fun h => e ⬝ᵥ M *ᵥ (P *ᵥ h) + (P *ᵥ h) ⬝ᵥ M *ᵥ e
  have hq0 : ∀ h, 0 ≤ q h := fun h => hM _
  have hqN : ∀ h, q h = h ⬝ᵥ (Pᵀ * M * P) *ᵥ h := by
    intro h
    simp only [q]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec h, vecMul_transpose]
  have hqint : Integrable q (stdGauss ι) := by
    rw [show q = fun h => h ⬝ᵥ (Pᵀ * M * P) *ᵥ h from funext hqN]; exact qform_integrable _
  have hEq : ∫ h, q h ∂stdGauss ι = M.trace - a := by
    rw [show q = fun h => h ⬝ᵥ (Pᵀ * M * P) *ᵥ h from funext hqN]
    rw [qform_integral, trace_mul_cycle, hP, projMat_transpose, projMat_mul_self he, projMat,
      Matrix.sub_mul, Matrix.one_mul, trace_sub, vecMulVec_mul, trace_vecMulVec, ha,
      dotProduct_mulVec, dotProduct_comm]
  have haT : a ≤ M.trace := by
    have : 0 ≤ ∫ h, q h ∂stdGauss ι := integral_nonneg hq0
    linarith
  have haR : a = v ⬝ᵥ M *ᵥ v / D := by
    rw [ha, he_def, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← hss]
    field_simp
  rw [← haR] at hδ0 ⊢
  set δ : ℝ := D - a with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- the event in the coordinates `(x, h)`
  let Φ : ℝ × (ι → ℝ) → ι → ℝ := fun p => p.1 • e + P *ᵥ p.2
  have hΦ : Measurable Φ := by fun_prop
  set S : Set (ι → ℝ) := {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} with hSdef
  have hS : MeasurableSet S := by
    have h1 : Continuous fun g : ι → ℝ => g ⬝ᵥ M *ᵥ g := by fun_prop
    have h2 : Continuous fun g : ι → ℝ => (g ⬝ᵥ v) ^ 2 := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  have hmem : ∀ (x : ℝ) (h : ι → ℝ), Φ (x, h) ∈ S ↔ x ^ 2 * a + x * β h + q h < D * x ^ 2 := by
    intro x h
    have h0 : (P *ᵥ h) ⬝ᵥ e = 0 := projMat_dot he h
    have e1 : Φ (x, h) ⬝ᵥ M *ᵥ Φ (x, h) = x ^ 2 * a + x * β h + q h := by
      simp only [Φ, β, q, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, ha]
      ring
    have e2 : (Φ (x, h) ⬝ᵥ v) ^ 2 = D * x ^ 2 := by
      simp only [Φ]
      rw [hve, dotProduct_smul, add_dotProduct, smul_dotProduct, he, h0, ← hss]
      simp only [smul_eq_mul]; ring
    change Φ (x, h) ⬝ᵥ M *ᵥ Φ (x, h) < (Φ (x, h) ⬝ᵥ v) ^ 2 ↔ _
    rw [e1, e2]
  have hreal : (stdGauss ι).real S =
      ∫ h, (gaussianReal 0 1).real {x | Φ (x, h) ∈ S} ∂stdGauss ι := by
    conv_lhs => rw [← stdGauss_decomp he]
    rw [map_measureReal_apply hΦ hS, Measure.real, Measure.prod_apply_symm (hΦ hS),
      ← integral_toReal (measurable_measure_prodMk_right (hΦ hS)).aemeasurable
        (ae_of_all _ fun h => measure_lt_top _ _)]
    rfl
  set c : ℝ := gaussianPDFReal 0 1 t0 / (2 * t0) with hc
  have hcpos : 0 < c := by
    have : 0 < gaussianPDFReal 0 1 t0 := by rw [pdf_eq]; positivity
    positivity
  set T1 : ℝ := (gaussianReal 0 1).real (Ioi t0) with hT1
  -- the pointwise lower bound, both signs
  have hpt : ∀ h, 2 * (T1 + c * (t0 ^ 2 - q h / δ)) ≤
      (gaussianReal 0 1).real {x | Φ (x, h) ∈ S} := by
    intro h
    set t : ℝ := √(q h / δ) with ht
    have htn : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t ^ 2 = q h / δ := Real.sq_sqrt (div_nonneg (hq0 h) hδpos.le)
    have hline := tail_line_at ht0 htn
    rw [htt] at hline
    rcases le_or_gt 1 t with ht1 | ht1
    · -- both tails
      have hqd : δ ≤ q h := by
        have h1 : 1 ≤ q h / δ := by rw [← htt]; nlinarith
        rwa [le_div_iff₀ hδpos, one_mul] at h1
      have h2 := two_roots (b := β h) hδpos hqd
      have hsub : {x : ℝ | 0 < δ * x ^ 2 - β h * x - q h} ⊆ {x | Φ (x, h) ∈ S} := by
        intro x hx
        have hx' : 0 < δ * x ^ 2 - β h * x - q h := hx
        rw [mem_ofPred_eq, hmem]
        rw [hδ] at hx'
        nlinarith
      have h3 := measureReal_mono (μ := gaussianReal 0 1) hsub
      rw [← ht] at h2
      linarith
    · -- one tail is at least `Φ̄(1)`
      have hkey : ∀ x : ℝ, t ^ 2 < x ^ 2 → x * β h ≤ 0 → Φ (x, h) ∈ S := by
        intro x hx hxb
        rw [hmem]
        rw [htt, div_lt_iff₀ hδpos] at hx
        rw [hδ] at hx
        nlinarith
      have hone : (gaussianReal 0 1).real (Ioi t) ≤
          (gaussianReal 0 1).real {x | Φ (x, h) ∈ S} := by
        rcases le_or_gt (β h) 0 with hb | hb
        · have hsub : Ioi t ⊆ {x | Φ (x, h) ∈ S} := by
            intro x hx
            have hx' : t < x := hx
            exact hkey x (pow_lt_pow_left₀ hx' htn two_ne_zero)
              (mul_nonpos_of_nonneg_of_nonpos (by linarith) hb)
          exact measureReal_mono (μ := gaussianReal 0 1) hsub
        · have hsub : Iio (-t) ⊆ {x | Φ (x, h) ∈ S} := by
            intro x hx
            have hx' : x < -t := hx
            have h8 : t ^ 2 < (-x) ^ 2 := pow_lt_pow_left₀ (by linarith) htn two_ne_zero
            rw [neg_sq] at h8
            exact hkey x h8 (mul_nonpos_of_nonpos_of_nonneg (by linarith) hb.le)
          exact (tail_neg t).symm.le.trans (measureReal_mono (μ := gaussianReal 0 1) hsub)
      have hsub1 : Ioi (1 : ℝ) ⊆ Ioi t := Ioi_subset_Ioi ht1.le
      have h1t : (gaussianReal 0 1).real (Ioi 1) ≤ (gaussianReal 0 1).real (Ioi t) :=
        measureReal_mono (μ := gaussianReal 0 1) hsub1
      have hqn : 0 ≤ c * (q h / δ) := mul_nonneg hcpos.le (div_nonneg (hq0 h) hδpos.le)
      have e : c * (t0 ^ 2 - q h / δ) = c * t0 ^ 2 - c * (q h / δ) := by ring
      rw [e]
      linarith
  have i1 : Integrable (fun h => q h / δ) (stdGauss ι) := hqint.div_const _
  have i2 : Integrable (fun h => t0 ^ 2 - q h / δ) (stdGauss ι) := (integrable_const _).sub i1
  have i3 : Integrable (fun h => c * (t0 ^ 2 - q h / δ)) (stdGauss ι) := i2.const_mul c
  have hint0 : Integrable (fun h => T1 + c * (t0 ^ 2 - q h / δ)) (stdGauss ι) :=
    (integrable_const _).add i3
  have hint1 : Integrable (fun h => 2 * (T1 + c * (t0 ^ 2 - q h / δ))) (stdGauss ι) :=
    hint0.const_mul 2
  have hint2 : Integrable (fun h => (gaussianReal 0 1).real {x | Φ (x, h) ∈ S}) (stdGauss ι) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_measure_prodMk_right (hΦ hS)).ennreal_toReal.aestronglyMeasurable ?_
    refine ae_of_all _ fun h => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hmono := integral_mono hint1 hint2 hpt
  rw [← hreal] at hmono
  have hI : ∫ h, T1 + c * (t0 ^ 2 - q h / δ) ∂stdGauss ι =
      T1 + c * (t0 ^ 2 - (M.trace - a) / δ) := by
    have e1 : ∫ h, q h / δ ∂stdGauss ι = (M.trace - a) / δ := by rw [integral_div, hEq]
    have e2 : ∫ h, (t0 ^ 2 - q h / δ) ∂stdGauss ι = t0 ^ 2 - (M.trace - a) / δ := by
      rw [integral_sub (integrable_const _) i1, e1]; simp
    have e3 : ∫ h, c * (t0 ^ 2 - q h / δ) ∂stdGauss ι = c * (t0 ^ 2 - (M.trace - a) / δ) := by
      rw [integral_const_mul, e2]
    rw [integral_add (integrable_const _) i3, e3]; simp
  rw [integral_const_mul, hI] at hmono
  exact hmono

end BstLean.Part144

open BstLean.Part144 in
#print axioms mills_upper
open BstLean.Part144 in
#print axioms tail_two_sided
open BstLean.Part144 in
#print axioms gauss_block_tangent2
