import BstLean.Part40Defs
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Part 40, wave 1: the imported results, in the special forms the proof uses

Paper: `proofs/option-m/40-explicit-22-every-diagonal-bingham.tex`, Lemmas `anderson`, `LM`, `pop`.
Specification: `delegations/answers/p40-spec-opus.md`. Mathlib lacks these; prove them here.
Do not use `native_decide` or `axiom` anywhere.

* `anderson_gauss`: the Gaussian case of Anderson's inequality for the symmetric convex set
  `{c : cᵀSc < s}`, `S` positive semidefinite. Suggested route: diagonalise `S` with an orthogonal
  matrix (the standard Gaussian is invariant), then shift one coordinate at a time; each slice is
  an interval centred at `−yᵢ`, and a centred interval has the largest Gaussian mass among intervals
  of its length.
* `chisq_upper`, `chisq_lower`: Laurent–Massart, Lemma 1, unit weights. Suggested route: Chernoff
  with `E e^{λz²} = (1 − 2λ)^{−1/2}` (a Gaussian integral) and
  `−½ log(1 − 2λ) − λ ≤ λ²/(1 − 2λ)`, `−½ log(1 + 2λ) + λ ≤ λ²`.
* `popoviciu`: `Var h ≤ (b − a)²/4` for `a ≤ h ≤ b`; use `Var h ≤ E (h − (a + b)/2)²`.
-/

namespace BstLean.Part40

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss qformι)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma gaussian_laplace_sq (t : ℝ) (ht : 0 ≤ t) :
    (∫ z : ℝ, Real.exp (-t * z ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he : (fun z : ℝ => gaussianPDFReal 0 1 z • Real.exp (-t * z ^ 2)) =
      fun z => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 + t) * z ^ 2) := by
    funext z
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, integral_gaussian]
  have hp := Real.pi_pos
  have ht' : 0 < 1 + 2 * t := by linarith
  have hdiv : Real.pi / (1 / 2 + t) = (2 * Real.pi) / (1 + 2 * t) := by
    field_simp
  rw [hdiv, Real.sqrt_div (by positivity), div_eq_mul_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

omit [DecidableEq ι] in
private lemma stdGauss_laplace_sq (t : ℝ) (ht : 0 ≤ t) :
    (∫ z : ι → ℝ, Real.exp (-t * ∑ i, z i ^ 2) ∂stdGauss ι) =
      Real.exp (-(Fintype.card ι : ℝ) * Real.log (1 + 2 * t) / 2) := by
  have he : (fun z : ι → ℝ => Real.exp (-t * ∑ i, z i ^ 2)) =
      fun z => ∏ i, Real.exp (-t * z i ^ 2) := by
    funext z
    rw [Finset.mul_sum, Real.exp_sum]
  rw [he, stdGauss,
    integral_fintype_prod_eq_prod (fun (_ : ι) (z : ℝ) => Real.exp (-t * z ^ 2))]
  simp only [gaussian_laplace_sq t ht, Finset.prod_const, Finset.card_univ]
  have ht' : 0 < 1 + 2 * t := by linarith
  rw [← Real.exp_log (by positivity : 0 < (Real.sqrt (1 + 2 * t))⁻¹),
    ← Real.exp_nat_mul, Real.log_inv, Real.log_sqrt ht'.le]
  congr 1
  ring

private lemma gaussian_mgf_sq (t : ℝ) (ht : t < 1 / 2) :
    (∫ z : ℝ, Real.exp (t * z ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he : (fun z : ℝ => gaussianPDFReal 0 1 z • Real.exp (t * z ^ 2)) =
      fun z => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * z ^ 2) := by
    funext z
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, integral_gaussian]
  have ht' : 0 < 1 - 2 * t := by linarith
  have hdiv : Real.pi / (1 / 2 - t) = (2 * Real.pi) / (1 - 2 * t) := by
    field_simp
  rw [hdiv, Real.sqrt_div (by positivity), div_eq_mul_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

private lemma gaussian_mgf_sq_integrable (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun z : ℝ => Real.exp (t * z ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero, mul_assoc, ← Real.exp_add]
  have he : (fun z : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-z ^ 2 / 2 + t * z ^ 2)) =
      fun z => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * z ^ 2) := by
    funext z
    congr 2
    ring
  rw [he]
  exact (integrable_exp_neg_mul_sq (by linarith : 0 < 1 / 2 - t)).const_mul _

omit [DecidableEq ι] in
private lemma stdGauss_mgf_sq (t : ℝ) (ht : t < 1 / 2) :
    (∫ z : ι → ℝ, Real.exp (t * ∑ i, z i ^ 2) ∂stdGauss ι) =
      Real.exp (-(Fintype.card ι : ℝ) * Real.log (1 - 2 * t) / 2) := by
  have he : (fun z : ι → ℝ => Real.exp (t * ∑ i, z i ^ 2)) =
      fun z => ∏ i, Real.exp (t * z i ^ 2) := by
    funext z
    rw [Finset.mul_sum, Real.exp_sum]
  rw [he, stdGauss,
    integral_fintype_prod_eq_prod (fun (_ : ι) (z : ℝ) => Real.exp (t * z ^ 2))]
  simp only [gaussian_mgf_sq t ht, Finset.prod_const, Finset.card_univ]
  have ht' : 0 < 1 - 2 * t := by linarith
  rw [← Real.exp_log (by positivity : 0 < (Real.sqrt (1 - 2 * t))⁻¹),
    ← Real.exp_nat_mul, Real.log_inv, Real.log_sqrt ht'.le]
  congr 1
  ring

private lemma gaussian_interval_shift (r y : ℝ) (hr : 0 ≤ r) :
    gaussianReal 0 1 (Set.Ioo (-r - y) (r - y)) ≤
      gaussianReal 0 1 (Set.Ioo (-r) r) := by
  let f := gaussianPDFReal 0 1
  have hf : Continuous f := by
    change Continuous (fun x : ℝ => (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ *
      Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))))
    fun_prop
  let P := fun x : ℝ => ∫ z in (0 : ℝ)..x, f z
  have hP (x : ℝ) : HasDerivAt P (f x) x := by
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  let F := fun z : ℝ => P (r - z) - P (-r - z)
  have hF (z : ℝ) : HasDerivAt F (f (-r - z) - f (r - z)) z := by
    convert ((hP (r - z)).comp z ((hasDerivAt_const z r).sub (hasDerivAt_id z))).sub
      ((hP (-r - z)).comp z ((hasDerivAt_const z (-r)).sub (hasDerivAt_id z))) using 1
    · rfl
    · ring
  have hanti : AntitoneOn F (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun z _ => hF z))
      (fun z _ => (hF z).differentiableAt.differentiableWithinAt)
    intro z hz
    rw [(hF z).deriv]
    have hz0 : 0 ≤ z := (interior_subset hz)
    apply sub_nonpos.mpr
    dsimp [f, gaussianPDFReal]
    simp only [mul_one, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hr hz0]
  have hFI (z : ℝ) : F z = ∫ x in (-r - z)..(r - z), f x := by
    dsimp [F, P]
    have h := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (f := f)
      (hf.intervalIntegrable 0 (-r - z)) (hf.intervalIntegrable (-r - z) (r - z))
    linarith only [h]
  have hfeven (x : ℝ) : f (-x) = f x := by
    simp [f, gaussianPDFReal]
  have hFeven (z : ℝ) : F (-z) = F z := by
    rw [hFI, hFI]
    have he := intervalIntegral.integral_comp_neg (f := f) (a := -r - z) (b := r - z)
    simp only [hfeven] at he
    convert he.symm using 1
    congr 1 <;> ring
  have hbound : F y ≤ F 0 := by
    by_cases hy : 0 ≤ y
    · exact hanti (by simp) hy hy
    · rw [← hFeven y]
      exact hanti (by simp) (by simp; linarith) (by linarith)
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply ENNReal.ofReal_le_ofReal
  rw [hFI y, hFI 0] at hbound
  simpa only [sub_zero, intervalIntegral.integral_of_le (show -r - y ≤ r - y by linarith),
    intervalIntegral.integral_of_le (show -r ≤ r by linarith),
    integral_Ioc_eq_integral_Ioo, f] using hbound

private lemma gaussian_sq_shift (a : ℝ) (ha : 0 ≤ a) (y s : ℝ) :
    gaussianReal 0 1 {z | a * (z + y) ^ 2 < s} ≤
      gaussianReal 0 1 {z | a * z ^ 2 < s} := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  by_cases hs : s ≤ 0
  · have he (v : ℝ) : {z : ℝ | a * (z + v) ^ 2 < s} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt.mpr (hs.trans (mul_nonneg ha (sq_nonneg _)))
    rw [he y]
    simp
  have hsp : 0 < s := lt_of_not_ge hs
  let r := Real.sqrt (s / a)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = s / a := Real.sq_sqrt (by positivity)
  have hars : a * r ^ 2 = s := by rw [hr2]; exact mul_div_cancel₀ s ha0
  have he (v : ℝ) : {z : ℝ | a * (z + v) ^ 2 < s} = Set.Ioo (-r - v) (r - v) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
    have hsq : a * (z + v) ^ 2 < s ↔ (z + v) ^ 2 < r ^ 2 := by
      rw [← hars]
      exact mul_lt_mul_iff_right₀ hap
    rw [hsq, sq_lt_sq, abs_of_nonneg hr, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]
  rw [he y]
  have he0 := he 0
  simp only [add_zero, sub_zero] at he0
  rw [he0]
  exact gaussian_interval_shift r y hr

private lemma gaussian_diagonal_shift_fin (n : ℕ) (a y : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : ℝ) :
    stdGauss (Fin n) {z | ∑ i, a i * (z i + y i) ^ 2 < s} ≤
      stdGauss (Fin n) {z | ∑ i, a i * z i ^ 2 < s} := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    let E := fun (v : Fin (n + 1) → ℝ) =>
      {p : ℝ × (Fin n → ℝ) | a 0 * (p.1 + v 0) ^ 2 +
        ∑ i, a i.succ * (p.2 i + v i.succ) ^ 2 < s}
    have hE (v : Fin (n + 1) → ℝ) : MeasurableSet (E v) := by
      apply measurableSet_lt _ measurable_const
      exact (show Continuous (fun p : ℝ × (Fin n → ℝ) =>
        a 0 * (p.1 + v 0) ^ 2 + ∑ i, a i.succ * (p.2 i + v i.succ) ^ 2) by
          fun_prop).measurable
    have hsplit (v : Fin (n + 1) → ℝ) :
        stdGauss (Fin (n + 1)) {z | ∑ i, a i * (z i + v i) ^ 2 < s} =
          (gaussianReal 0 1).prod (stdGauss (Fin n)) (E v) := by
      have hp := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => gaussianReal 0 1) 0).symm
      unfold stdGauss
      rw [← hp.measure_preimage_emb (MeasurableEquiv.measurableEmbedding _)
        {z | ∑ i, a i * (z i + v i) ^ 2 < s}]
      congr 1
      ext p
      simp [E, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.sum_univ_succ]
    rw [hsplit y]
    have hz : stdGauss (Fin (n + 1)) {z | ∑ i, a i * z i ^ 2 < s} =
        (gaussianReal 0 1).prod (stdGauss (Fin n)) (E 0) := by
      simpa using hsplit 0
    rw [hz]
    let v : Fin (n + 1) → ℝ := Fin.cases 0 (fun i => y i.succ)
    calc
      _ ≤ (gaussianReal 0 1).prod (stdGauss (Fin n)) (E v) := by
        rw [Measure.prod_apply_symm (hE y), Measure.prod_apply_symm (hE v)]
        apply lintegral_mono
        intro z
        have h := gaussian_sq_shift (a 0) (ha 0) (y 0)
          (s - ∑ i, a i.succ * (z i + y i.succ) ^ 2)
        convert h using 1 <;> apply congrArg (gaussianReal 0 1) <;> ext x <;>
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, E, v, Fin.cases_zero,
            Fin.cases_succ, add_zero] <;> constructor <;> intro h <;> linarith only [h]
      _ ≤ (gaussianReal 0 1).prod (stdGauss (Fin n)) (E 0) := by
        rw [Measure.prod_apply (hE v), Measure.prod_apply (hE 0)]
        apply lintegral_mono
        intro x
        have h := ih (fun i => a i.succ) (fun i => y i.succ)
          (fun i => ha i.succ) (s - a 0 * x ^ 2)
        convert h using 1 <;> apply congrArg (stdGauss (Fin n)) <;> ext z <;>
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, E, v, Fin.cases_zero,
            Fin.cases_succ, Pi.zero_apply, add_zero] <;>
          constructor <;> intro h <;> linarith only [h]

omit [DecidableEq ι] in
private lemma gaussian_basis_preserving {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ ι)) :
    MeasurePreserving (fun z : ι → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 z)))
      (stdGauss ι) (stdGauss κ) := by
  have hι : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ))
      (stdGauss ι) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨(MeasurableEquiv.toLp 2 (ι → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hb : MeasurePreserving b.repr (stdGaussian (EuclideanSpace ℝ ι))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨b.repr.continuous.measurable, stdGaussian_map b.repr⟩
  have hκ : MeasurePreserving (MeasurableEquiv.toLp 2 (κ → ℝ))
      (stdGauss κ) (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨(MeasurableEquiv.toLp 2 (κ → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  exact hκ.symm.comp (hb.comp hι)

private lemma qform_inner (S : Matrix ι ι ℝ) (c : ι → ℝ) :
    qformι S c = inner ℝ (WithLp.toLp 2 c) (S.toEuclideanLin (WithLp.toLp 2 c)) := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct, Matrix.mulVec,
    qformι, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma qform_eigenbasis (S : Matrix ι ι ℝ) (hT : S.toEuclideanLin.IsSymmetric)
    (c : ι → ℝ) :
    qformι S c = ∑ i, hT.eigenvalues finrank_euclideanSpace i *
      ((hT.eigenvectorBasis finrank_euclideanSpace).repr (WithLp.toLp 2 c) i) ^ 2 := by
  rw [qform_inner, ← (hT.eigenvectorBasis finrank_euclideanSpace).repr.inner_map_map]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [hT.eigenvectorBasis_apply_self_apply finrank_euclideanSpace]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

/-- **Anderson's inequality** (Gaussian, `PSD` quadratic sublevel set). -/
theorem anderson_gauss (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hpos : ∀ c, 0 ≤ qformι S c)
    (y : ι → ℝ) (s : ℝ) :
    stdGauss ι {c | qformι S (c + y) < s} ≤ stdGauss ι {c | qformι S c < s} := by
  classical
  have hH : S.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hS
  have hT : S.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  let a := hT.eigenvalues finrank_euclideanSpace
  let r := fun c : ι → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 c))
  have hq (c : ι → ℝ) : qformι S c = ∑ i, a i * (r c i) ^ 2 :=
    qform_eigenbasis S hT c
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    have h := hpos (WithLp.ofLp (b i))
    rw [hq] at h
    simpa [r, b.repr_self, PiLp.single_apply] using h
  have hp : MeasurePreserving r (stdGauss ι) (stdGauss (Fin (Fintype.card ι))) :=
    gaussian_basis_preserving b
  have hadd (c : ι → ℝ) : r (c + y) = r c + r y := by
    dsimp [r]
    rw [map_add, WithLp.ofLp_add]
  have hmeas (v : Fin (Fintype.card ι) → ℝ) :
      MeasurableSet {z : Fin (Fintype.card ι) → ℝ | ∑ i, a i * (z i + v i) ^ 2 < s} := by
    apply measurableSet_lt _ measurable_const
    exact (show Continuous (fun z : Fin (Fintype.card ι) → ℝ =>
      ∑ i, a i * (z i + v i) ^ 2) by fun_prop).measurable
  have hshift : {c : ι → ℝ | qformι S (c + y) < s} =
      r ⁻¹' {z | ∑ i, a i * (z i + r y i) ^ 2 < s} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hq, hadd, Pi.add_apply]
  have hzero : {c : ι → ℝ | qformι S c < s} =
      r ⁻¹' {z | ∑ i, a i * (z i + (0 : Fin (Fintype.card ι) → ℝ) i) ^ 2 < s} := by
    ext c
    simp [hq]
  rw [hshift, hzero, hp.measure_preimage (hmeas (r y)).nullMeasurableSet,
    hp.measure_preimage (hmeas 0).nullMeasurableSet]
  simpa using gaussian_diagonal_shift_fin (Fintype.card ι) a (r y) ha s

/-- **Laurent–Massart, upper tail**: `Pr{χ²_d − d ≥ 2√(dx) + 2x} ≤ e^{−x}`. -/
theorem chisq_upper (hι : 0 < Fintype.card ι) (x : ℝ) (hx : 0 < x) :
    stdGauss ι {z | 2 * Real.sqrt ((Fintype.card ι : ℝ) * x) + 2 * x ≤
      ∑ i, z i ^ 2 - (Fintype.card ι : ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by dsimp [d]; exact_mod_cast hι
  let u := Real.sqrt (x / d)
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos hx hd)
  have hu2 : u ^ 2 = x / d := Real.sq_sqrt (by positivity)
  have hux : d * u ^ 2 = x := by rw [hu2]; field_simp
  have hs : Real.sqrt (d * x) = d * u := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (mul_nonneg hd.le hu.le)).mpr
    calc
      d * x = d * (d * u ^ 2) := by rw [hux]
      _ = (d * u) ^ 2 := by ring
  let q := 1 + 2 * u + 2 * u ^ 2
  have hq : 1 < q := by dsimp [q]; nlinarith only [hu, sq_nonneg u]
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hlog : Real.log q ≤ 2 * u := by
    rw [Real.log_le_iff_le_exp hq0]
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * u by positivity)
    dsimp [q]
    nlinarith only [h]
  let t := (1 - q⁻¹) / 2
  have ht : 0 ≤ t := by
    dsimp [t]
    have hiq := (inv_le_one₀ hq0).mpr hq.le
    linarith only [hiq]
  have ht' : t < 1 / 2 := by
    dsimp [t]
    have hiq := inv_pos.mpr hq0
    linarith only [hiq]
  have hident : 1 - 2 * t = q⁻¹ := by dsimp [t]; ring
  have hi : Integrable (fun z : ι → ℝ => Real.exp (t * ∑ i, z i ^ 2)) (stdGauss ι) := by
    have he : (fun z : ι → ℝ => Real.exp (t * ∑ i, z i ^ 2)) =
        fun z => ∏ i, Real.exp (t * z i ^ 2) := by
      funext z
      rw [Finset.mul_sum, Real.exp_sum]
    rw [he, stdGauss]
    exact Integrable.fintype_prod (fun _ => gaussian_mgf_sq_integrable t ht')
  have hc := measure_ge_le_exp_mul_mgf (μ := stdGauss ι)
    (X := fun z : ι → ℝ => ∑ i, z i ^ 2) (d * q) ht hi
  rw [mgf, stdGauss_mgf_sq t ht', ← Real.exp_add, hident, Real.log_inv] at hc
  have he : -t * (d * q) + -(Fintype.card ι : ℝ) * -Real.log q / 2 ≤ -x := by
    change -t * (d * q) + -d * -Real.log q / 2 ≤ -x
    have halg : -t * (d * q) = -d * (q - 1) / 2 := by
      dsimp [t]
      field_simp [ne_of_gt hq0]
    rw [halg]
    have hmul := mul_le_mul_of_nonneg_left hlog hd.le
    dsimp [q] at hmul ⊢
    nlinarith only [hmul, hux]
  have hset : {z : ι → ℝ | 2 * Real.sqrt ((Fintype.card ι : ℝ) * x) + 2 * x ≤
      ∑ i, z i ^ 2 - (Fintype.card ι : ℝ)} =
      {z : ι → ℝ | d * q ≤ ∑ i, z i ^ 2} := by
    ext z
    change (2 * Real.sqrt (d * x) + 2 * x ≤ ∑ i, z i ^ 2 - d) ↔
      (d * q ≤ ∑ i, z i ^ 2)
    rw [hs]
    dsimp [q]
    constructor <;> intro h <;> nlinarith only [h, hux]
  rw [hset]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact hc.trans (Real.exp_le_exp.mpr he)

/-- **Laurent–Massart, lower tail**: `Pr{d − χ²_d ≥ 2√(dx)} ≤ e^{−x}`. -/
theorem chisq_lower (hι : 0 < Fintype.card ι) (x : ℝ) (hx : 0 < x) :
    stdGauss ι {z | 2 * Real.sqrt ((Fintype.card ι : ℝ) * x) ≤
      (Fintype.card ι : ℝ) - ∑ i, z i ^ 2} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by dsimp [d]; exact_mod_cast hι
  let t := Real.sqrt (x / d)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = x / d := Real.sq_sqrt (by positivity)
  have htx : d * t ^ 2 = x := by rw [ht2]; field_simp
  have hs : Real.sqrt (d * x) = d * t := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (mul_nonneg hd.le ht)).mpr
    calc
      d * x = d * (d * t ^ 2) := by rw [htx]
      _ = (d * t) ^ 2 := by ring
  have hlog : 2 * t - 2 * t ^ 2 ≤ Real.log (1 + 2 * t) := by
    have hl := Real.le_log_one_add_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht)
    have hden : 0 < 2 * t + 2 := by positivity
    have hr : 2 * t - 2 * t ^ 2 ≤ 2 * (2 * t) / (2 * t + 2) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [mul_nonneg ht (sq_nonneg t)]
    exact hr.trans hl
  have hi : Integrable (fun z : ι → ℝ => Real.exp (-t * ∑ i, z i ^ 2)) (stdGauss ι) := by
    refine (integrable_const (1 : ℝ)).mono'
      (show Continuous (fun z : ι → ℝ => Real.exp (-t * ∑ i, z i ^ 2)) by
        fun_prop).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht)
      (Finset.sum_nonneg fun i _ => sq_nonneg (z i))
  have hc := measure_le_le_exp_mul_mgf (μ := stdGauss ι)
    (X := fun z : ι → ℝ => ∑ i, z i ^ 2)
    (d - 2 * Real.sqrt (d * x)) (neg_nonpos.mpr ht) hi
  rw [mgf, stdGauss_laplace_sq t ht, ← Real.exp_add] at hc
  have he : -(-t) * (d - 2 * Real.sqrt (d * x)) +
      -(Fintype.card ι : ℝ) * Real.log (1 + 2 * t) / 2 ≤ -x := by
    change -(-t) * (d - 2 * Real.sqrt (d * x)) +
      -d * Real.log (1 + 2 * t) / 2 ≤ -x
    rw [hs]
    nlinarith only [htx, mul_le_mul_of_nonneg_left hlog hd.le]
  have hset : {z : ι → ℝ | 2 * Real.sqrt ((Fintype.card ι : ℝ) * x) ≤
      (Fintype.card ι : ℝ) - ∑ i, z i ^ 2} =
      {z : ι → ℝ | ∑ i, z i ^ 2 ≤ d - 2 * Real.sqrt (d * x)} := by
    ext z
    change (2 * Real.sqrt (d * x) ≤ d - ∑ i, z i ^ 2) ↔
      (∑ i, z i ^ 2 ≤ d - 2 * Real.sqrt (d * x))
    constructor <;> intro h <;> linarith only [h]
  rw [hset]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact hc.trans (Real.exp_le_exp.mpr he)

/-- **Popoviciu's inequality**. -/
theorem popoviciu {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → ℝ) (hh : AEMeasurable h μ) (a b : ℝ) (hab : ∀ᵐ x ∂μ, a ≤ h x ∧ h x ≤ b) :
    ∫ x, (h x - ∫ y, h y ∂μ) ^ 2 ∂μ ≤ (b - a) ^ 2 / 4 := by
  rw [← variance_eq_integral hh]
  calc
    variance h μ ≤ ((b - a) / 2) ^ 2 := variance_le_sq_of_bounded hab hh
    _ = (b - a) ^ 2 / 4 := by ring

#print axioms anderson_gauss
#print axioms chisq_upper
#print axioms chisq_lower
#print axioms popoviciu

end BstLean.Part40
