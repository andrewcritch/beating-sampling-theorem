import BstLean.Part149CDefs
import BstLean.Part149KK
import BstLean.Part149Mean
import BstLean.Part140Norm

/-!
# Part 149, item 5, helper `Centre`: the mean-field centre against the exact centre

Role: `delegations/statements/p149-spec.md`.

Do not use `sorry`, `native_decide` or `axiom`.

* `Kq = 93/200`, `kappa_quad_34`: `κ(s) ≤ κ(u) + kg(u)(s − u) + Kq·(s − u)²` for `0 ≤ u ≤ 3/4`
  and all `s ∈ [−1, 1]`.
* `gE μ a s b M = |ψ_s(M b) − E_u ReLU(M a(u))|²` for a bounded measurable family of vectors
  `a(u)`; `gE_mean`: the mean of `gE` over a Gaussian matrix `M` (three kernel terms).
* `gap_bound`: with `b = E a`, `N₂ = E|a|²`, `s² = v(N₂ − |b|²)`, `v = 2/m`, `|b|² ≤ (3/4)N₂`:
  `E_M gE ≤ (N₂ − (E|a|)²) + Kq·(Q/p₀ + 8·p₀·P(|a|² < p₀))`,
  `Q = E_{u,u'}(⟨a, a'⟩ − (|b|²/N₂)|a||a'|)²`.
* **`centreDist_cond`**: the same for the first hidden layer of `A` at the stand-in inputs: the
  mean over `A₂` of `eC = |bMF − b̄|²`, for fixed `c`, `τ`, `A₁`.
* `measurable_b1`, `measurable_N2`, `measurable_sMF`, `measurable_bMF`, `measurable_eC`: joint
  measurability.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part137 (psiS measurable_psiS smooth_layer cS normSq_cons dotp_cons)
open BstLean.Part140 (sq_layer cQ hP1 hP2 normSq_hP1 normSq_hP2 dotp_hP dotp_self)
open BstLean.Part145 (kg kappa_tangent_ge)

/-! ## A second-order upper bound of `κ` at a point of `[0, 3/4]` -/

/-- The constant of the second-order upper bound of `κ` at a point of `[0, 3/4]`. -/
noncomputable def Kq : ℝ := 93 / 200

lemma Kq_pos : 0 < Kq := by unfold Kq; norm_num

lemma arcsin_secant_one34 {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 3 / 4) :
    (Real.arcsin 1 - Real.arcsin u) / (1 - u) ≤ 93 / 100 * π := by
  have hp := Real.pi_pos
  have h34 : (Real.arcsin 1 - Real.arcsin (3 / 4)) / (1 - 3 / 4) ≤ 93 / 100 * π := by
    have h2 := arcsin_ge_poly7 (t := 3 / 4) (by norm_num) (by norm_num)
    have h4 := Real.pi_lt_d4
    rw [Real.arcsin_one, div_le_iff₀ (by norm_num)]
    norm_num at h2 ⊢
    linarith
  rcases eq_or_lt_of_le hu with h | h
  · rw [h]
    exact h34
  have hs := arcsin_convexOn.secant_mono (a := 1) (x := u) (y := 3 / 4)
    (right_mem_Icc.mpr zero_le_one) ⟨hu0, by linarith⟩ ⟨by norm_num, by norm_num⟩
    (by linarith : u < 1).ne (by norm_num) hu
  have e : ∀ x : ℝ, (Real.arcsin x - Real.arcsin 1) / (x - 1) =
      (Real.arcsin 1 - Real.arcsin x) / (1 - x) := fun x => by
    rw [← neg_sub (Real.arcsin 1), ← neg_sub (1 : ℝ) x, neg_div_neg_eq]
  rw [e, e] at hs
  exact hs.trans h34

/-- Slopes of `arcsin` from `u ∈ [0, 3/4]` to the right. -/
lemma arcsin_slope_up34 {u s : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 3 / 4) (hus : u < s) (hs : s ≤ 1) :
    Real.arcsin s - Real.arcsin u ≤ 93 / 100 * π * (s - u) := by
  have hmem : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, by linarith⟩
  have hne1 : (1 : ℝ) ≠ u := by intro h; linarith
  have h := arcsin_convexOn.secant_mono hmem ⟨by linarith, hs⟩ (right_mem_Icc.mpr zero_le_one)
    hus.ne' hne1 hs
  have h2 := h.trans (arcsin_secant_one34 hu0 hu)
  rwa [div_le_iff₀ (by linarith)] at h2

/-- Slopes of `arcsin` from `u ∈ [0, 3/4]` to the left. -/
lemma arcsin_slope_down34 {u s : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 3 / 4) (hs : -1 ≤ s) (hsu : s < u) :
    Real.arcsin u - Real.arcsin s ≤ 93 / 100 * π * (u - s) := by
  have hp := Real.pi_pos
  rcases le_total 0 s with h0 | h0
  · have hmem : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, by linarith⟩
    have hne1 : (1 : ℝ) ≠ u := by intro h; linarith
    have h := arcsin_convexOn.secant_mono hmem ⟨h0, by linarith⟩
      (right_mem_Icc.mpr zero_le_one) hsu.ne hne1 (by linarith)
    have h2 := h.trans (arcsin_secant_one34 hu0 hu)
    rw [div_le_iff_of_neg (by linarith)] at h2
    linarith
  · have ha := arcsin_le_half_pi_mul hu0 (by linarith : u ≤ 1)
    have hb := arcsin_le_half_pi_mul (t := -s) (by linarith) (by linarith)
    rw [Real.arcsin_neg] at hb
    have hm : 0 ≤ π * (u - s) := mul_nonneg hp.le (by linarith)
    nlinarith

/-- **A second-order upper bound of `κ` at a point `u ∈ [0, 3/4]`, on all of `[−1, 1]`.** -/
theorem kappa_quad_34 {u s : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 3 / 4) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    kappa s ≤ kappa u + kg u * (s - u) + Kq * (s - u) ^ 2 := by
  have hp := Real.pi_pos
  unfold Kq
  have h := ge_of_deriv_sign
    (f := fun x : ℝ => (kappa u + kg u * (x - u) + 93 / 200 * (x - u) ^ 2) - kappa x)
    (f' := fun x : ℝ => (kg u + 2 * (93 / 200) * (x - u)) - (π - Real.arccos x) / π)
    (a := -1) (b := 1) (c := u)
    (by have := continuous_kappa; fun_prop)
    (fun x hx => (hasDerivAt_quadQ _ _ _ _ x).sub (hasDerivAt_kappa hx.1 hx.2))
    (by linarith) (by linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq, kg_eq]
      have ha := arcsin_slope_up34 hu0 hu hx.1 hx.2.le
      have hb : (Real.arcsin x - Real.arcsin u) / π ≤ 93 / 100 * (x - u) := by
        rw [div_le_iff₀ hp]; linarith
      rw [sub_div] at hb
      linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq, kg_eq]
      have ha := arcsin_slope_down34 hu0 hu hx.1.le hx.2
      have hb : (Real.arcsin u - Real.arcsin x) / π ≤ 93 / 100 * (u - x) := by
        rw [div_le_iff₀ hp]; linarith
      rw [sub_div] at hb
      linarith)
    s hs
  beta_reduce at h
  nlinarith

/-- The perspective form of `kappa_quad_34`, with the denominator cut at `plo`. -/
lemma persp_quad_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 3 / 4) {p c plo : ℝ} (hp : 0 ≤ p)
    (hc : |c| ≤ p) (hplo : 0 < plo) :
    persp kappa p c ≤ (kappa u - kg u * u) * p + kg u * c +
      Kq * ((c - u * p) ^ 2 / plo + 4 * plo * (if p < plo then 1 else 0)) := by
  have hK := Kq_pos
  rcases eq_or_lt_of_le hp with h | h
  · subst h
    have hc0 : c = 0 := abs_nonpos_iff.mp hc
    subst hc0
    have e1 : (if (0 : ℝ) < plo then (1 : ℝ) else 0) = 1 := by simp [hplo]
    simp only [persp, zero_mul, mul_zero, add_zero, sub_zero]
    rw [e1]
    have : (0 : ℝ) ≤ (0 : ℝ) ^ 2 / plo := by positivity
    nlinarith
  · have hs := div_mem_Icc hp hc
    have hq := kappa_quad_34 hu0 hu hs
    have hmul := mul_le_mul_of_nonneg_left hq hp
    have e1 : p * (kappa u + kg u * (c / p - u) + Kq * (c / p - u) ^ 2) =
        (kappa u - kg u * u) * p + kg u * c + Kq * ((c - u * p) ^ 2 / p) := by
      field_simp
      ring
    rw [e1] at hmul
    have hcc := abs_le.mp hc
    have hup : 0 ≤ u * p := mul_nonneg hu0 hp
    have hup' : u * p ≤ p := by nlinarith
    have hrem : (c - u * p) ^ 2 / p ≤
        (c - u * p) ^ 2 / plo + 4 * plo * (if p < plo then 1 else 0) := by
      by_cases hpl : p < plo
      · have e1 : (if p < plo then (1 : ℝ) else 0) = 1 := by simp [hpl]
        rw [e1]
        have h1 : (c - u * p) ^ 2 / p ≤ 4 * p := by
          rw [div_le_iff₀ h]
          nlinarith
        have h2 : (0 : ℝ) ≤ (c - u * p) ^ 2 / plo := by positivity
        linarith
      · have e1 : (if p < plo then (1 : ℝ) else 0) = 0 := by simp [hpl]
        rw [e1]
        have h1 : (c - u * p) ^ 2 / p ≤ (c - u * p) ^ 2 / plo :=
          div_le_div_of_nonneg_left (sq_nonneg _) hplo (not_lt.mp hpl)
        linarith
    have := mul_le_mul_of_nonneg_left hrem hK.le
    unfold persp
    linarith

/-! ## Linearity helpers -/

section lin

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integral_lin2 {f1 f2 : α → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (c1 c2 : ℝ) :
    Integrable (fun x => c1 * f1 x + c2 * f2 x) μ ∧
    ∫ x, (c1 * f1 x + c2 * f2 x) ∂μ = c1 * ∫ x, f1 x ∂μ + c2 * ∫ x, f2 x ∂μ := by
  refine ⟨(h1.const_mul c1).add (h2.const_mul c2), ?_⟩
  rw [integral_add (h1.const_mul c1) (h2.const_mul c2), integral_const_mul, integral_const_mul]

lemma integral_lin5 {f1 f2 f3 f4 f5 : α → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (c1 c2 c3 c4 c5 : ℝ) :
    Integrable (fun x => c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x + c5 * f5 x) μ ∧
    ∫ x, (c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x + c5 * f5 x) ∂μ =
      c1 * ∫ x, f1 x ∂μ + c2 * ∫ x, f2 x ∂μ + c3 * ∫ x, f3 x ∂μ + c4 * ∫ x, f4 x ∂μ +
        c5 * ∫ x, f5 x ∂μ := by
  have i12 : Integrable (fun x => c1 * f1 x + c2 * f2 x) μ :=
    (h1.const_mul c1).add (h2.const_mul c2)
  have i123 : Integrable (fun x => c1 * f1 x + c2 * f2 x + c3 * f3 x) μ :=
    i12.add (h3.const_mul c3)
  have i1234 : Integrable (fun x => c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x) μ :=
    i123.add (h4.const_mul c4)
  refine ⟨i1234.add (h5.const_mul c5), ?_⟩
  have e4 : ∫ x, (c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x + c5 * f5 x) ∂μ =
      ∫ x, (c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x) ∂μ + ∫ x, c5 * f5 x ∂μ :=
    integral_add i1234 (h5.const_mul c5)
  have e3 : ∫ x, (c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x) ∂μ =
      ∫ x, (c1 * f1 x + c2 * f2 x + c3 * f3 x) ∂μ + ∫ x, c4 * f4 x ∂μ :=
    integral_add i123 (h4.const_mul c4)
  have e2 : ∫ x, (c1 * f1 x + c2 * f2 x + c3 * f3 x) ∂μ =
      ∫ x, (c1 * f1 x + c2 * f2 x) ∂μ + ∫ x, c3 * f3 x ∂μ :=
    integral_add i12 (h3.const_mul c3)
  have e1 : ∫ x, (c1 * f1 x + c2 * f2 x) ∂μ = ∫ x, c1 * f1 x ∂μ + ∫ x, c2 * f2 x ∂μ :=
    integral_add (h1.const_mul c1) (h2.const_mul c2)
  rw [e4, e3, e2, e1]
  simp only [integral_const_mul]

lemma integral_lin3 {f1 f2 f3 : α → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) :
    Integrable (fun x => f1 x - 2 * f2 x + f3 x) μ ∧
    ∫ x, (f1 x - 2 * f2 x + f3 x) ∂μ = ∫ x, f1 x ∂μ - 2 * ∫ x, f2 x ∂μ + ∫ x, f3 x ∂μ := by
  have i12 : Integrable (fun x => f1 x - 2 * f2 x) μ := h1.sub (h2.const_mul 2)
  refine ⟨i12.add h3, ?_⟩
  have e2 : ∫ x, (f1 x - 2 * f2 x + f3 x) ∂μ = ∫ x, (f1 x - 2 * f2 x) ∂μ + ∫ x, f3 x ∂μ :=
    integral_add i12 h3
  have e1 : ∫ x, (f1 x - 2 * f2 x) ∂μ = ∫ x, f1 x ∂μ - ∫ x, 2 * f2 x ∂μ :=
    integral_sub h1 (h2.const_mul 2)
  rw [e2, e1, integral_const_mul]

lemma integrable_of_abs_le [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

end lin

/-! ## A Gaussian layer against a bounded family of vectors -/

section gen

variable {U : Type*} [MeasurableSpace U] {m k : ℕ}

lemma measurable_mulVec_joint :
    Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) => p.1.mulVec p.2) :=
  (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable

lemma measurable_mulVec_left (M : Matrix (Fin m) (Fin k) ℝ) :
    Measurable (fun x : Fin k → ℝ => M.mulVec x) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).measurable

lemma normSq_sub {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    normSq (x - y) = normSq x - 2 * dotp x y + normSq y := by
  unfold normSq dotp
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.sub_apply]
    ring

lemma abs_relu_mulVec_le (M : Matrix (Fin m) (Fin k) ℝ) (i : Fin m) (x : Fin k → ℝ) :
    |relu ((M.mulVec x) i)| ≤ normSq (rowOf i M) + normSq x := by
  have e : (M.mulVec x) i = dotp (rowOf i M) x := rfl
  rw [e]
  exact (abs_relu_le _).trans (abs_dotp_le _ _)

/-- The smoothed vector `ψ_s(M b)`. -/
noncomputable def psV (s : ℝ) (b : Fin k → ℝ) (M : Matrix (Fin m) (Fin k) ℝ) : Fin m → ℝ :=
  fun i => psiS s ((M.mulVec b) i)

lemma measurable_psV (s : ℝ) (b : Fin k → ℝ) :
    Measurable (psV (m := m) s b) :=
  measurable_pi_iff.mpr fun i => measurable_psiS.comp
    (measurable_const.prodMk ((measurable_pi_apply i).comp (measurable_mulVec_right b)))

/-- The squared distance of the smoothed vector `ψ_s(M b)` to the mean of `ReLU(M a(u))`. -/
noncomputable def gE (μ : Measure U) (a : U → Fin k → ℝ) (s : ℝ) (b : Fin k → ℝ)
    (M : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  normSq (psV s b M - hbar μ (fun u => reluV (M.mulVec (a u))))

variable (μ : Measure U) [IsProbabilityMeasure μ]

lemma integrable_relu_coord {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ u, normSq (a u) ≤ H) (M : Matrix (Fin m) (Fin k) ℝ) (i : Fin m) :
    Integrable (fun u => relu ((M.mulVec (a u)) i)) μ :=
  integrable_of_abs_le
    (measurable_relu.comp ((measurable_pi_apply i).comp ((measurable_mulVec_left M).comp ham)))
    (B := normSq (rowOf i M) + H)
    fun u => (abs_relu_mulVec_le M i (a u)).trans (by linarith [hH u])

/-- `|ReLU(M h(u))|²` is integrable on the product. -/
lemma reluSq_prod_integrable {v : ℝ} (hv : 0 ≤ v) {h : U → Fin k → ℝ} (hm : Measurable h)
    {H : ℝ} (hH : ∀ u, normSq (h u) ≤ H) :
    Integrable (fun p : U × Matrix (Fin m) (Fin k) ℝ => normSq (reluV (p.2.mulVec (h p.1))))
      (μ.prod (gaussMat m k v)) := by
  have mf : Measurable (fun p : U × Matrix (Fin m) (Fin k) ℝ =>
      normSq (reluV (p.2.mulVec (h p.1)))) :=
    continuous_normSq.measurable.comp (measurable_reluV.comp
      (measurable_mulVec_joint.comp (measurable_snd.prodMk (hm.comp measurable_fst))))
  refine (prod_step mf (fun _ => normSq_nonneg _) (fun u => (m : ℝ) / 2 * (v * normSq (h u)))
    (fun u => layer_relu_sq hv (h u)) ?_).1
  refine integrable_of_abs_le
    (((continuous_normSq.measurable.comp hm).const_mul v).const_mul _)
    (B := (m : ℝ) / 2 * (v * H)) fun u => ?_
  have h0 := normSq_nonneg (h u)
  rw [abs_of_nonneg (by positivity)]
  have := hH u
  gcongr

/-- The joint integrability of the cross term. -/
lemma cross_integrable {v : ℝ} (hv : 0 < v) (s : ℝ) (b : Fin k → ℝ) {a : U → Fin k → ℝ}
    (ham : Measurable a) {H : ℝ} (hH : ∀ u, normSq (a u) ≤ H) :
    Integrable (fun p : U × Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (p.2.mulVec (a p.1))) (psV s b p.2)) (μ.prod (gaussMat m k v)) := by
  have i1 := reluSq_prod_integrable (m := m) μ hv.le ham hH
  have i2 : Integrable (fun p : U × Matrix (Fin m) (Fin k) ℝ => normSq (psV s b p.2))
      (μ.prod (gaussMat m k v)) := (sq_layer (m := m) hv s b).1.comp_snd μ
  have mf : Measurable (fun p : U × Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (p.2.mulVec (a p.1))) (psV s b p.2)) :=
    continuous_dotp.measurable.comp ((measurable_reluV.comp
      (measurable_mulVec_joint.comp (measurable_snd.prodMk (ham.comp measurable_fst)))).prodMk
      ((measurable_psV s b).comp measurable_snd))
  exact Integrable.mono' (i1.add i2) mf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => abs_dotp_le _ _)

/-- **The mean of the cross term.** -/
lemma cross_mean {v : ℝ} (hv : 0 < v) (s : ℝ) (b : Fin k → ℝ) {a : U → Fin k → ℝ}
    (ham : Measurable a) {H : ℝ} (hH : ∀ u, normSq (a u) ≤ H) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (psV s b M) (hbar μ (fun u => reluV (M.mulVec (a u))))) (gaussMat m k v) ∧
    Integrable (fun u => (m : ℝ) * cS v s (a u) b) μ ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, dotp (psV s b M) (hbar μ (fun u => reluV (M.mulVec (a u))))
      ∂gaussMat m k v = ∫ u, (m : ℝ) * cS v s (a u) b ∂μ := by
  have iF := cross_integrable (m := m) μ hv s b ham hH
  have iU : Integrable (fun u => ∫ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec (a u))) (psV s b M) ∂gaussMat m k v) μ := iF.integral_prod_left
  have eU : (fun u => ∫ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec (a u))) (psV s b M) ∂gaussMat m k v) =
      fun u => (m : ℝ) * cS v s (a u) b :=
    funext fun u => (smooth_layer (m := m) hv s (a u) b).2.1
  rw [eU] at iU
  have hpt : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (psV s b M) (hbar μ (fun u => reluV (M.mulVec (a u)))) =
        ∫ u, dotp (reluV (M.mulVec (a u))) (psV s b M) ∂μ := by
    intro M
    have h1 : ∫ u, dotp (reluV (M.mulVec (a u))) (psV s b M) ∂μ =
        ∑ i, ∫ u, relu ((M.mulVec (a u)) i) * psV s b M i ∂μ :=
      integral_finsetSum _ fun i _ => (integrable_relu_coord μ ham hH M i).mul_const _
    rw [h1]
    unfold dotp
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, mul_comm]
    rfl
  have e : (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (psV s b M) (hbar μ (fun u => reluV (M.mulVec (a u))))) =
      fun M => ∫ u, dotp (reluV (M.mulVec (a u))) (psV s b M) ∂μ := funext hpt
  rw [e]
  refine ⟨iF.integral_prod_right, iU, ?_⟩
  have hsw := integral_integral_swap
    (f := fun (u : U) (M : Matrix (Fin m) (Fin k) ℝ) =>
      dotp (reluV (M.mulVec (a u))) (psV s b M)) iF
  rw [← hsw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact (smooth_layer (m := m) hv s (a u) b).2.1

/-- **The mean of the squared length of the mean of `ReLU(M a(u))`.** -/
lemma sq_mean {v : ℝ} (hv : 0 ≤ v) {a : U → Fin k → ℝ}
    (ham : Measurable a) {H : ℝ} (hH : ∀ u, normSq (a u) ≤ H) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (hbar μ (fun u => reluV (M.mulVec (a u))))) (gaussMat m k v) ∧
    Integrable (fun p : U × U => (m : ℝ) / 2 * (v * kernelPhi (a p.1) (a p.2))) (μ.prod μ) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, normSq (hbar μ (fun u => reluV (M.mulVec (a u))))
      ∂gaussMat m k v =
      ∫ p, (m : ℝ) / 2 * (v * kernelPhi (a p.1) (a p.2)) ∂(μ.prod μ) := by
  have i1 := reluSq_prod_integrable (m := m) (μ.prod μ) hv (h := fun p : U × U => a p.1)
    (ham.comp measurable_fst) (fun p => hH p.1)
  have i2 := reluSq_prod_integrable (m := m) (μ.prod μ) hv (h := fun p : U × U => a p.2)
    (ham.comp measurable_snd) (fun p => hH p.2)
  have mf : Measurable (fun q : (U × U) × Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (q.2.mulVec (a q.1.1))) (reluV (q.2.mulVec (a q.1.2)))) :=
    continuous_dotp.measurable.comp ((measurable_reluV.comp
      (measurable_mulVec_joint.comp (measurable_snd.prodMk
        (ham.comp (measurable_fst.comp measurable_fst))))).prodMk
      (measurable_reluV.comp (measurable_mulVec_joint.comp (measurable_snd.prodMk
        (ham.comp (measurable_snd.comp measurable_fst))))))
  have iF : Integrable (fun q : (U × U) × Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (q.2.mulVec (a q.1.1))) (reluV (q.2.mulVec (a q.1.2))))
      ((μ.prod μ).prod (gaussMat m k v)) :=
    Integrable.mono' (i1.add i2) mf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => abs_dotp_le _ _)
  have hpt : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      normSq (hbar μ (fun u => reluV (M.mulVec (a u)))) =
        ∫ p, dotp (reluV (M.mulVec (a p.1))) (reluV (M.mulVec (a p.2))) ∂(μ.prod μ) := by
    intro M
    have h1 : ∫ p, dotp (reluV (M.mulVec (a p.1))) (reluV (M.mulVec (a p.2))) ∂(μ.prod μ) =
        ∑ i, ∫ p : U × U, relu ((M.mulVec (a p.1)) i) * relu ((M.mulVec (a p.2)) i)
          ∂(μ.prod μ) :=
      integral_finsetSum _ fun i _ => (integrable_relu_coord μ ham hH M i).mul_prod
        (integrable_relu_coord μ ham hH M i)
    rw [h1]
    unfold normSq
    refine Finset.sum_congr rfl fun i _ => ?_
    have := integral_prod_mul (μ := μ) (ν := μ) (fun u => relu ((M.mulVec (a u)) i))
      (fun u => relu ((M.mulVec (a u)) i))
    rw [sq]
    exact this.symm
  have e : (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (hbar μ (fun u => reluV (M.mulVec (a u))))) =
      fun M => ∫ p, dotp (reluV (M.mulVec (a p.1))) (reluV (M.mulVec (a p.2))) ∂(μ.prod μ) :=
    funext hpt
  rw [e]
  have iU : Integrable (fun p : U × U => ∫ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec (a p.1))) (reluV (M.mulVec (a p.2))) ∂gaussMat m k v)
      (μ.prod μ) := iF.integral_prod_left
  have eU : (fun p : U × U => ∫ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec (a p.1))) (reluV (M.mulVec (a p.2))) ∂gaussMat m k v) =
      fun p => (m : ℝ) / 2 * (v * kernelPhi (a p.1) (a p.2)) :=
    funext fun p => (layer_dot_relu (m := m) hv (a p.1) (a p.2)).2
  rw [eU] at iU
  refine ⟨iF.integral_prod_right, iU, ?_⟩
  have hsw := integral_integral_swap
    (f := fun (p : U × U) (M : Matrix (Fin m) (Fin k) ℝ) =>
      dotp (reluV (M.mulVec (a p.1))) (reluV (M.mulVec (a p.2)))) iF
  rw [← hsw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact (layer_dot_relu (m := m) hv (a p.1) (a p.2)).2

/-- **The mean of `gE` over the Gaussian matrix.** -/
theorem gE_mean {v : ℝ} (hv : 0 < v) (s : ℝ) (b : Fin k → ℝ) {a : U → Fin k → ℝ}
    (ham : Measurable a) {H : ℝ} (hH : ∀ u, normSq (a u) ≤ H) :
    Integrable (gE (m := m) μ a s b) (gaussMat m k v) ∧
    Integrable (fun u => (m : ℝ) * cS v s (a u) b) μ ∧
    Integrable (fun p : U × U => (m : ℝ) / 2 * (v * kernelPhi (a p.1) (a p.2))) (μ.prod μ) ∧
    ∫ M, gE (m := m) μ a s b M ∂gaussMat m k v =
      (m : ℝ) * cQ v s b - 2 * ∫ u, (m : ℝ) * cS v s (a u) b ∂μ +
        ∫ p, (m : ℝ) / 2 * (v * kernelPhi (a p.1) (a p.2)) ∂(μ.prod μ) := by
  obtain ⟨iA, eA, -, -⟩ := sq_layer (m := m) hv s b
  obtain ⟨iB, iBu, eB⟩ := cross_mean (m := m) μ hv s b ham hH
  obtain ⟨iC, iCu, eC'⟩ := sq_mean (m := m) μ hv.le ham hH
  have e : (gE (m := m) μ a s b) = fun M =>
      normSq (psV s b M) - 2 * dotp (psV s b M) (hbar μ (fun u => reluV (M.mulVec (a u)))) +
        normSq (hbar μ (fun u => reluV (M.mulVec (a u)))) := by
    funext M
    exact normSq_sub _ _
  have iA' : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (psV s b M))
      (gaussMat m k v) := iA
  have eA' : ∫ M : Matrix (Fin m) (Fin k) ℝ, normSq (psV s b M) ∂gaussMat m k v =
      (m : ℝ) * cQ v s b := eA
  obtain ⟨i3, e3⟩ := integral_lin3 iA' iB iC
  rw [e]
  refine ⟨i3, iBu, iCu, ?_⟩
  rw [e3, eA', eB, eC']

/-! ## The bound of the mean -/

lemma sq_coord_le {x : Fin k → ℝ} {H : ℝ} (h : normSq x ≤ H) (j : Fin k) : x j ^ 2 ≤ H :=
  (Finset.single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)).trans h

lemma integrable_coord {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ u, normSq (a u) ≤ H) (j : Fin k) : Integrable (fun u => a u j) μ :=
  integrable_of_abs_le ((measurable_pi_apply j).comp ham) (B := √H)
    fun u => Real.abs_le_sqrt (sq_coord_le (hH u) j)

/-- Jensen: `|E a|² ≤ E|a|²`. -/
lemma normSq_hbar_le {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ u, normSq (a u) ≤ H) : normSq (hbar μ a) ≤ ∫ u, normSq (a u) ∂μ := by
  have hi : ∀ j, Integrable (fun u => a u j ^ 2) μ := fun j =>
    integrable_of_abs_le (((measurable_pi_apply j).comp ham).pow_const 2) (B := H) fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact sq_coord_le (hH u) j
  have e : ∫ u, normSq (a u) ∂μ = ∑ j, ∫ u, a u j ^ 2 ∂μ :=
    integral_finsetSum _ fun j _ => hi j
  rw [e]
  unfold normSq
  exact Finset.sum_le_sum fun j _ => sq_integral_le (hi j)

lemma integral_dotp_hbar {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ u, normSq (a u) ≤ H) :
    Integrable (fun u => dotp (a u) (hbar μ a)) μ ∧
    ∫ u, dotp (a u) (hbar μ a) ∂μ = normSq (hbar μ a) := by
  have hi : ∀ j, Integrable (fun u => a u j * hbar μ a j) μ := fun j =>
    (integrable_coord μ ham hH j).mul_const _
  have h1 : ∫ u, dotp (a u) (hbar μ a) ∂μ = ∑ j, ∫ u, a u j * hbar μ a j ∂μ :=
    integral_finsetSum _ fun j _ => hi j
  refine ⟨integrable_finsetSum _ fun j _ => hi j, ?_⟩
  rw [h1]
  unfold normSq
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, sq]
  rfl

lemma integral_dotp_prod {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ u, normSq (a u) ≤ H) :
    Integrable (fun p : U × U => dotp (a p.1) (a p.2)) (μ.prod μ) ∧
    ∫ p, dotp (a p.1) (a p.2) ∂(μ.prod μ) = normSq (hbar μ a) := by
  have hi : ∀ j, Integrable (fun p : U × U => a p.1 j * a p.2 j) (μ.prod μ) := fun j =>
    (integrable_coord μ ham hH j).mul_prod (integrable_coord μ ham hH j)
  have h1 : ∫ p, dotp (a p.1) (a p.2) ∂(μ.prod μ) =
      ∑ j, ∫ p : U × U, a p.1 j * a p.2 j ∂(μ.prod μ) :=
    integral_finsetSum _ fun j _ => hi j
  refine ⟨integrable_finsetSum _ fun j _ => hi j, ?_⟩
  rw [h1]
  unfold normSq
  refine Finset.sum_congr rfl fun j _ => ?_
  have := integral_prod_mul (μ := μ) (ν := μ) (fun u => a u j) (fun u => a u j)
  rw [sq]
  exact this

lemma lt_of_mul_lt {x y plo : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hplo : 0 < plo)
    (h : x * y < plo) : x ^ 2 < plo ∨ y ^ 2 < plo := by
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  obtain ⟨h1, h2⟩ := hc
  have h3 : plo * plo ≤ x ^ 2 * y ^ 2 := mul_le_mul h1 h2 hplo.le (sq_nonneg _)
  have h4 : 0 ≤ x * y := mul_nonneg hx hy
  nlinarith

/-- The pointwise lower bound of the cross kernel (the tangent plane of the perspective). -/
lemma mid_point {v s N α k' mm : ℝ} (hv0 : 0 < v) (hmv0 : mm * v = 2) (b : Fin k → ℝ)
    (hsq : s ^ 2 / v + normSq b = N)
    (hab : ∀ t ∈ Icc (-1 : ℝ) 1, α + k' * t ≤ kappa t) (x : Fin k → ℝ) :
    α * √N * nrm x + k' * dotp x b ≤ mm * cS v s x b := by
  have hK1 := psi_ge hab (Fin.cons 0 x : Fin (k + 1) → ℝ)
    (Fin.cons (s / √v) b : Fin (k + 1) → ℝ)
  have e1 : nrm (Fin.cons 0 x : Fin (k + 1) → ℝ) = nrm x := by
    unfold nrm
    rw [normSq_cons]
    simp
  have e2 : nrm (Fin.cons (s / √v) b : Fin (k + 1) → ℝ) = √N := by
    unfold nrm
    rw [normSq_cons, div_pow, Real.sq_sqrt hv0.le, hsq]
  have e3 : dotp (Fin.cons 0 x : Fin (k + 1) → ℝ)
      (Fin.cons (s / √v) b : Fin (k + 1) → ℝ) = dotp x b := by
    rw [dotp_cons, zero_mul, zero_add]
  rw [e1, e2, e3] at hK1
  have e4 : mm * cS v s x b = psi kappa (Fin.cons 0 x : Fin (k + 1) → ℝ)
      (Fin.cons (s / √v) b : Fin (k + 1) → ℝ) := by
    unfold cS
    rw [kernelPhi_eq_psi]
    linear_combination (psi kappa (Fin.cons 0 x : Fin (k + 1) → ℝ)
      (Fin.cons (s / √v) b : Fin (k + 1) → ℝ) / 2) * hmv0
  rw [e4]
  linarith

/-- The pointwise upper bound of the two-point kernel (second order, cut at `plo`). -/
lemma third_point {u v mm plo : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 3 / 4) (hmv0 : mm * v = 2)
    (hplo : 0 < plo) (x y : Fin k → ℝ) :
    mm / 2 * (v * kernelPhi x y) ≤
      (kappa u - kg u * u) * (nrm x * nrm y) + kg u * dotp x y +
        Kq / plo * (dotp x y - u * (nrm x * nrm y)) ^ 2 +
        4 * plo * Kq * (if normSq x < plo then (1 : ℝ) else 0) +
        4 * plo * Kq * (if normSq y < plo then (1 : ℝ) else 0) := by
  have hK := Kq_pos
  have e4 : mm / 2 * (v * kernelPhi x y) = persp kappa (nrm x * nrm y) (dotp x y) := by
    rw [kernelPhi_eq_psi, psi_eq_persp]
    linear_combination (persp kappa (nrm x * nrm y) (dotp x y) / 2) * hmv0
  have hq := persp_quad_le hu0 hu1 (nrm_mul_nonneg x y) (abs_dotp_le_nrm x y) hplo
  have h1 : (0 : ℝ) ≤ (if normSq x < plo then (1 : ℝ) else 0) := by positivity
  have h2 : (0 : ℝ) ≤ (if normSq y < plo then (1 : ℝ) else 0) := by positivity
  have hI : (if nrm x * nrm y < plo then (1 : ℝ) else 0) ≤
      (if normSq x < plo then (1 : ℝ) else 0) + (if normSq y < plo then (1 : ℝ) else 0) := by
    by_cases hlt : nrm x * nrm y < plo
    · have e1 : (if nrm x * nrm y < plo then (1 : ℝ) else 0) = 1 := by simp [hlt]
      rw [e1]
      rcases lt_of_mul_lt (nrm_nonneg _) (nrm_nonneg _) hplo hlt with h | h
      · rw [nrm_sq] at h
        have e2 : (if normSq x < plo then (1 : ℝ) else 0) = 1 := by simp [h]
        rw [e2]
        linarith
      · rw [nrm_sq] at h
        have e2 : (if normSq y < plo then (1 : ℝ) else 0) = 1 := by simp [h]
        rw [e2]
        linarith
    · have e1 : (if nrm x * nrm y < plo then (1 : ℝ) else 0) = 0 := by simp [hlt]
      rw [e1]
      linarith
  have h3 : Kq * ((dotp x y - u * (nrm x * nrm y)) ^ 2 / plo +
      4 * plo * (if nrm x * nrm y < plo then (1 : ℝ) else 0)) ≤
      Kq * ((dotp x y - u * (nrm x * nrm y)) ^ 2 / plo +
      4 * plo * ((if normSq x < plo then (1 : ℝ) else 0) +
        (if normSq y < plo then (1 : ℝ) else 0))) := by
    gcongr
  rw [e4]
  refine (hq.trans (add_le_add le_rfl h3)).trans (le_of_eq ?_)
  ring

/-- The indicator of `{|a|² < plo}`: integrability and integral. -/
lemma integral_ite_lt {a : U → Fin k → ℝ} (ham : Measurable a) (plo : ℝ) :
    Integrable (fun x => if normSq (a x) < plo then (1 : ℝ) else 0) μ ∧
    ∫ x, (if normSq (a x) < plo then (1 : ℝ) else 0) ∂μ = μ.real {x | normSq (a x) < plo} := by
  have mS : MeasurableSet {x | normSq (a x) < plo} :=
    measurableSet_lt (continuous_normSq.measurable.comp ham) measurable_const
  have e : (fun x => if normSq (a x) < plo then (1 : ℝ) else 0) =
      Set.indicator {x | normSq (a x) < plo} (fun _ : U => (1 : ℝ)) := by
    funext x
    by_cases h : normSq (a x) < plo <;> simp [Set.indicator, h]
  rw [e]
  refine ⟨(integrable_const (1 : ℝ)).indicator mS, ?_⟩
  rw [integral_indicator_const _ mS]
  simp

/-- The squared error of the Gram kernel against `u·|a||a'|` is integrable. -/
lemma integrable_gramErr {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ x, normSq (a x) ≤ H) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Integrable (fun p : U × U =>
      (dotp (a p.1) (a p.2) - u * (nrm (a p.1) * nrm (a p.2))) ^ 2) (μ.prod μ) := by
  have mn : Measurable (fun x => nrm (a x)) := continuous_nrm.measurable.comp ham
  have hnb : ∀ x, nrm (a x) ≤ √H := fun x => Real.sqrt_le_sqrt (hH x)
  have mQ : Measurable (fun p : U × U =>
      (dotp (a p.1) (a p.2) - u * (nrm (a p.1) * nrm (a p.2))) ^ 2) :=
    ((continuous_dotp.measurable.comp ((ham.comp measurable_fst).prodMk
      (ham.comp measurable_snd))).sub (((mn.comp measurable_fst).mul
        (mn.comp measurable_snd)).const_mul u)).pow_const 2
  refine integrable_of_abs_le mQ (B := (2 * (√H * √H)) ^ 2) fun p => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have hc := abs_le.mp (abs_dotp_le_nrm (a p.1) (a p.2))
  have hp0 := nrm_mul_nonneg (a p.1) (a p.2)
  have hpP : nrm (a p.1) * nrm (a p.2) ≤ √H * √H :=
    mul_le_mul (hnb p.1) (hnb p.2) (nrm_nonneg _) ((nrm_nonneg _).trans (hnb p.1))
  have hup : 0 ≤ u * (nrm (a p.1) * nrm (a p.2)) := mul_nonneg hu0 hp0
  have hup' : u * (nrm (a p.1) * nrm (a p.2)) ≤ nrm (a p.1) * nrm (a p.2) := by nlinarith
  have habs : |dotp (a p.1) (a p.2) - u * (nrm (a p.1) * nrm (a p.2))| ≤ 2 * (√H * √H) := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  have := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rwa [sq_abs] at this

/-- The length `|a|`: integrability, and `0 ≤ E|a| ≤ √(E|a|²)`. -/
lemma nrm_mean {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ x, normSq (a x) ≤ H) :
    Integrable (fun x => nrm (a x)) μ ∧ 0 ≤ ∫ x, nrm (a x) ∂μ ∧
      ∫ x, nrm (a x) ∂μ ≤ √(∫ x, normSq (a x) ∂μ) := by
  have mn : Measurable (fun x => nrm (a x)) := continuous_nrm.measurable.comp ham
  have iN : Integrable (fun x => nrm (a x)) μ := integrable_of_abs_le mn (B := √H) fun x => by
    rw [abs_of_nonneg (nrm_nonneg _)]
    exact Real.sqrt_le_sqrt (hH x)
  have iN2 : Integrable (fun x => nrm (a x) ^ 2) μ :=
    integrable_of_abs_le (mn.pow_const 2) (B := H) fun x => by
      rw [abs_of_nonneg (sq_nonneg _), nrm_sq]
      exact hH x
  have h2 := sq_integral_le iN2
  simp_rw [nrm_sq] at h2
  exact ⟨iN, integral_nonneg fun x => nrm_nonneg _, (le_abs_self _).trans (Real.abs_le_sqrt h2)⟩

/-- The integrated lower bound of the cross term. -/
lemma mid_int {v s α k' : ℝ} (hv0 : 0 < v) (hmv0 : (m : ℝ) * v = 2) {a : U → Fin k → ℝ}
    (ham : Measurable a) {H : ℝ} (hH : ∀ x, normSq (a x) ≤ H)
    (hsq : s ^ 2 / v + normSq (hbar μ a) = ∫ x, normSq (a x) ∂μ)
    (hab : ∀ t ∈ Icc (-1 : ℝ) 1, α + k' * t ≤ kappa t)
    (iMid : Integrable (fun x => (m : ℝ) * cS v s (a x) (hbar μ a)) μ) :
    α * √(∫ x, normSq (a x) ∂μ) * (∫ x, nrm (a x) ∂μ) + k' * normSq (hbar μ a) ≤
      ∫ x, (m : ℝ) * cS v s (a x) (hbar μ a) ∂μ := by
  obtain ⟨iN, -, -⟩ := nrm_mean μ ham hH
  obtain ⟨iD1, eD1⟩ := integral_dotp_hbar μ ham hH
  obtain ⟨iL2, eL2⟩ := integral_lin2 iN iD1 (α * √(∫ x, normSq (a x) ∂μ)) k'
  rw [← eD1, ← eL2]
  exact integral_mono iL2 iMid fun x => mid_point hv0 hmv0 (hbar μ a) hsq hab (a x)

/-- The integrated upper bound of the two-point term. -/
lemma third_int {u v plo : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 3 / 4) (hmv0 : (m : ℝ) * v = 2)
    (hplo : 0 < plo) {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ x, normSq (a x) ≤ H)
    (iThird : Integrable (fun p : U × U => (m : ℝ) / 2 * (v * kernelPhi (a p.1) (a p.2)))
      (μ.prod μ)) :
    ∫ p, (m : ℝ) / 2 * (v * kernelPhi (a p.1) (a p.2)) ∂(μ.prod μ) ≤
      (kappa u - kg u * u) * ((∫ x, nrm (a x) ∂μ) * ∫ x, nrm (a x) ∂μ) +
        kg u * normSq (hbar μ a) +
        Kq / plo * (∫ p : U × U,
          (dotp (a p.1) (a p.2) - u * (nrm (a p.1) * nrm (a p.2))) ^ 2 ∂(μ.prod μ)) +
        4 * plo * Kq * μ.real {x | normSq (a x) < plo} +
        4 * plo * Kq * μ.real {x | normSq (a x) < plo} := by
  obtain ⟨iN, -, -⟩ := nrm_mean μ ham hH
  obtain ⟨iD2, eD2⟩ := integral_dotp_prod μ ham hH
  obtain ⟨iI, eI⟩ := integral_ite_lt μ ham plo
  have iQ := integrable_gramErr μ ham hH hu0 (by linarith : u ≤ 1)
  have eNN : ∫ p : U × U, nrm (a p.1) * nrm (a p.2) ∂(μ.prod μ) =
      (∫ x, nrm (a x) ∂μ) * ∫ x, nrm (a x) ∂μ :=
    integral_prod_mul (μ := μ) (ν := μ) (fun x => nrm (a x)) (fun x => nrm (a x))
  have iNN : Integrable (fun p : U × U => nrm (a p.1) * nrm (a p.2)) (μ.prod μ) :=
    iN.mul_prod iN
  have iI1 : Integrable (fun p : U × U => if normSq (a p.1) < plo then (1 : ℝ) else 0)
      (μ.prod μ) := iI.comp_fst μ
  have iI2 : Integrable (fun p : U × U => if normSq (a p.2) < plo then (1 : ℝ) else 0)
      (μ.prod μ) := iI.comp_snd μ
  have eI1 : ∫ p : U × U, (if normSq (a p.1) < plo then (1 : ℝ) else 0) ∂(μ.prod μ) =
      μ.real {x | normSq (a x) < plo} := by
    have := integral_fun_fst (μ := μ) (ν := μ)
      (fun x => if normSq (a x) < plo then (1 : ℝ) else 0)
    rw [this, eI]
    simp
  have eI2 : ∫ p : U × U, (if normSq (a p.2) < plo then (1 : ℝ) else 0) ∂(μ.prod μ) =
      μ.real {x | normSq (a x) < plo} := by
    have := integral_fun_snd (μ := μ) (ν := μ)
      (fun x => if normSq (a x) < plo then (1 : ℝ) else 0)
    rw [this, eI]
    simp
  obtain ⟨iL5, eL5⟩ := integral_lin5 iNN iD2 iQ iI1 iI2 (kappa u - kg u * u) (kg u) (Kq / plo)
    (4 * plo * Kq) (4 * plo * Kq)
  have := integral_mono iThird iL5 fun p => third_point hu0 hu1 hmv0 hplo (a p.1) (a p.2)
  rw [eL5, eNN, eD2, eI1, eI2] at this
  exact this

/-- The arithmetic of the bound. -/
lemma gap_arith {α k' N nb r E Q P plo T1 Mid Third : ℝ} (hα1 : α ≤ 1)
    (hE0 : 0 ≤ E) (hEr : E ≤ r) (hr2 : r * r = N)
    (hT1 : T1 = α * N + k' * nb) (hMid : α * r * E + k' * nb ≤ Mid)
    (hThird : Third ≤ α * (E * E) + k' * nb + Kq / plo * Q + 4 * plo * Kq * P +
      4 * plo * Kq * P) :
    T1 - 2 * Mid + Third ≤ (N - E ^ 2) + Kq * (Q / plo + 8 * plo * P) := by
  have t1 : α * (r - E) ^ 2 ≤ (r - E) ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hα1
  have t2 : 0 ≤ E * (r - E) := mul_nonneg hE0 (by linarith)
  have hKQ : Kq * (Q / plo + 8 * plo * P) =
      Kq / plo * Q + 4 * plo * Kq * P + 4 * plo * Kq * P := by ring
  rw [hT1, hKQ, ← hr2]
  nlinarith

/-- **The bound of the mean of `gE`**, at the scale `s² = v(N₂ − |b|²)`, `b = E a`,
`N₂ = E|a|²`, `v = 2/m`, if `|b|² ≤ (3/4)·N₂`. -/
theorem gap_bound (hm : 1 ≤ m) {a : U → Fin k → ℝ} (ham : Measurable a) {H : ℝ}
    (hH : ∀ u, normSq (a u) ≤ H) (hN2 : 0 < ∫ u, normSq (a u) ∂μ)
    (hu : normSq (hbar μ a) ≤ 3 / 4 * ∫ u, normSq (a u) ∂μ) {plo : ℝ} (hplo : 0 < plo) :
    Integrable (gE (m := m) μ a
      (√(2 / (m : ℝ) * (∫ u, normSq (a u) ∂μ - normSq (hbar μ a)))) (hbar μ a))
      (gaussMat m k (2 / (m : ℝ))) ∧
    ∫ M, gE (m := m) μ a
      (√(2 / (m : ℝ) * (∫ u, normSq (a u) ∂μ - normSq (hbar μ a)))) (hbar μ a) M
      ∂gaussMat m k (2 / (m : ℝ)) ≤
      (∫ u, normSq (a u) ∂μ - (∫ u, nrm (a u) ∂μ) ^ 2) +
        Kq * ((∫ p, (dotp (a p.1) (a p.2) -
          normSq (hbar μ a) / (∫ u, normSq (a u) ∂μ) * (nrm (a p.1) * nrm (a p.2))) ^ 2
            ∂(μ.prod μ)) / plo + 8 * plo * μ.real {u | normSq (a u) < plo}) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hv0 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hmv0 : (m : ℝ) * (2 / (m : ℝ)) = 2 := by field_simp
  have hJ := normSq_hbar_le μ ham hH
  obtain ⟨-, hE0, hEr⟩ := nrm_mean μ ham hH
  have hsq : √(2 / (m : ℝ) * (∫ u, normSq (a u) ∂μ - normSq (hbar μ a))) ^ 2 / (2 / (m : ℝ)) +
      normSq (hbar μ a) = ∫ u, normSq (a u) ∂μ := by
    rw [Real.sq_sqrt (mul_nonneg hv0.le (sub_nonneg.mpr hJ))]
    field_simp
    ring
  have hu0 : 0 ≤ normSq (hbar μ a) / ∫ u, normSq (a u) ∂μ :=
    div_nonneg (normSq_nonneg _) hN2.le
  have hu1 : normSq (hbar μ a) / ∫ u, normSq (a u) ∂μ ≤ 3 / 4 := by
    rw [div_le_iff₀ hN2]
    exact hu
  have huN : normSq (hbar μ a) / (∫ u, normSq (a u) ∂μ) * ∫ u, normSq (a u) ∂μ =
      normSq (hbar μ a) := div_mul_cancel₀ _ hN2.ne'
  obtain ⟨u, hud⟩ : ∃ u : ℝ, u = normSq (hbar μ a) / ∫ u, normSq (a u) ∂μ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ,
      s = √(2 / (m : ℝ) * (∫ u, normSq (a u) ∂μ - normSq (hbar μ a))) := ⟨_, rfl⟩
  rw [← hud] at hu0 hu1 huN ⊢
  rw [← hs] at hsq ⊢
  have huI : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hα1 : kappa u - kg u * u ≤ 1 := by
    have h1 := kappa_tangent_ge (ρ := 0) (ρ₀ := u) ⟨by norm_num, by norm_num⟩ huI
    have h2 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).2
    linarith
  have hab : ∀ t ∈ Icc (-1 : ℝ) 1, (kappa u - kg u * u) + kg u * t ≤ kappa t := by
    intro t ht
    have := kappa_tangent_ge ht huI
    linarith
  obtain ⟨iE, iMid, iThird, eE⟩ := gE_mean (m := m) μ hv0 s (hbar μ a) ham hH
  refine ⟨iE, ?_⟩
  rw [eE]
  have hT1 : (m : ℝ) * cQ (2 / (m : ℝ)) s (hbar μ a) =
      (kappa u - kg u * u) * (∫ u, normSq (a u) ∂μ) + kg u * normSq (hbar μ a) := by
    unfold cQ kernelPhi
    rw [normSq_hP1 hv0, normSq_hP2 hv0, dotp_hP, hsq, Real.mul_self_sqrt hN2.le, ← hud,
      ← huN]
    linear_combination ((∫ u, normSq (a u) ∂μ) * kappa u / 2) * hmv0
  exact gap_arith hα1 hE0 hEr (Real.mul_self_sqrt hN2.le) hT1
    (mid_int μ hv0 hmv0 ham hH hsq hab iMid)
    (third_int μ hu0 hu1 hmv0 hplo ham hH iThird)

end gen

/-! ## The first hidden layer of `A` at the stand-in inputs -/

section agent

variable {n m : ℕ}

lemma measurable_a1 (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (a1 c τ A₁) :=
  measurable_reluV.comp ((measurable_mulVec_left A₁).comp
    (measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ))))

/-- The first hidden vector is bounded: the inputs are unit vectors. -/
lemma a1_bound (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    ∃ H : ℝ, ∀ γ, normSq (a1 c τ A₁ γ) ≤ H := by
  have hc : Continuous (fun x : Fin n → ℝ => normSq (reluV (A₁.mulVec x))) :=
    continuous_normSq.comp (continuous_reluV.comp
      (Continuous.matrix_mulVec continuous_const continuous_id))
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun γ => ?_⟩
  have := hC (sphPt (c + τ • γ)) (normSq_sphPt hn _)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- **The mean over `A₂` of the squared distance of the mean-field centre to the exact centre**,
for fixed `c`, `τ`, `A₁`. -/
theorem centreDist_cond {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (hN2 : 0 < N2 c τ A₁)
    (hu : normSq (b1 c τ A₁) ≤ 3 / 4 * N2 c τ A₁) {plo : ℝ} (hplo : 0 < plo) :
    ∫⁻ A₂, ENNReal.ofReal (eC c τ (A₁, A₂)) ∂gaussMat m m (2 / (m : ℝ)) ≤
      ENNReal.ofReal (V1 c τ A₁ + Kq * (Qu c τ A₁ / plo +
        8 * plo * (stdGauss (Fin n)).real {γ | normSq (a1 c τ A₁ γ) < plo})) := by
  obtain ⟨H, hH⟩ := a1_bound hn c τ A₁
  obtain ⟨iE, hE⟩ := gap_bound (m := m) (stdGauss (Fin n)) hm (measurable_a1 c τ A₁) hH hN2 hu
    hplo
  have iE' : Integrable (fun A₂ : Matrix (Fin m) (Fin m) ℝ => eC c τ (A₁, A₂))
      (gaussMat m m (2 / (m : ℝ))) := iE
  have hE' : ∫ A₂ : Matrix (Fin m) (Fin m) ℝ, eC c τ (A₁, A₂) ∂gaussMat m m (2 / (m : ℝ)) ≤
      V1 c τ A₁ + Kq * (Qu c τ A₁ / plo +
        8 * plo * (stdGauss (Fin n)).real {γ | normSq (a1 c τ A₁ γ) < plo}) := hE
  rw [← ofReal_integral_eq_lintegral_ofReal iE'
    (Filter.Eventually.of_forall fun M => normSq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hE'

/-! ## Joint measurability -/

lemma measurable_a1_joint :
    Measurable (fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) × (Fin n → ℝ) =>
      a1 z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have h1 : Measurable (fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) × (Fin n → ℝ) =>
      z.1.1.1 + z.1.1.2 • z.2) :=
    (by fun_prop : Continuous fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) ×
      (Fin n → ℝ) => z.1.1.1 + z.1.1.2 • z.2).measurable
  exact measurable_reluV.comp (measurable_mulVec_joint.comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp h1)))

lemma measurable_b1 :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ => b1 x.1.1 x.1.2 x.2) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have mf : Measurable (fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) × (Fin n → ℝ) =>
      a1 z.1.1.1 z.1.1.2 z.1.2 z.2 j) := (measurable_pi_apply j).comp measurable_a1_joint
  exact (mf.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_N2 :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ => N2 x.1.1 x.1.2 x.2) := by
  have mf : Measurable (fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) × (Fin n → ℝ) =>
      normSq (a1 z.1.1.1 z.1.1.2 z.1.2 z.2)) :=
    continuous_normSq.measurable.comp measurable_a1_joint
  exact (mf.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_sMF :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ =>
      sMF x.1.1 x.1.2 x.2) := by
  unfold sMF
  exact Real.continuous_sqrt.measurable.comp (measurable_const.mul
    (measurable_N2.sub (continuous_normSq.measurable.comp measurable_b1)))

lemma measurable_bMF :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => bMF x.1.1 x.1.2 x.2) := by
  have hre : Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => (x.1, x.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hs := (measurable_sMF (n := n) (m := m)).comp hre
  simp only [Function.comp_def] at hs
  have hb := (measurable_b1 (n := n) (m := m)).comp hre
  simp only [Function.comp_def] at hb
  have hmv := (measurable_mulVec_joint (m := m) (k := m)).comp
    ((measurable_snd.comp measurable_snd).prodMk hb)
  simp only [Function.comp_def] at hmv
  refine measurable_pi_iff.mpr fun i => ?_
  have h := measurable_psiS.comp (hs.prodMk ((measurable_pi_apply i).comp hmv))
  simp only [Function.comp_def] at h
  exact h

lemma measurable_eC :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => eC x.1.1 x.1.2 x.2) := by
  unfold eC
  exact continuous_normSq.measurable.comp (measurable_bMF.sub measurable_bbar)

end agent

end BstLean.Part149

#print axioms BstLean.Part149.kappa_quad_34
#print axioms BstLean.Part149.centreDist_cond
#print axioms BstLean.Part149.measurable_eC
#print axioms BstLean.Part149.measurable_bMF
