import BstLean.Part153Op
import BstLean.Part151J
import BstLean.Part152OpMom
import BstLean.Part152LM
import Mathlib.Probability.Moments.SubGaussian

/-!
# Part 153: ingredients of Lemma PP (count of active rows, moments of lengths, Minkowski)

Paper source: `proofs/option-n/theorem5-05-covariance.tex`, Lemma PP, Step 0 and Step (c);
the standard facts (G1), (G7) of `theorem5-03-inputs.tex`.

* `cnt_tail`, `cnt_tail_lower`: Hoeffding's inequality for the number `∑ i, mask (g i)` of positive
  coordinates of a standard Gaussian vector `g` of `ℝ^m` (the count is `Bin(m, 1/2)`).
* `nrm_moment`: `E |ζ|^{2P} ≤ (√d + 𝔪_P)^{2P}`.
* `nrm_reluV_moment`: `E |ReLU(ζ)|^{2P} ≤ (√(d/2) + 𝔪_P)^{2P}`.
* `nrm_moment_lintegral`, `nrm_reluV_moment_lintegral`: the same in `∫⁻` form.
* `lintegral_pow_add_le`: Minkowski's inequality for `N`-th moments.
* `lintegral_pow_const_mul_le`: the version for the product with a constant.
* `lintegral_pow_split_le`, `lintegral_pow_split_le'`: splitting on an event.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130
open BstLean.Part152
open BstLean.Part151 (mask measurable_mask mask_nonneg)

/-! ## 1. Hoeffding's inequality for the count of positive coordinates -/

lemma mask_le_one_bin (t : ℝ) : mask t ≤ 1 := by
  unfold mask; split_ifs <;> norm_num

lemma integrable_mask : Integrable mask (gaussianReal 0 1) :=
  Integrable.of_mem_Icc 0 1 measurable_mask.aemeasurable
    (ae_of_all _ fun t => ⟨mask_nonneg t, mask_le_one_bin t⟩)

/-- `Pr(g > 0) = 1/2` for a standard Gaussian `g`, in the form `E mask(g) = 1/2`. -/
lemma int_mask : ∫ t, mask t ∂gaussianReal 0 1 = 1 / 2 := by
  have hneg : ∫ t, mask (-t) ∂gaussianReal 0 1 = ∫ t, mask t ∂gaussianReal 0 1 := by
    have h := integral_map (μ := gaussianReal 0 1) (φ := fun x : ℝ => -x)
      measurable_neg.aemeasurable (f := mask) measurable_mask.aestronglyMeasurable
    rw [gaussianReal_map_neg, neg_zero] at h
    exact h.symm
  have hi2 : Integrable (fun t => mask (-t)) (gaussianReal 0 1) :=
    Integrable.of_mem_Icc 0 1 (measurable_mask.comp measurable_neg).aemeasurable
      (ae_of_all _ fun t => ⟨mask_nonneg _, mask_le_one_bin _⟩)
  have hae : (fun t => mask t + mask (-t)) =ᵐ[gaussianReal 0 1] fun _ => (1 : ℝ) := by
    have : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    have h0 : ∀ᵐ t ∂gaussianReal 0 1, t ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
      exact measure_singleton 0
    filter_upwards [h0] with t ht
    unfold mask
    rcases lt_or_gt_of_ne ht with h | h
    · have h1 : ¬ (0 < t) := not_lt.mpr h.le
      have h2 : 0 < -t := by linarith
      simp [h1, h2]
    · have h2 : ¬ (0 < -t) := by linarith
      simp [h, h2]
  have hs := integral_add integrable_mask hi2
  rw [integral_congr_ae hae, hneg] at hs
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hs
  linarith

lemma int_mask_coord {m : ℕ} (i : Fin m) :
    ∫ g : Fin m → ℝ, mask (g i) ∂stdGauss (Fin m) = 1 / 2 := by
  unfold stdGauss
  rw [integral_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := i)
    measurable_mask.aestronglyMeasurable, int_mask]

lemma mask_coord_subG {m : ℕ} (i : Fin m) :
    HasSubgaussianMGF (fun g : Fin m → ℝ => mask (g i) - 1 / 2) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2)
      (stdGauss (Fin m)) := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := stdGauss (Fin m))
    (X := fun g : Fin m → ℝ => mask (g i)) (a := 0) (b := 1)
    (measurable_mask.comp (measurable_pi_apply i)).aemeasurable
    (ae_of_all _ fun g => ⟨mask_nonneg _, mask_le_one_bin _⟩)
  rw [int_mask_coord i] at h
  exact h

lemma mask_coord_indep (m : ℕ) :
    iIndepFun (fun (i : Fin m) (g : Fin m → ℝ) => mask (g i) - 1 / 2) (stdGauss (Fin m)) := by
  unfold stdGauss
  exact iIndepFun_pi (X := fun (_ : Fin m) (t : ℝ) => mask t - 1 / 2)
    (μ := fun _ : Fin m => gaussianReal 0 1)
    (fun _ => (measurable_mask.sub_const _).aemeasurable)

lemma mask_coord_indep_neg (m : ℕ) :
    iIndepFun (fun (i : Fin m) (g : Fin m → ℝ) => -(mask (g i) - 1 / 2)) (stdGauss (Fin m)) := by
  unfold stdGauss
  exact iIndepFun_pi (X := fun (_ : Fin m) (t : ℝ) => -(mask t - 1 / 2))
    (μ := fun _ : Fin m => gaussianReal 0 1)
    (fun _ => (measurable_mask.sub_const _).neg.aemeasurable)

lemma hoeff_exponent {m : ℕ} (hm : 0 < m) (η : ℝ) :
    -(η * m) ^ 2 / (2 * ((∑ _i : Fin m, ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ≥0) : ℝ)) =
      -2 * η ^ 2 * m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [sub_zero, nnnorm_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

/-- **Hoeffding's inequality for the count of positive coordinates** (upper tail):
`Pr(K > (1/2 + η)m) ≤ exp(−2η²m)`, `K = ∑ i, mask (g i)`. -/
theorem cnt_tail {m : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    (stdGauss (Fin m)).real {g | (1 / 2 + η) * m < ∑ i, mask (g i)} ≤
      Real.exp (-2 * η ^ 2 * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (mask_coord_indep m) (s := Finset.univ)
    (c := fun _ => (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (fun i _ => mask_coord_subG i)
    (ε := η * m) (by positivity)
  rw [hoeff_exponent hm η] at h
  refine le_trans (measureReal_mono (fun g hg => ?_)) h
  simp only [Set.mem_ofPred_eq] at hg ⊢
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- **Hoeffding's inequality for the count of positive coordinates** (lower tail):
`Pr(K < (1/2 − η)m) ≤ exp(−2η²m)`. -/
theorem cnt_tail_lower {m : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    (stdGauss (Fin m)).real {g | ∑ i, mask (g i) < (1 / 2 - η) * m} ≤
      Real.exp (-2 * η ^ 2 * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (mask_coord_indep_neg m)
    (s := Finset.univ) (c := fun _ => (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (fun i _ => (mask_coord_subG i).neg)
    (ε := η * m) (by positivity)
  rw [hoeff_exponent hm η] at h
  refine le_trans (measureReal_mono (fun g hg => ?_)) h
  simp only [Set.mem_ofPred_eq] at hg ⊢
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-! ## 2, 3. Moments of the length of a Gaussian vector and of its ReLU -/

section moments

variable {ι : Type} [Fintype ι]

/-- `(E f)² ≤ E f²`. -/
lemma sq_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  set c := ∫ ω, f ω ∂μ with hc
  have h0 : 0 ≤ ∫ ω, (f ω - c) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have e : ∀ ω, (f ω - c) ^ 2 = f ω ^ 2 - (2 * c * f ω - c ^ 2) := fun ω => by ring
  simp_rw [e] at h0
  have I2 : Integrable (fun ω => 2 * c * f ω - c ^ 2) μ :=
    (hf.const_mul _).sub (integrable_const _)
  have h1 : ∫ ω, (f ω ^ 2 - (2 * c * f ω - c ^ 2)) ∂μ =
      ∫ ω, f ω ^ 2 ∂μ - ∫ ω, (2 * c * f ω - c ^ 2) ∂μ := integral_sub hf2 I2
  have h2 : ∫ ω, (2 * c * f ω - c ^ 2) ∂μ = ∫ ω, 2 * c * f ω ∂μ - ∫ _ω, c ^ 2 ∂μ :=
    integral_sub (hf.const_mul _) (integrable_const _)
  rw [h1, h2, integral_const_mul] at h0
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
  nlinarith

/-- The general form: a nonnegative `1`-Lipschitz function `f` of a standard Gaussian vector
with `E f² ≤ s` has `E f^{2P} ≤ (√s + 𝔪_P)^{2P}`. -/
theorem lip_moment {f : (ι → ℝ) → ℝ} (hL : EuLip f 1) (hf0 : ∀ x, 0 ≤ f x) {s : ℝ}
    (hf2 : Integrable (fun x => f x ^ 2) (stdGauss ι)) (hs : ∫ x, f x ^ 2 ∂stdGauss ι ≤ s)
    {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun x => f x ^ (2 * P)) (stdGauss ι) ∧
    ∫ x, f x ^ (2 * P) ∂stdGauss ι ≤ (√s + gaussMomConst P) ^ (2 * P) := by
  classical
  obtain ⟨hfi, -, -⟩ := gaussConc_mgf_sharp zero_le_one hL 0
  have hmeas : Measurable f := (hL.continuous zero_le_one).measurable
  have hmean : ∫ x, f x ∂stdGauss ι ≤ √s := by
    apply Real.le_sqrt_of_sq_le
    exact (sq_integral_le hfi hf2).trans hs
  obtain ⟨hYi, hYb⟩ := gaussConc_moment zero_le_one hL P
  rw [one_pow, one_mul, ← gaussMomConst_pow hP] at hYb
  exact moment_shift (μ := stdGauss ι) (X := f)
    (Y := fun x => max (f x - ∫ y, f y ∂stdGauss ι) 0) hmeas
    ((hmeas.sub_const _).max measurable_const) hf0 (fun _ => le_max_right _ _)
    (Real.sqrt_nonneg s)
    (fun x => by
      have := le_max_left (f x - ∫ y, f y ∂stdGauss ι) 0
      linarith)
    hP (gaussMomConst_nonneg P) hYi hYb

lemma euLip_nrm : EuLip (nrm : (ι → ℝ) → ℝ) 1 := by
  intro x y
  rw [one_mul]
  exact abs_nrm_sub_le x y

lemma euLip_nrm_reluV : EuLip (fun x : ι → ℝ => nrm (reluV x)) 1 := by
  intro x y
  rw [one_mul]
  exact (abs_nrm_sub_le (reluV x) (reluV y)).trans (nrm_reluV_sub_le x y)

end moments

lemma int_normSq_std (d : ℕ) :
    Integrable (fun ζ : Fin d → ℝ => nrm ζ ^ 2) (stdGauss (Fin d)) ∧
    ∫ ζ : Fin d → ℝ, nrm ζ ^ 2 ∂stdGauss (Fin d) = d := by
  simp_rw [nrm_sq]
  unfold normSq stdGauss
  refine ⟨pi_sum_integrable (integrable_pow_gauss 2), ?_⟩
  rw [pi_sum (integrable_pow_gauss 2), BstLean.Part29.gaussMom_eq, Fintype.card_fin]
  norm_num [BstLean.Part29.gaussMom]

lemma int_normSq_reluV_std (d : ℕ) :
    Integrable (fun ζ : Fin d → ℝ => nrm (reluV ζ) ^ 2) (stdGauss (Fin d)) ∧
    ∫ ζ : Fin d → ℝ, nrm (reluV ζ) ^ 2 ∂stdGauss (Fin d) = (d : ℝ) / 2 := by
  simp_rw [nrm_sq]
  unfold normSq reluV stdGauss
  refine ⟨pi_sum_integrable (integrable_relu_pow 2), ?_⟩
  rw [pi_sum (integrable_relu_pow 2), int_relu_sq, Fintype.card_fin]
  ring

/-- **Moments of the length of a standard Gaussian vector**:
`E |ζ|^{2P} ≤ (√d + 𝔪_P)^{2P}`. -/
theorem nrm_moment (d : ℕ) {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun ζ : Fin d → ℝ => nrm ζ ^ (2 * P)) (stdGauss (Fin d)) ∧
    ∫ ζ : Fin d → ℝ, nrm ζ ^ (2 * P) ∂stdGauss (Fin d) ≤
      (√(d : ℝ) + gaussMomConst P) ^ (2 * P) :=
  lip_moment euLip_nrm nrm_nonneg (int_normSq_std d).1 (int_normSq_std d).2.le hP

/-- **Moments of the length of the ReLU of a standard Gaussian vector**:
`E |ReLU(ζ)|^{2P} ≤ (√(d/2) + 𝔪_P)^{2P}`. -/
theorem nrm_reluV_moment (d : ℕ) {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun ζ : Fin d → ℝ => nrm (reluV ζ) ^ (2 * P)) (stdGauss (Fin d)) ∧
    ∫ ζ : Fin d → ℝ, nrm (reluV ζ) ^ (2 * P) ∂stdGauss (Fin d) ≤
      (√((d : ℝ) / 2) + gaussMomConst P) ^ (2 * P) :=
  lip_moment (f := fun ζ : Fin d → ℝ => nrm (reluV ζ)) euLip_nrm_reluV (fun _ => nrm_nonneg _)
    (int_normSq_reluV_std d).1 (int_normSq_reluV_std d).2.le hP

/-! ## 4. The `∫⁻` forms -/

lemma lintegral_ofReal_le_of_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfi : Integrable f μ) {C : ℝ} (h : ∫ ω, f ω ∂μ ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal C := by
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)]
  exact ENNReal.ofReal_le_ofReal h

theorem nrm_moment_lintegral (d : ℕ) {P : ℕ} (hP : 1 ≤ P) :
    ∫⁻ ζ : Fin d → ℝ, ENNReal.ofReal (nrm ζ ^ (2 * P)) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal ((√(d : ℝ) + gaussMomConst P) ^ (2 * P)) :=
  lintegral_ofReal_le_of_integral_le (fun _ => pow_nonneg (nrm_nonneg _) _)
    (nrm_moment d hP).1 (nrm_moment d hP).2

theorem nrm_reluV_moment_lintegral (d : ℕ) {P : ℕ} (hP : 1 ≤ P) :
    ∫⁻ ζ : Fin d → ℝ, ENNReal.ofReal (nrm (reluV ζ) ^ (2 * P)) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal ((√((d : ℝ) / 2) + gaussMomConst P) ^ (2 * P)) :=
  lintegral_ofReal_le_of_integral_le (fun _ => pow_nonneg (nrm_nonneg _) _)
    (nrm_reluV_moment d hP).1 (nrm_reluV_moment d hP).2

/-! ## 5. Minkowski's inequality for `N`-th moments, and splitting on an event -/

section mink

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Minkowski's inequality**: if `∫⁻ X^N ≤ a^N` and `∫⁻ Y^N ≤ b^N` then
`∫⁻ (X + Y)^N ≤ (a + b)^N`. Any measure `μ`. -/
theorem lintegral_pow_add_le {X Y : Ω → ℝ≥0∞} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {N : ℕ} (hN : 1 ≤ N)
    (h1 : ∫⁻ ω, X ω ^ N ∂μ ≤ ENNReal.ofReal (a ^ N))
    (h2 : ∫⁻ ω, Y ω ^ N ∂μ ≤ ENNReal.ofReal (b ^ N)) :
    ∫⁻ ω, (X ω + Y ω) ^ N ∂μ ≤ ENNReal.ofReal ((a + b) ^ N) := by
  have hn : 0 < N := hN
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have Mk := ENNReal.lintegral_Lp_add_le (μ := μ) (p := (N : ℝ)) hX hY hn1
  simp only [Pi.add_apply, ENNReal.rpow_natCast] at Mk
  have root : ∀ {I : ℝ≥0∞} {c : ℝ}, 0 ≤ c → I ≤ ENNReal.ofReal (c ^ N) →
      I ^ (1 / (N : ℝ)) ≤ ENNReal.ofReal c := by
    intro I c hc hI
    calc I ^ (1 / (N : ℝ)) ≤ ENNReal.ofReal (c ^ N) ^ (1 / (N : ℝ)) :=
          ENNReal.rpow_le_rpow hI (by positivity)
      _ = ENNReal.ofReal c := by rw [ENNReal.ofReal_pow hc, enn_pow_root _ hn]
  have h3 : (∫⁻ ω, (X ω + Y ω) ^ N ∂μ) ^ (1 / (N : ℝ)) ≤ ENNReal.ofReal a + ENNReal.ofReal b :=
    Mk.trans (add_le_add (root ha h1) (root hb h2))
  have := pow_le_pow_left' h3 N
  rw [enn_root_pow _ hn, ← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_pow (by positivity)] at this
  exact this

/-- The product with a constant: if `∫⁻ X^N ≤ a^N` then `∫⁻ (c·X)^N ≤ (c·a)^N`. -/
theorem lintegral_pow_const_mul_le {X : Ω → ℝ≥0∞} {a c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    (h1 : ∫⁻ ω, X ω ^ N ∂μ ≤ ENNReal.ofReal (a ^ N)) :
    ∫⁻ ω, (ENNReal.ofReal c * X ω) ^ N ∂μ ≤ ENNReal.ofReal ((c * a) ^ N) := by
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    ENNReal.ofReal_mul (pow_nonneg hc N), ENNReal.ofReal_pow hc]
  gcongr

/-- **Splitting on an event**: if `μ S ≤ q`, `X ≤ a` outside `S` and `X ≤ b` everywhere, then
`∫⁻ X^N ≤ a^N + q·b^N`. -/
theorem lintegral_pow_split_le [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    {q : ℝ} (hq : 0 ≤ q) (hSq : μ S ≤ ENNReal.ofReal q) {X : Ω → ℝ≥0∞} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hXa : ∀ ω, ω ∉ S → X ω ≤ ENNReal.ofReal a)
    (hXb : ∀ ω, X ω ≤ ENNReal.ofReal b) (N : ℕ) :
    ∫⁻ ω, X ω ^ N ∂μ ≤ ENNReal.ofReal (a ^ N + q * b ^ N) := by
  have hpt : ∀ ω, X ω ^ N ≤
      ENNReal.ofReal (a ^ N) + S.indicator (fun _ => ENNReal.ofReal (b ^ N)) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, ENNReal.ofReal_pow hb]
      exact (pow_le_pow_left' (hXb ω) N).trans le_add_self
    · rw [Set.indicator_of_notMem hω, add_zero, ENNReal.ofReal_pow ha]
      exact pow_le_pow_left' (hXa ω hω) N
  calc ∫⁻ ω, X ω ^ N ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (a ^ N) +
          S.indicator (fun _ => ENNReal.ofReal (b ^ N)) ω) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (a ^ N) + ENNReal.ofReal (b ^ N) * μ S := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator hS, setLIntegral_const]
    _ ≤ ENNReal.ofReal (a ^ N) + ENNReal.ofReal (b ^ N) * ENNReal.ofReal q := by gcongr
    _ = ENNReal.ofReal (a ^ N + q * b ^ N) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hb N), ← ENNReal.ofReal_add (pow_nonneg ha N)
          (mul_nonneg (pow_nonneg hb N) hq), mul_comm]

lemma pow_add_pow_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {N : ℕ} (hN : 1 ≤ N) :
    a ^ N + c ^ N ≤ (a + c) ^ N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
    have h1 : 0 ≤ a * c ^ k := mul_nonneg ha (pow_nonneg hc k)
    have h2 : 0 ≤ c * a ^ k := mul_nonneg hc (pow_nonneg ha k)
    have h3 : (a + c) * (a ^ k + c ^ k) ≤ (a + c) * (a + c) ^ k :=
      mul_le_mul_of_nonneg_left ih (add_nonneg ha hc)
    rw [pow_succ', pow_succ', pow_succ']
    nlinarith

/-- **Splitting on an event**, the `L^N` form: `∫⁻ X^N ≤ (a + q^{1/N}·b)^N`. -/
theorem lintegral_pow_split_le' [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    {q : ℝ} (hq : 0 ≤ q) (hSq : μ S ≤ ENNReal.ofReal q) {X : Ω → ℝ≥0∞} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hXa : ∀ ω, ω ∉ S → X ω ≤ ENNReal.ofReal a)
    (hXb : ∀ ω, X ω ≤ ENNReal.ofReal b) {N : ℕ} (hN : 1 ≤ N) :
    ∫⁻ ω, X ω ^ N ∂μ ≤ ENNReal.ofReal ((a + q ^ ((1 : ℝ) / N) * b) ^ N) := by
  refine (lintegral_pow_split_le hS hq hSq ha hb hXa hXb N).trans (ENNReal.ofReal_le_ofReal ?_)
  have hN' : (N : ℝ) ≠ 0 := by
    have : 0 < N := hN
    exact_mod_cast this.ne'
  have e : (q ^ ((1 : ℝ) / N) * b) ^ N = q * b ^ N := by
    rw [mul_pow, ← Real.rpow_natCast (q ^ ((1 : ℝ) / N)) N, ← Real.rpow_mul hq,
      one_div, inv_mul_cancel₀ hN', Real.rpow_one]
  rw [← e]
  exact pow_add_pow_le ha (mul_nonneg (Real.rpow_nonneg hq _) hb) hN

end mink

end BstLean.Part153

#print axioms BstLean.Part153.cnt_tail
#print axioms BstLean.Part153.cnt_tail_lower
#print axioms BstLean.Part153.nrm_moment
#print axioms BstLean.Part153.nrm_reluV_moment
#print axioms BstLean.Part153.nrm_moment_lintegral
#print axioms BstLean.Part153.nrm_reluV_moment_lintegral
#print axioms BstLean.Part153.lintegral_pow_add_le
#print axioms BstLean.Part153.lintegral_pow_const_mul_le
#print axioms BstLean.Part153.lintegral_pow_split_le
#print axioms BstLean.Part153.lintegral_pow_split_le'
