import BstLean.Part57Defs
import BstLean.Part56PropD_Average

set_option maxHeartbeats 200000

/-! Conditional Key Lemma estimates for Part 57 Prop D. -/
namespace BstLean.Part57.PropD57
open MeasureTheory
open BstLean.Part41 (Mono)
open BstLean.Part29 (stdGauss)
open BstLean.Part56 (PhiJI PhiJI_bound coord_abs_le_one continuous_PhiJI
  dot_sq_integrable cross_gram_sq_integrable)
variable {n r : ℕ}

/-- The squared norm of a point in an orthonormal frame. -/
theorem spanV_sumsq (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (y : Fin r → ℝ) :
    ∑ i, spanV V y i ^ 2 = ∑ a, y a ^ 2 := by
  classical
  unfold spanV
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  have he (b : Fin r) :
      (∑ i, (y a * V a i) * (y b * V b i)) = y a * y b * (∑ i, V a i * V b i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he, show ∀ a b : Fin r, ∑ i, V a i * V b i = if a = b then 1 else 0 from hV]
  simp

/-- Normalizing the perpendicular projection has squared norm at most one. -/
theorem perpDirR_sumsq_le_one (V : Fin r → Fin n → ℝ) (g : Fin n → ℝ) :
    ∑ i, perpDirR V g i ^ 2 ≤ 1 :=
  BstLean.Part56.unitF53_sumsq_le_one
    (fun i => g i - ∑ a, coordY V g a * V a i)

theorem PhiJI_perpR_memLp (d j i : ℕ) (V : Fin r → Fin n → ℝ) (hV : OrthoF V)
    (y : Fin r → ℝ) (hy : ∑ a, y a ^ 2 ≤ 1) (p : Mono n d) :
    MemLp (fun g => PhiJI d j i (spanV V y) (perpDirR V g) p) 2 (stdGauss (Fin n)) := by
  have hcoord (a : Fin r) : Continuous (fun g : Fin n → ℝ => coordY V g a) := by
    unfold coordY
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))
  have hres : Continuous (fun g : Fin n → ℝ =>
      fun i => g i - ∑ a, coordY V g a * V a i) := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).sub
      (continuous_finsetSum _ (fun a _ => (hcoord a).mul continuous_const))
  have hw : Measurable (perpDirR V) := by
    change Measurable (BstLean.Part53.unitF53 ∘
      (fun g : Fin n → ℝ => fun i => g i - ∑ a, coordY V g a * V a i))
    exact BstLean.Part53.measurable_unitF.comp hres.measurable
  let f : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun q => PhiJI d j i q.1 q.2 p
  let q : (Fin n → ℝ) → ((Fin n → ℝ) × (Fin n → ℝ)) := fun g => (spanV V y, perpDirR V g)
  have hf : Measurable f := (continuous_PhiJI d j i p).measurable
  have hq : Measurable q := measurable_const.prodMk hw
  have hm : Measurable (fun g => PhiJI d j i (spanV V y) (perpDirR V g) p) := by
    change Measurable (f ∘ q)
    exact hf.comp hq
  apply MemLp.of_bound hm.aestronglyMeasurable ((2 : ℝ) ^ j)
  apply Filter.Eventually.of_forall
  intro g
  simpa only [Real.norm_eq_abs] using
    PhiJI_bound d j i (spanV V y) (perpDirR V g)
      (coord_abs_le_one _ ((spanV_sumsq V hV y).trans_le hy))
      (coord_abs_le_one _ (perpDirR_sumsq_le_one V g)) p

/-- The nonconstant perpendicular feature, divided by the perpendicular radius. -/
noncomputable def psiHatR (d j : ℕ) (u : ℝ) (a w : Fin n → ℝ) : Mono n d → ℝ :=
  ∑ i ∈ Finset.range j, u ^ i • PhiJI d j (i + 1) a w

theorem psiHatR_dot_expansion (d j : ℕ) (r r' : ℝ) (a a' w w' : Fin n → ℝ) :
    (∑ p : Mono n d, psiHatR d j r a w p * psiHatR d j r' a' w' p) =
      ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j,
        (r ^ i * r' ^ i') * ∑ p : Mono n d,
          PhiJI d j (i + 1) a w p * PhiJI d j (i' + 1) a' w' p := by
  classical
  simp only [psiHatR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem psiHatR_dot_sq_le (d j : ℕ) (r r' : ℝ) (a a' w w' : Fin n → ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr'0 : 0 ≤ r') (hr'1 : r' ≤ 1) :
    (∑ p : Mono n d, psiHatR d j r a w p * psiHatR d j r' a' w' p) ^ 2 ≤
      (j : ℝ) ^ 2 * ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j,
        (∑ p : Mono n d, PhiJI d j (i + 1) a w p *
          PhiJI d j (i' + 1) a' w' p) ^ 2 := by
  classical
  let S := (Finset.range j).product (Finset.range j)
  let Q (q : ℕ × ℕ) := ∑ p : Mono n d,
    PhiJI d j (q.1 + 1) a w p * PhiJI d j (q.2 + 1) a' w' p
  let L (q : ℕ × ℕ) := r ^ q.1 * r' ^ q.2
  have hL : ∀ q ∈ S, L q ^ 2 ≤ 1 := by
    intro q _
    have h0 : 0 ≤ L q := mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hr'0 _)
    have h1 : L q ≤ 1 := (mul_le_mul (pow_le_one₀ hr0 hr1) (pow_le_one₀ hr'0 hr'1)
      (pow_nonneg hr'0 _) (by norm_num)).trans_eq (one_mul _)
    exact pow_le_one₀ h0 h1
  have hs : (∑ q ∈ S, L q ^ 2) ≤ (j : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _q ∈ S, (1 : ℝ) := Finset.sum_le_sum hL
      _ = _ := by simp [S, Finset.card_product, pow_two]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S L Q
  have ht := hc.trans (mul_le_mul_of_nonneg_right hs
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  rw [psiHatR_dot_expansion]
  have he : (∑ q ∈ S, L q * Q q) =
      ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, (r ^ i * r' ^ i') * Q (i, i') :=
    Finset.sum_product' _ _ (fun i i' => (r ^ i * r' ^ i') * Q (i, i'))
  have he' : (∑ q ∈ S, Q q ^ 2) =
      ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, Q (i, i') ^ 2 :=
    Finset.sum_product' _ _ (fun i i' => Q (i, i') ^ 2)
  simpa only [he, he', Q] using ht

theorem psiHatR_key_integral_le (d : ℕ) (CK : ℝ) (hK : KeyLemma57 d r CK)
    (hn : 2 * r ≤ n) (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (j : ℕ) (hj : j ≤ d)
    (y y' : Fin r → ℝ) (u u' : ℝ) (hy : ∑ a, y a ^ 2 ≤ 1)
    (hy' : ∑ a, y' a ^ 2 ≤ 1)
    (hr0 : 0 ≤ u) (hr1 : u ≤ 1) (hr'0 : 0 ≤ u') (hr'1 : u' ≤ 1) :
    (∫ g, ∫ g', (∑ p : Mono n d, psiHatR d j u (spanV V y) (perpDirR V g) p *
      psiHatR d j u' (spanV V y') (perpDirR V g') p) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n)) ≤
      (j : ℝ) ^ 4 * (CK / ((n : ℝ) - r)) := by
  classical
  let μ := stdGauss (Fin n)
  let Q (i i' : ℕ) (g g' : Fin n → ℝ) :=
    (∑ p : Mono n d, PhiJI d j (i + 1) (spanV V y) (perpDirR V g) p *
      PhiJI d j (i' + 1) (spanV V y') (perpDirR V g') p) ^ 2
  have hQi (i i' : ℕ) (g : Fin n → ℝ) : Integrable (Q i i' g) μ :=
    dot_sq_integrable μ _ (PhiJI_perpR_memLp d j (i' + 1) V hV y' hy') _
  have hQo (i i' : ℕ) : Integrable (fun g => ∫ g', Q i i' g g' ∂μ) μ :=
    (cross_gram_sq_integrable μ _ _ (PhiJI_perpR_memLp d j (i + 1) V hV y hy)
      (PhiJI_perpR_memLp d j (i' + 1) V hV y' hy')).integral_prod_left
  have hinner (g : Fin n → ℝ) :
      (∫ g', (∑ p : Mono n d, psiHatR d j u (spanV V y) (perpDirR V g) p *
        psiHatR d j u' (spanV V y') (perpDirR V g') p) ^ 2 ∂μ) ≤
      (j : ℝ) ^ 2 * ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, ∫ g', Q i i' g g' ∂μ := by
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun i' _ => hQi i i' g))).const_mul ((j : ℝ) ^ 2))
      (Filter.Eventually.of_forall fun g' => psiHatR_dot_sq_le d j u u' (spanV V y) (spanV V y')
        (perpDirR V g) (perpDirR V g') hr0 hr1 hr'0 hr'1)
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun i' _ => hQi i i' g))] at h
    simp_rw [integral_finsetSum _ (fun i' _ => hQi _ i' g)] at h
    exact h
  have houter := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun g => integral_nonneg fun _ => sq_nonneg _)
    ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun i' _ => hQo i i'))).const_mul ((j : ℝ) ^ 2))
    (Filter.Eventually.of_forall hinner)
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun i' _ => hQo i i'))] at houter
  simp_rw [integral_finsetSum _ (fun i' _ => hQo _ i')] at houter
  apply houter.trans
  have hsum : (∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j,
      ∫ g, ∫ g', Q i i' g g' ∂μ ∂μ) ≤
      (j : ℝ) ^ 2 * (CK / ((n : ℝ) - r)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range j, ∑ _i' ∈ Finset.range j, CK / ((n : ℝ) - r) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro i' hi'
        exact hK n hn V hV y y' hy hy' j (i + 1) (i' + 1) hj (by omega)
          (by simpa using Finset.mem_range.mp hi) (by omega)
          (by simpa using Finset.mem_range.mp hi')
      _ = _ := by simp [pow_two, mul_assoc]
  calc
    _ ≤ (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 * (CK / ((n : ℝ) - r))) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring


/-- A coordinate bound used only to justify integrals on a product law. -/
theorem psiHatR_bound (d j : ℕ) (u : ℝ) (a w : Fin n → ℝ)
    (ha : ∀ l, |a l| ≤ 1) (hw : ∀ l, |w l| ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (p : Mono n d) : |psiHatR d j u a w p| ≤ (j : ℝ) * 2 ^ j := by
  classical
  simp only [psiHatR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ i ∈ Finset.range j, |u ^ i * PhiJI d j (i + 1) a w p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 _)]
      exact (mul_le_mul (pow_le_one₀ hu0 hu1) (PhiJI_bound d j (i + 1) a w ha hw p)
        (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
    _ = _ := by simp

/-- The conditional Key Lemma remains valid after any bounded measurable mixture of axial
coordinates and perpendicular radii. -/
theorem mixedPsiR_key_integral_le {A : Type*} [MeasurableSpace A]
    (d : ℕ) (CK : ℝ) (hK : KeyLemma57 d r CK) (hn : 2 * r ≤ n)
    (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (j : ℕ) (hj : j ≤ d)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (y : A → Fin r → ℝ) (u : A → ℝ) (hy : Measurable y) (hu : Measurable u)
    (hyb : ∀ a, ∑ b, y a b ^ 2 ≤ 1) (hu0 : ∀ a, 0 ≤ u a) (hu1 : ∀ a, u a ≤ 1) :
    (∫ x, ∫ x', (∑ p : Mono n d,
      psiHatR d j (u x.1) (spanV V (y x.1)) (perpDirR V x.2) p *
      psiHatR d j (u x'.1) (spanV V (y x'.1)) (perpDirR V x'.2) p) ^ 2
      ∂ν.prod (stdGauss (Fin n)) ∂ν.prod (stdGauss (Fin n))) ≤
      (j : ℝ) ^ 4 * (CK / ((n : ℝ) - r)) := by
  classical
  let γ := stdGauss (Fin n)
  let f (x : A × (Fin n → ℝ)) :=
    psiHatR d j (u x.1) (spanV V (y x.1)) (perpDirR V x.2)
  have hspan : Continuous (spanV V) := by
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ (fun a _ => (continuous_apply a).mul continuous_const)
  have hcoord (a : Fin r) : Continuous (fun g : Fin n → ℝ => coordY V g a) := by
    unfold coordY
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))
  have hres : Continuous (fun g : Fin n → ℝ =>
      fun i => g i - ∑ a, coordY V g a * V a i) := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).sub
      (continuous_finsetSum _ (fun a _ => (hcoord a).mul continuous_const))
  have hw : Measurable (perpDirR V) := by
    change Measurable (BstLean.Part53.unitF53 ∘
      (fun g : Fin n → ℝ => fun i => g i - ∑ a, coordY V g a * V a i))
    exact BstLean.Part53.measurable_unitF.comp hres.measurable
  have hfm (p : Mono n d) : Measurable (fun x => f x p) := by
    have hP (i : ℕ) : Measurable (fun x : A × (Fin n → ℝ) =>
        PhiJI d j (i + 1) (spanV V (y x.1)) (perpDirR V x.2) p) := by
      let P : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun q => PhiJI d j (i + 1) q.1 q.2 p
      let q : A × (Fin n → ℝ) → ((Fin n → ℝ) × (Fin n → ℝ)) :=
        fun x => (spanV V (y x.1), perpDirR V x.2)
      have hPm : Measurable P := (continuous_PhiJI d j (i + 1) p).measurable
      have hqm : Measurable q :=
        ((hspan.measurable.comp hy).comp measurable_fst).prodMk (hw.comp measurable_snd)
      change Measurable (P ∘ q)
      exact hPm.comp hqm
    simp only [f, psiHatR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun i _ =>
      ((hu.comp measurable_fst).pow_const i).mul (hP i))
  have hfb (x : A × (Fin n → ℝ)) (p : Mono n d) : |f x p| ≤ (j : ℝ) * 2 ^ j :=
    psiHatR_bound d j _ _ _
      (coord_abs_le_one _ ((spanV_sumsq V hV (y x.1)).trans_le (hyb x.1)))
      (coord_abs_le_one _ (perpDirR_sumsq_le_one V x.2)) (hu0 x.1) (hu1 x.1) p
  have hm : Measurable (fun q : (A × (Fin n → ℝ)) × (A × (Fin n → ℝ)) =>
      (∑ p : Mono n d, f q.1 p * f q.2 p) ^ 2) := by
    apply Measurable.pow_const
    exact Finset.measurable_sum _ (fun p _ =>
      ((hfm p).comp measurable_fst).mul ((hfm p).comp measurable_snd))
  let C := ((Fintype.card (Mono n d) : ℝ) * ((j : ℝ) * 2 ^ j) ^ 2) ^ 2
  change (∫ x, ∫ x', (∑ p : Mono n d, f x p * f x' p) ^ 2 ∂ν.prod γ ∂ν.prod γ) ≤ _
  rw [BstLean.Part56.product_kernel_reorder ν γ
    (fun x x' => (∑ p : Mono n d, f x p * f x' p) ^ 2) hm C
    (fun x x' => BstLean.Part56.finite_dot_sq_bound _ _ _ (by positivity) (hfb x) (hfb x'))]
  have hi (a a' : A) :
      (∫ g, ∫ g', (∑ p : Mono n d, f (a, g) p * f (a', g') p) ^ 2 ∂γ ∂γ) ≤
      (j : ℝ) ^ 4 * (CK / ((n : ℝ) - r)) :=
    psiHatR_key_integral_le d CK hK hn V hV j hj
      (y a) (y a') (u a) (u a') (hyb a) (hyb a') (hu0 a) (hu1 a) (hu0 a') (hu1 a')
  have ha (a : A) := integral_mono_of_nonneg (μ := ν)
    (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _)
    (integrable_const (μ := ν) ((j : ℝ) ^ 4 * (CK / ((n : ℝ) - r))))
    (Filter.Eventually.of_forall (hi a))
  simp only [integral_const, probReal_univ, one_smul] at ha
  have h := integral_mono_of_nonneg (μ := ν)
    (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => integral_nonneg fun _ =>
      integral_nonneg fun _ => sq_nonneg _)
    (integrable_const (μ := ν) ((j : ℝ) ^ 4 * (CK / ((n : ℝ) - r))))
    (Filter.Eventually.of_forall ha)
  simpa only [integral_const, probReal_univ, one_smul] using h


end BstLean.Part57.PropD57
