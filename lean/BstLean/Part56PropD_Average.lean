import BstLean.Part56PropD_Bounds
import BstLean.Part56PropD_Moments

/-! Conditional averaging estimates for Prop D. -/
namespace BstLean.Part56
open MeasureTheory
open BstLean.Part41 (Mono)
open BstLean.Part29 (stdGauss)
variable {n : ℕ}

theorem psiHat_key_integral_le (d : ℕ) (CK : ℝ) (hK : KeyLemma56 d CK)
    (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (j : ℕ) (hj : j ≤ d)
    (s r s' r' : ℝ) (hs : |s| ≤ 1) (hs' : |s'| ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr'0 : 0 ≤ r') (hr'1 : r' ≤ 1) :
    (∫ g, ∫ g', (∑ p : Mono n d, psiHat d j s r v (perpDir v g) p *
      psiHat d j s' r' v (perpDir v g') p) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n)) ≤
      (j : ℝ) ^ 4 * (CK / ((n : ℝ) - 1)) := by
  classical
  let μ := stdGauss (Fin n)
  let Q (i i' : ℕ) (g g' : Fin n → ℝ) :=
    (∑ p : Mono n d, PhiJI d j (i + 1) (s • v) (perpDir v g) p *
      PhiJI d j (i' + 1) (s' • v) (perpDir v g') p) ^ 2
  have hQi (i i' : ℕ) (g : Fin n → ℝ) : Integrable (Q i i' g) μ :=
    dot_sq_integrable μ _ (PhiJI_perp_memLp d j (i' + 1) v hv s' hs') _
  have hQo (i i' : ℕ) : Integrable (fun g => ∫ g', Q i i' g g' ∂μ) μ :=
    (cross_gram_sq_integrable μ _ _ (PhiJI_perp_memLp d j (i + 1) v hv s hs)
      (PhiJI_perp_memLp d j (i' + 1) v hv s' hs')).integral_prod_left
  have hinner (g : Fin n → ℝ) :
      (∫ g', (∑ p : Mono n d, psiHat d j s r v (perpDir v g) p *
        psiHat d j s' r' v (perpDir v g') p) ^ 2 ∂μ) ≤
      (j : ℝ) ^ 2 * ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, ∫ g', Q i i' g g' ∂μ := by
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun i' _ => hQi i i' g))).const_mul ((j : ℝ) ^ 2))
      (Filter.Eventually.of_forall fun g' => psiHat_dot_sq_le d j s r s' r' v
        (perpDir v g) (perpDir v g') hr0 hr1 hr'0 hr'1)
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
      (j : ℝ) ^ 2 * (CK / ((n : ℝ) - 1)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range j, ∑ _i' ∈ Finset.range j, CK / ((n : ℝ) - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro i' hi'
        exact hK n hn v hv s s' hs hs' j (i + 1) (i' + 1) hj (by omega)
          (by simpa using Finset.mem_range.mp hi) (by omega)
          (by simpa using Finset.mem_range.mp hi')
      _ = _ := by simp [pow_two, mul_assoc]
  calc
    _ ≤ (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 * (CK / ((n : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring

section Product
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable (ν : Measure A) (γ : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]

theorem bounded_measurable_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hm : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem product_kernel_reorder (F : (A × B) → (A × B) → ℝ)
    (hm : Measurable (Function.uncurry F)) (C : ℝ)
    (hb : ∀ x y, ‖F x y‖ ≤ C) :
    (∫ x, ∫ y, F x y ∂ν.prod γ ∂ν.prod γ) =
      ∫ a, ∫ a', ∫ b, ∫ b', F (a, b) (a', b') ∂γ ∂γ ∂ν ∂ν := by
  have hall : Integrable (Function.uncurry F) ((ν.prod γ).prod (ν.prod γ)) :=
    bounded_measurable_integrable _ _ hm C (fun p => hb p.1 p.2)
  have hi (x : A × B) : Integrable (F x) (ν.prod γ) :=
    bounded_measurable_integrable _ _ (hm.comp (measurable_const.prodMk measurable_id)) C (hb x)
  rw [integral_prod (fun x => ∫ y, F x y ∂ν.prod γ) hall.integral_prod_left]
  simp_rw [integral_prod (fun y => F _ y) (hi _)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  apply integral_integral_swap
  have hm3 : Measurable (fun p : (B × A) × B => F (a, p.1.1) (p.1.2, p.2)) :=
    hm.comp ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hm2 := hm3.stronglyMeasurable.integral_prod_right' (ν := γ)
  apply bounded_measurable_integrable (γ.prod ν) _ hm2.measurable C
  intro p
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := γ)
      (Filter.Eventually.of_forall fun b' => hb (a, p.1) (p.2, b'))

end Product

theorem finite_dot_sq_bound {ι : Type*} [Fintype ι] (f g : ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ i, |f i| ≤ C) (hg : ∀ i, |g i| ≤ C) :
    ‖(∑ i, f i * g i) ^ 2‖ ≤ ((Fintype.card ι : ℝ) * C ^ 2) ^ 2 := by
  have hb : |∑ i, f i * g i| ≤ (Fintype.card ι : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ i, |f i * g i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, C ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, pow_two]
        exact mul_le_mul (hf i) (hg i) (abs_nonneg _) hC
      _ = _ := by simp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∑ i, f i * g i))]
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mpr hb

section Mixed
variable {k : ℕ}

theorem measurable_mixedGram (d j : ℕ) (v : Fin (k + 1) → ℝ) :
    Measurable (fun q : (((ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) ×
      ((ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ))) =>
      (∑ p : Mono (k + 1) d, mixedPsi d j v q.1 p * mixedPsi d j v q.2 p) ^ 2) := by
  apply Measurable.pow_const
  apply Finset.measurable_sum
  intro p _
  exact ((measurable_mixedPsi_coord d j v p).comp measurable_fst).mul
    ((measurable_mixedPsi_coord d j v p).comp measurable_snd)

theorem mixedPsi_key_integral_le (d : ℕ) (CK : ℝ) (hK : KeyLemma56 d CK)
    (hn : 2 ≤ k + 1) (v : Fin (k + 1) → ℝ) (hv : UnitV v)
    (j : ℕ) (hj : j ≤ d) (ν : Measure (ℝ × (Fin k → ℝ))) [IsProbabilityMeasure ν] :
    (∫ x, ∫ y, (∑ p : Mono (k + 1) d, mixedPsi d j v x p * mixedPsi d j v y p) ^ 2
      ∂ν.prod (stdGauss (Fin (k + 1))) ∂ν.prod (stdGauss (Fin (k + 1)))) ≤
      (j : ℝ) ^ 4 * (CK / (((k + 1 : ℕ) : ℝ) - 1)) := by
  let γ := stdGauss (Fin (k + 1))
  let C := ((Fintype.card (Mono (k + 1) d) : ℝ) * ((j : ℝ) * 2 ^ j) ^ 2) ^ 2
  rw [product_kernel_reorder ν γ
    (fun x y => (∑ p : Mono (k + 1) d, mixedPsi d j v x p * mixedPsi d j v y p) ^ 2)
    (measurable_mixedGram d j v) C
    (fun x y => finite_dot_sq_bound _ _ ((j : ℝ) * 2 ^ j) (by positivity)
      (mixedPsi_bound d j v hv x) (mixedPsi_bound d j v hv y))]
  have hi (a a' : ℝ × (Fin k → ℝ)) :
      (∫ g, ∫ g', (∑ p : Mono (k + 1) d,
        mixedPsi d j v (a, g) p * mixedPsi d j v (a', g') p) ^ 2 ∂γ ∂γ) ≤
      (j : ℝ) ^ 4 * (CK / (((k + 1 : ℕ) : ℝ) - 1)) := by
    dsimp only [mixedPsi, γ]
    exact psiHat_key_integral_le d CK hK hn v hv j hj
      (axialS a.1 (BstLean.Part53.radF53 a.2)) (axialR a.1 (BstLean.Part53.radF53 a.2))
      (axialS a'.1 (BstLean.Part53.radF53 a'.2)) (axialR a'.1 (BstLean.Part53.radF53 a'.2))
      (axialS_abs_le_one _ _) (axialS_abs_le_one _ _)
      (axialR_nonneg _ _ (Real.sqrt_nonneg _)) (axialR_le_one _ _ (Real.sqrt_nonneg _))
      (axialR_nonneg _ _ (Real.sqrt_nonneg _)) (axialR_le_one _ _ (Real.sqrt_nonneg _))
  have ha (a : ℝ × (Fin k → ℝ)) := integral_mono_of_nonneg (μ := ν)
    (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _)
    (integrable_const (μ := ν) ((j : ℝ) ^ 4 * (CK / (((k + 1 : ℕ) : ℝ) - 1))))
    (Filter.Eventually.of_forall (hi a))
  simp only [integral_const, probReal_univ, one_smul] at ha
  have h := integral_mono_of_nonneg (μ := ν)
    (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => integral_nonneg fun _ =>
      integral_nonneg fun _ => sq_nonneg _)
    (integrable_const (μ := ν) ((j : ℝ) ^ 4 * (CK / (((k + 1 : ℕ) : ℝ) - 1))))
    (Filter.Eventually.of_forall ha)
  simpa only [integral_const, probReal_univ, one_smul] using h

end Mixed

end BstLean.Part56
