import BstLean.Part56PropD_Average
import BstLean.Part56PropD_Correlation

/-! Assembly of the conditional estimates for Prop D. -/
namespace BstLean.Part56
open MeasureTheory
open BstLean.Part41 (Mono phiM)
open BstLean.Part29 (stdGauss)

variable {n : ℕ}

@[fun_prop] theorem continuous_phiB_PropD (d j : ℕ) (p : Mono n d) :
    Continuous (fun x : Fin n → ℝ => phiB d j x p) := by
  classical
  unfold phiB
  split_ifs
  · exact continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)
  · exact continuous_const

@[fun_prop] theorem continuous_kJ_PropD {X : Type*} [TopologicalSpace X]
    (d j : ℕ) (f g : X → (Fin n → ℝ)) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => kJ d j (f x) (g x)) := by
  unfold kJ
  apply continuous_finsetSum
  intro p _
  exact ((continuous_phiB_PropD d j p).comp hf).mul
    ((continuous_phiB_PropD d j p).comp hg)

@[fun_prop] theorem continuous_KR_PropD {X : Type*} [TopologicalSpace X]
    (d : ℕ) (v : Fin n → ℝ) (f g : X → (Fin n → ℝ))
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => KR d v (f x) (g x)) := by
  unfold KR
  apply continuous_finsetSum
  intro j _
  fun_prop

theorem measurable_rhoSq_PropD (d : ℕ) (v : Fin n → ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rhoR d v q.1 q.2 ^ 2) := by
  unfold rhoR tauR
  fun_prop

theorem kernel_integral_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (φ : X → Y) (hφ : Measurable φ)
    (F : Y → Y → ℝ) (hF : Measurable (Function.uncurry F)) :
    (∫ x, ∫ y, F x y ∂μ.map φ ∂μ.map φ) =
      ∫ x, ∫ y, F (φ x) (φ y) ∂μ ∂μ := by
  have hout : StronglyMeasurable (fun x => ∫ y, F x y ∂μ.map φ) := by
    simpa only [Function.uncurry] using
      hF.stronglyMeasurable.integral_prod_right' (ν := μ.map φ)
  rw [integral_map_of_stronglyMeasurable (μ := μ) hφ hout]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact integral_map_of_stronglyMeasurable hφ
    (hF.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable

section Mixed
variable {k : ℕ}

theorem mixed_correlation_integral_le (d : ℕ) (hd : 1 ≤ d) (CK : ℝ)
    (hK : KeyLemma56 d CK) (hn : 2 ≤ k + 1) (v : Fin (k + 1) → ℝ) (hv : UnitV v)
    (ν : Measure (ℝ × (Fin k → ℝ))) [IsProbabilityMeasure ν] :
    (∫ x, ∫ y, rhoR d v (polarState v x) (polarState v y) ^ 2
      ∂ν.prod (stdGauss (Fin (k + 1))) ∂ν.prod (stdGauss (Fin (k + 1)))) ≤
      (d : ℝ) * (∑ j ∈ Finset.Icc 1 d, (j : ℝ) ^ 4) *
        (CK / (((k + 1 : ℕ) : ℝ) - 1)) := by
  classical
  let μ := ν.prod (stdGauss (Fin (k + 1)))
  let f (j : ℕ) := mixedPsi d j v
  let u (j : ℕ) := phiB d j v
  let Q (j : ℕ) (x y : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) :=
    (∑ p : Mono (k + 1) d, projectOff (u j) (f j x) p * projectOff (u j) (f j y) p) ^ 2
  have hP (j : ℕ) (p : Mono (k + 1) d) :
      MemLp (fun x => projectOff (u j) (f j x) p) 2 μ :=
    projectOff_memLp μ (u j) (f j) (mixedPsi_memLp d j v hv μ) p
  have hQi (j : ℕ) (x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) :
      Integrable (Q j x) μ := dot_sq_integrable μ _ (hP j) _
  have hQo (j : ℕ) : Integrable (fun x => ∫ y, Q j x y ∂μ) μ :=
    (gram_sq_integrable μ _ (hP j)).integral_prod_left
  have hi (x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) :
      (∫ y, rhoR d v (polarState v x) (polarState v y) ^ 2 ∂μ) ≤
      (d : ℝ) * ∑ j ∈ Finset.Icc 1 d, ∫ y, Q j x y ∂μ := by
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((integrable_finsetSum _ (fun j _ => hQi j x)).const_mul (d : ℝ))
      (Filter.Eventually.of_forall fun y => rhoR_polarState_sq_le d hd v hv x y)
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => hQi j x)] at h
    exact h
  have ho := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
    ((integrable_finsetSum _ (fun j _ => hQo j)).const_mul (d : ℝ))
    (Filter.Eventually.of_forall hi)
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hQo j)] at ho
  apply ho.trans
  have hsum : (∑ j ∈ Finset.Icc 1 d, ∫ x, ∫ y, Q j x y ∂μ ∂μ) ≤
      ∑ j ∈ Finset.Icc 1 d, (j : ℝ) ^ 4 * (CK / (((k + 1 : ℕ) : ℝ) - 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (projectOff_gram_integral_le μ (u j) (f j) (mixedPsi_memLp d j v hv μ)).trans
      (mixedPsi_key_integral_le d CK hK hn v hv j (Finset.mem_Icc.mp hj).2 ν)
  calc
    _ ≤ (d : ℝ) * ∑ j ∈ Finset.Icc 1 d, (j : ℝ) ^ 4 *
        (CK / (((k + 1 : ℕ) : ℝ) - 1)) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end Mixed
end BstLean.Part56
