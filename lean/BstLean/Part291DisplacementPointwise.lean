import BstLean.Part162BD
import BstLean.Part242WeightedVariance
import BstLean.Part248Network

/-! The location displacement keeps the actual good-mean denominator.
The scale displacement retains its pointwise positive floor. -/
namespace BstLean.BlueprintLow
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part161 BstLean.Part162 BstLean.Part242 BstLean.Part248
variable {V : Type*} [MeasurableSpace V] {ν : Measure V} [IsProbabilityMeasure ν]
variable {G : Set V}

theorem idx_disp_good_mean (n : ℕ) (hG : MeasurableSet G) (hm : 0 < ν.real G) {φ ψ : V → ℝ}
    (mφ : Measurable φ) (mψ : Measurable ψ) {Mφ Mψ : ℝ} (bφ : ∀ v, |φ v| ≤ Mφ)
    (bψ : ∀ v, |ψ v| ≤ Mψ) {σl η C : ℝ} (hσl : 0 < σl) (hGψ : ∀ v ∈ G, σl ≤ ψ v)
    (hη : 1 - η ≤ ν.real G) (hη1 : η < 1) (hC : 0 ≤ C) :
    BstLean.Part161.hellG2 n ((∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C)
        (∫ v, ψ v ^ 2 ∂nrm ν G) (∫ v, ψ v ^ 2 ∂ν) ≤
      (1 - ν.real G) * (C * (∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν) / (2 * (1 - η) * goodMeanSq ν G ψ) +
        n * (∫ v, (ψ v ^ 2 - ∫ w, ψ w ^ 2 ∂ν) ^ 2 ∂ν) / (8 * (1 - η) ^ 2 * σl ^ 4)) := by
  have hP := nrm_prob ν hG hm
  set m := ν.real G with hmd
  have hm1 : m ≤ 1 := measureReal_le_one
  have hη0 : 0 < 1 - η := by linarith
  set S0 := ∫ v, ψ v ^ 2 ∂nrm ν G
  set Sb := ∫ v, ψ v ^ 2 ∂ν
  have b2 := sq_bound_of_abs bψ
  have hS0 : σl ^ 2 ≤ S0 := (nrm_mean_mem hG hm (mψ.pow_const 2) b2 (hi := Mψ ^ 2)
    fun v hv => ⟨pow_le_pow_left₀ hσl.le (hGψ v hv) 2, by
      have := b2 v; rw [abs_of_nonneg (sq_nonneg _)] at this; exact this⟩).1
  have hS0p : 0 < S0 := lt_of_lt_of_le (by positivity) hS0
  have i2 : Integrable (fun v => ψ v ^ 2) ν := intB (mψ.pow_const 2) b2
  have hSb : m * S0 ≤ Sb := by
    have e : m * S0 = ∫ v, G.indicator (fun v => ψ v ^ 2) v ∂ν := by
      simp only [S0]; rw [integral_nrm ν hG hm, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
    rw [e]
    exact integral_mono (i2.indicator hG) i2 fun v => by
      by_cases hv : v ∈ G
      · simp [Set.indicator_of_mem hv]
      · simp only [Set.indicator_of_notMem hv]; exact sq_nonneg _
  have hSbp : 0 < Sb := lt_of_lt_of_le (by positivity) hSb
  have hd0 : 0 ≤ (∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C := by positivity
  have hH := BstLean.Part161.hellG2_le n hS0p hSbp hd0
  refine hH.trans ?_
  -- the two mean shifts
  have sh1 := mean_shift hG hm mφ bφ
  have sh2 := mean_shift hG hm (mψ.pow_const 2) b2
  rw [← hmd] at sh1 sh2
  set Vφ := ∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν
  set VS := ∫ v, (ψ v ^ 2 - ∫ w, ψ w ^ 2 ∂ν) ^ 2 ∂ν
  have hVφ : 0 ≤ Vφ := integral_nonneg fun v => sq_nonneg _
  have hVS : 0 ≤ VS := integral_nonneg fun v => sq_nonneg _
  have hmη : (1 - η) ≤ m := hη
  have hβ0 : 0 ≤ 1 - m := by linarith
  have hSgm : goodMeanSq ν G ψ ≤ S0 := mean_sq_le mψ bψ
  have hgm : 0 < goodMeanSq ν G ψ :=
    (sq_pos_of_pos hσl).trans_le (good_mean_sq_lower ν hG hm mψ bψ hσl.le hGψ)
  -- location term
  have t2 : (∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C / (2 * (S0 + Sb)) ≤
      (1 - m) * (C * Vφ / (2 * (1 - η) * goodMeanSq ν G ψ)) := by
    rw [div_le_iff₀ (by positivity)]
    have k1 : (∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C ≤ (1 - m) / m * Vφ * C :=
      mul_le_mul_of_nonneg_right sh1 hC
    have k2 : (1 - m) / m * Vφ * C ≤ (1 - m) * (C * Vφ / (2 * (1 - η) * goodMeanSq ν G ψ)) *
        (2 * (S0 + Sb)) := by
      have h3 : (1 - η) * goodMeanSq ν G ψ ≤ m * (S0 + Sb) := by
        have : (1 - η) * goodMeanSq ν G ψ ≤ m * S0 := mul_le_mul hmη hSgm (by positivity) (by linarith)
        nlinarith
      have key : 1 / m ≤ (S0 + Sb) / ((1 - η) * goodMeanSq ν G ψ) := by
        rw [div_le_div_iff₀ hm (by positivity)]; linarith
      have hX : 0 ≤ (1 - m) * Vφ * C := by positivity
      calc (1 - m) / m * Vφ * C = (1 - m) * Vφ * C * (1 / m) := by ring
        _ ≤ (1 - m) * Vφ * C * ((S0 + Sb) / ((1 - η) * goodMeanSq ν G ψ)) :=
            mul_le_mul_of_nonneg_left key hX
        _ = (1 - m) * (C * Vφ / (2 * (1 - η) * goodMeanSq ν G ψ)) * (2 * (S0 + Sb)) := by
            field_simp
    linarith
  -- scale term
  have t1 : n * (S0 / Sb - 1) ^ 2 / (8 * (S0 / Sb)) ≤
      (1 - m) * (n * VS / (8 * (1 - η) ^ 2 * σl ^ 4)) := by
    have e : n * (S0 / Sb - 1) ^ 2 / (8 * (S0 / Sb)) = n * (S0 - Sb) ^ 2 / (8 * (S0 * Sb)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have k1 : (S0 - Sb) ^ 2 ≤ (1 - m) / m * VS := by
      have := sh2; rw [sub_sq'] at this ⊢; linarith
    have k3 : (1 - η) ^ 2 * σl ^ 4 ≤ m * (S0 * Sb) := by
      have q1 : (1 - η) * σl ^ 2 ≤ m * S0 := mul_le_mul hmη hS0 (by positivity) (by linarith)
      have q2 : (1 - η) * σl ^ 2 ≤ Sb := q1.trans hSb
      have : (1 - η) ^ 2 * σl ^ 4 = ((1 - η) * σl ^ 2) * ((1 - η) * σl ^ 2) := by ring
      rw [this]
      calc ((1 - η) * σl ^ 2) * ((1 - η) * σl ^ 2) ≤ (m * S0) * Sb :=
            mul_le_mul q1 q2 (by positivity) (by positivity)
        _ = m * (S0 * Sb) := by ring
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc n * (S0 - Sb) ^ 2 ≤ n * ((1 - m) / m * VS) := mul_le_mul_of_nonneg_left k1 hn0
      _ = (1 - m) * (n * VS) / m := by ring
      _ ≤ (1 - m) * (n * VS / (8 * (1 - η) ^ 2 * σl ^ 4)) * (8 * (S0 * Sb)) := by
        rw [div_le_iff₀ hm]
        have h0 : 0 ≤ (1 - m) * (n * VS) := by positivity
        have e2 : (1 - m) * (n * VS / (8 * (1 - η) ^ 2 * σl ^ 4)) * (8 * (S0 * Sb)) * m =
            (1 - m) * (n * VS) * (m * (S0 * Sb) / ((1 - η) ^ 2 * σl ^ 4)) := by
          field_simp
        rw [e2]
        have : 1 ≤ m * (S0 * Sb) / ((1 - η) ^ 2 * σl ^ 4) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith
  linarith


end BstLean.BlueprintLow
