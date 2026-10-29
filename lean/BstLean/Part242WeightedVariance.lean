import BstLean.Part242GoodScale

/-! The integrated variance terms retain their actual good-mean denominator. -/
namespace BstLean.Part242
open MeasureTheory ProbabilityTheory Real
open BstLean.Part162
variable {V : Type*} [MeasurableSpace V] {ν : Measure V} [IsProbabilityMeasure ν]
variable {G : Set V}

theorem weighted_eps_variance (hG : MeasurableSet G) (hm : 0 < ν.real G)
    {ψ : V → ℝ} (mψ : Measurable ψ) {Mψ : ℝ} (bψ : ∀ v, |ψ v| ≤ Mψ)
    {ws σl η : ℝ} (hws : 0 ≤ ws) (hσl : 0 < σl) (hη : 1 - η ≤ ν.real G) (hη1 : η < 1)
    (hGψ : ∀ v ∈ G, |ψ v - ∫ w, ψ w ∂ν| ≤ ws ∧ σl ≤ ψ v) :
    ∫ v, (ψ v ^ 2 / ∫ w, ψ w ^ 2 ∂nrm ν G - 1) ^ 2 ∂nrm ν G ≤
      (4 * (1 + ws / σl) ^ 2 / (1 - η)) *
        (conditionalVariance ν ψ / goodMeanSq ν G ψ)
:= by
  have hP := nrm_prob ν hG hm
  obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, t1, t2⟩ := idx_scale hG hm mψ bψ hws hσl hGψ
  set P := nrm ν G
  set S0 := ∫ w, ψ w ^ 2 ∂P
  set ψg := ∫ w, ψ w ∂P
  set ψb := ∫ w, ψ w ∂ν
  have hg0 : σl ≤ ψg := hlo.trans t1
  have hgp : 0 < ψg := lt_of_lt_of_le hσl hg0
  have hSg : ψg ^ 2 ≤ S0 := mean_sq_le mψ bψ
  have hS0 : 0 < S0 := lt_of_lt_of_le (by positivity) hSg
  have b2 := sq_bound_of_abs bψ
  -- step 1: E ε² = E(ψ² − S0)²/S0²
  have e1 : ∫ v, (ψ v ^ 2 / S0 - 1) ^ 2 ∂P = (∫ v, (ψ v ^ 2 - S0) ^ 2 ∂P) / S0 ^ 2 := by
    rw [← integral_div]
    congr 1; funext v; field_simp
  -- step 2: variance ≤ second moment about ψg²
  have h2 : ∫ v, (ψ v ^ 2 - S0) ^ 2 ∂P ≤ ∫ v, (ψ v ^ 2 - ψg ^ 2) ^ 2 ∂P :=
    var_le_sq_sub (mψ.pow_const 2) b2 (ψg ^ 2)
  -- step 3: pointwise on G
  have bψd : ∀ v, |ψ v - ψg| ≤ Mψ + |ψg| := fun v => (abs_sub _ _).trans (by linarith [bψ v])
  have bψb : ∀ v, |ψ v - ψb| ≤ Mψ + |ψb| := fun v => (abs_sub _ _).trans (by linarith [bψ v])
  have i3 : Integrable (fun v => (2 * ψg + 2 * ws) ^ 2 * (ψ v - ψg) ^ 2) P :=
    (intB ((mψ.sub_const _).pow_const 2) (sq_bound_of_abs bψd)).const_mul _
  have i4 : Integrable (fun v => (ψ v ^ 2 - ψg ^ 2) ^ 2) P :=
    intB (((mψ.pow_const 2).sub_const _).pow_const 2) (sq_bound_of_abs (M := Mψ ^ 2 + |ψg ^ 2|)
      fun v => (abs_sub _ _).trans (by linarith [b2 v]))
  have h3 : ∫ v, (ψ v ^ 2 - ψg ^ 2) ^ 2 ∂P ≤ ∫ v, (2 * ψg + 2 * ws) ^ 2 * (ψ v - ψg) ^ 2 ∂P := by
    refine integral_mono_ae i4 i3 ((nrm_ae_mem ν hG).mono fun v hv => ?_)
    obtain ⟨a1, a2⟩ := hG' v hv
    have hψ0 : 0 ≤ ψ v := (lt_of_lt_of_le hσl (hlo.trans a1)).le
    have k1 : 0 ≤ ψ v + ψg := by linarith
    have k2 : ψ v + ψg ≤ 2 * ψg + 2 * ws := by linarith
    have e : (ψ v ^ 2 - ψg ^ 2) ^ 2 = (ψ v + ψg) ^ 2 * (ψ v - ψg) ^ 2 := by ring
    beta_reduce
    rw [e]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ k1 k2 2) (sq_nonneg _)
  have h4 : ∫ v, (ψ v - ψg) ^ 2 ∂P ≤ ∫ v, (ψ v - ψb) ^ 2 ∂P := var_le_sq_sub mψ bψ ψb
  rw [integral_const_mul] at h3
  have W0 : 0 ≤ ∫ v, (ψ v - ψb) ^ 2 ∂P := integral_nonneg fun v => sq_nonneg _
  have kc : (2 * ψg + 2 * ws) ^ 2 / S0 ^ 2 ≤
      4 * (1 + ws / σl) ^ 2 / ψg ^ 2 := by
    calc
      _ ≤ (2 * ψg + 2 * ws) ^ 2 / (ψg ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (pow_le_pow_left₀ (by positivity) hSg 2)
      _ = 4 * (1 + ws / ψg) ^ 2 / ψg ^ 2 := by field_simp <;> ring
      _ ≤ _ := by
        have hratio : ws / ψg ≤ ws / σl := div_le_div_of_nonneg_left hws hσl hg0
        gcongr
  have hiW := intB (μ := ν) ((mψ.sub_const ψb).pow_const 2) (sq_bound_of_abs bψb)
  have hres := integral_nrm_le hG hm (fun v => sq_nonneg (ψ v - ψb)) hiW
  have hinv : (ν.real G)⁻¹ ≤ (1 - η)⁻¹ := inv_anti₀ (by linarith) hη
  have hfull0 : 0 ≤ conditionalVariance ν ψ := integral_nonneg fun v => sq_nonneg _
  have hW : ∫ v, (ψ v - ψb) ^ 2 ∂P ≤ conditionalVariance ν ψ / (1 - η) := by
    refine hres.trans ?_
    change (ν.real G)⁻¹ * conditionalVariance ν ψ ≤ _
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hinv hfull0
  have hnum : ∫ v, (ψ v ^ 2 - S0) ^ 2 ∂P ≤
      (2 * ψg + 2 * ws) ^ 2 * ∫ v, (ψ v - ψb) ^ 2 ∂P := by
    have hm4 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (2 * ψg + 2 * ws))
    linarith
  rw [e1]
  calc
    _ ≤ (2 * ψg + 2 * ws) ^ 2 / S0 ^ 2 * ∫ v, (ψ v - ψb) ^ 2 ∂P := by
      exact (div_le_div_of_nonneg_right hnum (sq_nonneg S0)).trans_eq (by ring)
    _ ≤ (4 * (1 + ws / σl) ^ 2 / ψg ^ 2) *
        (conditionalVariance ν ψ / (1 - η)) :=
      mul_le_mul kc hW W0 (by positivity)
    _ = _ := by unfold goodMeanSq; dsimp [ψg]; ring

/-- The location term retains the same good-mean denominator and reference scale. -/
theorem weighted_location_variance (hG : MeasurableSet G) (hm : 0 < ν.real G)
    {φ z : V → ℝ} (mφ : Measurable φ) {Mφ : ℝ} (bφ : ∀ v, |φ v| ≤ Mφ)
    {S0 C η : ℝ} (hgm : 0 < goodMeanSq ν G z)
    (hS0 : goodMeanSq ν G z ≤ S0) (hC : 0 ≤ C)
    (hη : 1 - η ≤ ν.real G) (hη1 : η < 1) :
    ∫ v, (sqrt (C / S0) * (φ v - ∫ w, φ w ∂nrm ν G)) ^ 2 ∂nrm ν G ≤
      (C / (1 - η)) * (conditionalVariance ν φ / goodMeanSq ν G z) := by
  have h := idx_del_sq hG hm mφ bφ (sqrt_pos.mpr hgm)
    (show sqrt (goodMeanSq ν G z) ^ 2 ≤ S0 by rwa [sq_sqrt hgm.le]) hC hη hη1
  rw [sq_sqrt hgm.le] at h
  exact h.trans_eq (by unfold conditionalVariance; ring)

end BstLean.Part242
