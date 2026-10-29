import BstLean.Part292CoarseCaps
import BstLean.Part292SourceNumbers

/-! The actual source constants satisfy the six normalized row-coefficient caps. -/
namespace BstLean.Part292
open Real BstLean.Part170 BstLean.Part171 BstLean.Part223

theorem normalized_coefficient_caps {n : ℕ} (hn : 8000 ≤ n) :
    let σ := lowSigma n
    let O := lowOperator n
    let sp := lowBiasUpper n
    let Γ := tA n*O^2+sp^2
    let C := sqrt (tA n)*O
    let d := (1035/100 : ℝ)/(n : ℝ)^3
    let v := (414/10 : ℝ)/(n : ℝ)^4
    let p := (8*10^14 : ℝ)/(n : ℝ)^8
    (n : ℝ)*sqrt n*lowF0 (391/1000) (605/1000) σ Γ d v p ≤ 36/10000 ∧
    (n : ℝ)*sqrt n*lowF1 (391/1000) (605/1000) σ C d v p ≤ 126/100000 ∧
    (n : ℝ)*sqrt n*lowF2 (605/1000) σ d ≤ 41/100000 ∧
    (n : ℝ)^2*lowW0 (391/1000) (605/1000) σ Γ d v p ≤ 205/100000 ∧
    (n : ℝ)^2*lowW1 (391/1000) (605/1000) σ C sp d v p ≤ 161/100000 ∧
    (n : ℝ)^2*lowW2 (391/1000) (605/1000) C d p ≤ 79/100000 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hn0
  have hσ : 0 < lowSigma n := by unfold lowSigma; positivity
  have hx0 : (0 : ℝ) ≤ 1/(n : ℝ) := by positivity
  have hx : (1 : ℝ)/(n : ℝ) ≤ 1/8000 := one_div_le_one_div_of_le (by norm_num) hnR
  have hs3 : sqrt (n : ℝ)^3 = (n : ℝ)*sqrt n := by
    rw [pow_succ, sq_sqrt hn0.le]
  have hs4 : sqrt (n : ℝ)^4 = (n : ℝ)^2 := by
    rw [show 4=2*2 by rfl, pow_mul, sq_sqrt hn0.le]
  have hs6 : sqrt (n : ℝ)^6 = (n : ℝ)^3 := by
    rw [show 6=2*3 by rfl, pow_mul, sq_sqrt hn0.le]
  have hs8 : sqrt (n : ℝ)^8 = (n : ℝ)^4 := by
    rw [show 8=2*4 by rfl, pow_mul, sq_sqrt hn0.le]
  have hs16 : sqrt (n : ℝ)^16 = (n : ℝ)^8 := by
    rw [show 16=2*8 by rfl, pow_mul, sq_sqrt hn0.le]
  have hscale := collected_scale hr (by norm_num : (0 : ℝ) < 391/1000)
    (by positivity : (0 : ℝ) < sqrt (999/2000)) (605/1000) 7 3 2
    (1035/100) (414/10) (8*10^14) (by norm_num) (by norm_num)
  simp only [hs3, hs4, hs6, hs8, hs16, sq_sqrt hn0.le] at hscale
  obtain ⟨hG,hC,hsp⟩ := source_scale_caps hn
  have ht := tA_nonneg n
  have hO : 0 ≤ lowOperator n := by unfold lowOperator; positivity
  have hsp0 : 0 ≤ lowBiasUpper n := by unfold lowBiasUpper; positivity
  have hp0 := (BstLean.Part153.phiG_pos 0).le
  have hp1 := (BstLean.Part153.phiG_pos 1).le
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply le_trans ?_ (normF0_cap hx0 hx)
    rw [← hscale.1]
    unfold lowF0 lowSigma
    gcongr
  · apply le_trans ?_ (normF1_cap hx0 hx)
    rw [← hscale.2.1]
    unfold lowF1 lowSigma
    gcongr
  · simpa only [lowSigma, ← hscale.2.2.1] using normF2_cap hx0 hx
  · apply le_trans ?_ (normW0_cap hx0 hx)
    rw [← hscale.2.2.2.1]
    unfold lowW0 lowSigma
    gcongr
  · apply le_trans ?_ (normW1_cap hx0 hx)
    rw [← hscale.2.2.2.2.1]
    unfold lowW1 lowSigma
    gcongr
  · apply le_trans ?_ (normW2_cap hx0 hx)
    rw [← hscale.2.2.2.2.2]
    unfold lowW2
    gcongr

theorem momentBound_weaken {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {k : ℕ} {f : X → ℝ} {a b : ℝ} (h : MomentBound μ k f a) (hab : a ≤ b) :
    MomentBound μ k f b :=
  ⟨h.measurable, h.nonneg.trans hab,
    h.moment.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h.nonneg hab k))⟩

end BstLean.Part292
