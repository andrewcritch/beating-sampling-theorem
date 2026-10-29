import BstLean.Part212ActualEvent
import BstLean.Part212Weighted

/-! The fresh event retains the latitude moment in the mixed moment estimate. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix muI)
open BstLean.Part166 (certI psiK fK sK winC)
open BstLean.Part153 (nuA)

theorem key_weighted_score80 {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    (Φ : AgFam n → (Fin n → ℝ) → ℝ)
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) =>
      psiK Φ z.1 z.2.1 z.2.2))
    {w : Ix n → ℝ} (hw : Measurable w) (hw0 : ∀ a, 0 ≤ w a)
    (hwpos : ∀ᵐ a ∂muI n, 0 < w a) (hw1 : ∀ a, w a ≤ 1)
    {scale B Θ : ℝ} (hscale : 0 ≤ scale) (hB : 0 ≤ B) (hΘ : 0 ≤ Θ)
    (hΘmom : ∫⁻ a, ENNReal.ofReal (w a ^ 12) ∂muI n ≤ ENNReal.ofReal (Θ ^ 12))
    (hM : ∀ a : Ix n, ∀ v : Fin (n - 1) → ℝ, v ≠ 0 →
      ∫⁻ θ, ENNReal.ofReal ((scale * psiK Φ ((c, τ), θ) a v) ^ 80) ∂nuA n ≤
        ENNReal.ofReal ((B * w a) ^ 80)) :
    ∫⁻ θ, (ENNReal.ofReal scale ^ (12 : ℕ) * certI Φ ((c, τ), θ)) ^ ((20 : ℝ) / 3)
      ∂nuA n ≤ ENNReal.ofReal ((B * Θ) ^ 80) := by
  letI : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by
    unfold stdGauss; infer_instance
  letI : SFinite (stdGauss (Fin (n - 1))) := inferInstance
  let ν := (muI n).prod (stdGauss (Fin (n - 1)))
  let Ψ := fun θ (p : Ix n × (Fin (n - 1) → ℝ)) => scale * psiK Φ ((c, τ), θ) p.1 p.2
  let W := fun p : Ix n × (Fin (n - 1) → ℝ) => w p.1
  let S := ∫⁻ p, ENNReal.ofReal (W p ^ 12) ∂ν
  have hm : Measurable (Function.uncurry Ψ) :=
    (hΦ.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).const_mul scale
  have h0 : ∀ θ p, 0 ≤ Ψ θ p := fun θ p =>
    mul_nonneg hscale (BstLean.Part166.psiK_nonneg _ _ _ _)
  have hW : Measurable W := hw.comp measurable_fst
  have hWpos : ∀ᵐ p ∂ν, 0 < W p :=
    (Measure.quasiMeasurePreserving_fst (μ := muI n)
      (ν := stdGauss (Fin (n - 1)))).ae hwpos
  have hS0 : S ≠ 0 := by
    intro hz
    have he := (lintegral_eq_zero_iff (hW.pow_const 12).ennreal_ofReal).mp hz
    have hh : ∀ᵐ p ∂ν, False := by
      filter_upwards [hWpos, he] with p hp he
      exact (ENNReal.ofReal_pos.mpr (pow_pos hp 12)).ne' he
    have he0 : ν Set.univ = 0 := by simpa using ae_iff.mp hh
    have he1 : ν Set.univ = 1 := by simp [ν]
    exact zero_ne_one (he0.symm.trans he1)
  have hS1 : S ≤ 1 := by
    calc S ≤ ∫⁻ _p, (1 : ℝ≥0∞) ∂ν := by
          apply lintegral_mono
          intro p
          simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal
            (pow_le_one₀ (hw0 p.1) (hw1 p.1) : W p ^ 12 ≤ 1))
      _ = 1 := by simp [ν]
  have hSt : S ≠ ∞ := ne_of_lt (hS1.trans_lt (by simp))
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have hv : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have hz : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton _)
    rw [ae_iff]
    simpa using hz
  have hp : ∀ᵐ p ∂ν, p.2 ≠ 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := muI n)
      (ν := stdGauss (Fin (n - 1)))).ae hv
  have hraw : ∀ᵐ p ∂ν, ∫⁻ θ, ENNReal.ofReal (Ψ θ p ^ 80) ∂nuA n ≤
      ENNReal.ofReal ((B * W p) ^ 80) := hp.mono fun p hp => hM p.1 p.2 hp
  have hc (θ) : ∫⁻ p, ENNReal.ofReal (Ψ θ p ^ 12) ∂ν =
      ENNReal.ofReal scale ^ (12 : ℕ) * certI Φ ((c, τ), θ) := by
    have hθ : Measurable (fun p => ENNReal.ofReal (Ψ θ p ^ 12)) :=
      ((hm.comp (measurable_const.prodMk measurable_id)).pow_const 12).ennreal_ofReal
    dsimp [ν]
    rw [lintegral_prod _ hθ.aemeasurable]
    dsimp [Ψ]
    simp_rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hscale 12),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [ENNReal.ofReal_pow hscale]
    rfl
  have hSmom : S ≤ ENNReal.ofReal (Θ ^ 12) := by
    dsimp [S, W, ν]
    have hmW : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
        ENNReal.ofReal (w p.1 ^ 12)) :=
      ((hw.comp measurable_fst).pow_const 12).ennreal_ofReal
    rw [lintegral_prod _ hmW.aemeasurable]
    simpa only [lintegral_const, measure_univ, smul_eq_mul, mul_one] using hΘmom
  have h := weighted_score80 (nuA n) ν hm h0 hW (fun p => hw0 p.1) hWpos
    rfl hS0 hSt hB hraw
  simp only [hc] at h
  refine h.trans ?_
  calc ENNReal.ofReal (B ^ 80) * S ^ ((20 : ℝ) / 3)
      ≤ ENNReal.ofReal (B ^ 80) * ENNReal.ofReal (Θ ^ 12) ^ ((20 : ℝ) / 3) := by gcongr
    _ = ENNReal.ofReal ((B * Θ) ^ 80) := by
      rw [ENNReal.ofReal_pow hΘ, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num only [Nat.cast_ofNat, show (12 : ℝ) * (20 / 3) = 80 by norm_num]
      change ENNReal.ofReal (B ^ 80) * ENNReal.ofReal Θ ^ ((80 : ℕ) : ℝ) =
        ENNReal.ofReal ((B * Θ) ^ 80)
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hΘ,
        ← ENNReal.ofReal_mul (pow_nonneg hB 80), ← mul_pow]
end BstLean.Part212
