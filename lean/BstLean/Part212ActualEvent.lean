import BstLean.Part212Supply
import BstLean.Part212Mixed
import BstLean.Part212Retained

/-! A concrete fresh event uses the conservative coefficient `Theta = 1`. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix muI)
open BstLean.Part166 (certI psiK fK sK winC)
open BstLean.Part153 (nuA)

theorem latitude_fields_moment80 {n : ℕ} (hn : 1 ≤ n) {K2 : ℝ} (hK : 0 ≤ K2)
    (hLJ : LatitudeMoment160 n K2) (c : Fin n → ℝ) (τ : ℝ) (hw : winC c τ)
    (a : Ix n) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    (∫⁻ θ, ENNReal.ofReal (psiK fK ((c, τ), θ) a v ^ 80) ∂nuA n) ≤
      ENNReal.ofReal ((K2 / n) ^ 80) ∧
    (∫⁻ θ, ENNReal.ofReal (((n : ℝ) / 2 * psiK sK ((c, τ), θ) a v) ^ 80) ∂nuA n) ≤
      ENNReal.ofReal ((K2 / n) ^ 80) := by
  obtain ⟨hf, hz⟩ := hLJ c τ hw a v hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let s := latitude (n := n) (√(normSq c)) τ a
  have hs : s ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  have ht0 : 0 ≤ 1 - s ^ 2 := by linarith
  have ht1 : 1 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hbound : ((1 - s ^ 2) * K2 / n) ^ 80 ≤ (K2 / n) ^ 80 := by
    apply pow_le_pow_left₀ (div_nonneg (mul_nonneg ht0 hK) hn0.le)
    have h := mul_le_mul_of_nonneg_right ht1 (div_nonneg hK hn0.le)
    simpa only [one_mul, mul_div_assoc] using h
  refine ⟨hf.trans (ENNReal.ofReal_le_ofReal hbound), ?_⟩
  simp_rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg (by positivity : (0 : ℝ) ≤ n / 2) 80)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ n / 2)]
  calc ENNReal.ofReal ((n : ℝ) / 2) ^ 80 *
      (∫⁻ θ, ENNReal.ofReal (psiK sK ((c, τ), θ) a v ^ 80) ∂nuA n)
      ≤ ENNReal.ofReal ((n : ℝ) / 2) ^ 80 *
        ENNReal.ofReal (((1 - s ^ 2) * (2 / n) * K2 / n) ^ 80) := by
          rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ n / 2)]
          exact mul_le_mul_right hz _
    _ = ENNReal.ofReal (((1 - s ^ 2) * K2 / n) ^ 80) := by
      rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ n / 2),
        ← ENNReal.ofReal_mul (pow_nonneg (by positivity : (0 : ℝ) ≤ n / 2) 80),
        ← mul_pow]
      congr 2
      field_simp
    _ ≤ ENNReal.ofReal ((K2 / n) ^ 80) := ENNReal.ofReal_le_ofReal hbound

theorem key_mixed_score80 {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    (Φ : AgFam n → (Fin n → ℝ) → ℝ)
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) =>
      psiK Φ z.1 z.2.1 z.2.2)) {scale B : ℝ} (hscale : 0 ≤ scale)
    (hM : ∀ a : Ix n, ∀ v : Fin (n - 1) → ℝ, v ≠ 0 →
      ∫⁻ θ, ENNReal.ofReal ((scale * psiK Φ ((c, τ), θ) a v) ^ 80) ∂nuA n ≤
        ENNReal.ofReal (B ^ 80)) :
    ∫⁻ θ, (ENNReal.ofReal scale ^ (12 : ℕ) * certI Φ ((c, τ), θ)) ^ ((20 : ℝ) / 3)
      ∂nuA n ≤ ENNReal.ofReal (B ^ 80) := by
  letI : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by
    unfold stdGauss; infer_instance
  letI : SFinite (stdGauss (Fin (n - 1))) := inferInstance
  let ν := (muI n).prod (stdGauss (Fin (n - 1)))
  let Ψ := fun θ (p : Ix n × (Fin (n - 1) → ℝ)) => scale * psiK Φ ((c, τ), θ) p.1 p.2
  have hm : Measurable (Function.uncurry Ψ) :=
    (hΦ.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).const_mul scale
  have h0 : ∀ θ p, 0 ≤ Ψ θ p := fun θ p =>
    mul_nonneg hscale (BstLean.Part166.psiK_nonneg _ _ _ _)
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
      ENNReal.ofReal (B ^ 80) := hp.mono fun p hp => hM p.1 p.2 hp
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
  have h := mixed_score80 (nuA n) ν hm h0 hraw
  simpa only [hc] using h

/-- This coefficient retains the exact radius supply and uses `Theta = 1`. -/
noncomputable def conservativeLatitudeConstant160 (n q : ℕ) : ℝ :=
  latitudeConstant (√(latitudeJacobianSquared160 n q)) 1 (1 / 10000)

theorem fresh_latitude_charge160 {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q)
    (c : Fin n → ℝ) (τ : ℝ) (hw : winC c τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n
      (ENNReal.ofReal (conservativeLatitudeConstant160 n q / n))} ≤ 1 / 10000 := by
  have hK := latitudeJacobianSquared_pos160 hn hq
  have hj := latitudeMoment160_proved hn hq
  have hf := key_mixed_score80 (by omega) c τ fK BstLean.Part166.measurable_psiK_f
    (by norm_num : (0 : ℝ) ≤ 1) (B := latitudeJacobianSquared160 n q / n)
    (fun a v hv => by simpa only [one_mul] using
      (latitude_fields_moment80 (by omega) hK.le hj c τ hw a hv).1)
  have hz := key_mixed_score80 (by omega) c τ sK BstLean.Part166.measurable_psiK_s
    (scale := (n : ℝ) / 2) (by positivity) (B := latitudeJacobianSquared160 n q / n)
    (fun a v hv => (latitude_fields_moment80 (by omega) hK.le hj c τ hw a hv).2)
  have hs : √(latitudeJacobianSquared160 n q) ^ 2 = latitudeJacobianSquared160 n q :=
    Real.sq_sqrt hK.le
  apply latitudeEvent_charge_oneTenThousand (by omega) c τ (Real.sqrt_pos.mpr hK)
    (by norm_num : (0 : ℝ) < 1)
  · simpa only [hs, mul_one, ENNReal.ofReal_one, one_pow, one_mul] using hf
  · simpa only [hs, mul_one, latitudeCertZ] using hz
end BstLean.Part212
