import BstLean.Part207Mixture

/-! The paper coefficient six follows from the stronger elementary coefficient three. -/
namespace BstLean.Part207
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part161

variable {V : Type*} [MeasurableSpace V]

/-- The scalar price is exactly the paper formula when Y equals a² vδ. -/
lemma hqL_eq_paper (n : ℕ) (e ve vd a2 : ℝ) :
    hqL n e ve (a2 * vd) =
      n * ve / (4 * (1 - e) ^ 2) + a2 * vd / (2 * (1 - e)) +
        (√(a2 * vd * ve) + √((n : ℝ) / 2) * ve) / (1 - e) := by
  simp only [hqL, mul_comm ve (a2 * vd)]

theorem mix_root_hq_paper {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ}
    (hl : Measurable l) (hS : Measurable S) {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1)
    (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0)
    :
    (√(∫ v, gP B (l v • c) (S v) ∂pm) - √(gP B (l0 • c) S0)) ^ 2 ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
        (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1) / 4 +
      6 * hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) ^ 3 := by
  have h := mix_root_hq_cubic pm c hB hS0 hl hS hε₀ hwS hwl hml hmS
  have hL : 0 ≤ hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
      (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) := hqL_nonneg hε₀
    (integral_nonneg fun v => sq_nonneg (S v / S0 - 1))
    (integral_nonneg fun v => mul_nonneg
      (div_nonneg (normSq_nonneg c) hS0.le) (sq_nonneg (l v - l0)))
  have h3 := pow_nonneg hL 3
  linarith

theorem mix_density_hq_paper {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ}
    (hl : Measurable l) (hS : Measurable S) {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1)
    (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0)
    :
    BstLean.Part138.hellSq (stdGauss (Fin n))
      (fun z => ∫ v, gdN (muN c l0 S0 (l v)) (S v / S0) z ∂pm) (fun _ => 1) ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
        (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1) / 4 +
      6 * hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) ^ 3 := by
  have h := mix_density_hq_cubic pm c hS0 hl hS hε₀ hwS hwl hml hmS
  have hL : 0 ≤ hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
      (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) := hqL_nonneg hε₀
    (integral_nonneg fun v => sq_nonneg (S v / S0 - 1))
    (integral_nonneg fun v => mul_nonneg
      (div_nonneg (normSq_nonneg c) hS0.le) (sq_nonneg (l v - l0)))
  have h3 := pow_nonneg hL 3
  linarith

end BstLean.Part207
