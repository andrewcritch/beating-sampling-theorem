import BstLean.Part210Calibration

/-! S07: restricted calibration and integrability from dimension 4096. -/
namespace BstLean.Part210
open MeasureTheory Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part159
open BstLean.Part136 (hidGauss)

/-- Every measurable restriction of the source event has the sharp bound. -/
theorem qLtwo {n : ℕ} (hn : 4096 ≤ n) {G : Set (WHid n)}
    (mG : MeasurableSet G) (hG : G ⊆ GPap n) :
    BstLean.Part133.L2le (hidGauss (2 * n) (mW n))
      (G.indicator fun θ => qOf n (ccP n) θ - 1) (Rnew n / √(mW n : ℝ)) ∧
      (∀ θ ∈ GPap n, 0 ≤ qOf n (ccP n) θ ∧ qOf n (ccP n) θ ≤ 1001 / 1000) := by
  refine ⟨restricted_calibration hn mG (fun θ hθ => (hG hθ).1.2), ?_⟩
  intro θ hθ
  exact ⟨Real.sqrt_nonneg _,
    (BstLean.Part204.pap_q hn (BstLean.Part201.constK hn) hθ.1.2).1⟩

/-- The indicator error and its square are integrable. -/
theorem calibration_integrable {n : ℕ} (hn : 4096 ≤ n) {G : Set (WHid n)}
    (mG : MeasurableSet G) (hG : G ⊆ goodS n) :
    Integrable (G.indicator fun θ => qOf n (ccP n) θ - 1)
        (hidGauss (2 * n) (mW n)) ∧
      Integrable (fun θ => (G.indicator (fun θ => qOf n (ccP n) θ - 1) θ) ^ 2)
        (hidGauss (2 * n) (mW n)) := by
  have h := restricted_calibration hn mG hG
  exact ⟨((memLp_two_iff_integrable_sq h.aesm).2 h.int_sq).integrable one_le_two,
    h.int_sq⟩

/-- The same square bound holds on the unnormalized restricted measure. -/
theorem calibration_restrict {n : ℕ} (hn : 4096 ≤ n) {G : Set (WHid n)}
    (mG : MeasurableSet G) (hG : G ⊆ goodS n) :
    IntegrableOn (fun θ => qOf n (ccP n) θ - 1) G (hidGauss (2 * n) (mW n)) ∧
      IntegrableOn (fun θ => (qOf n (ccP n) θ - 1) ^ 2) G
        (hidGauss (2 * n) (mW n)) ∧
      (∫ θ in G, (qOf n (ccP n) θ - 1) ^ 2 ∂hidGauss (2 * n) (mW n)) ≤
        (Rnew n / √(mW n : ℝ)) ^ 2 := by
  have h := restricted_calibration hn mG hG
  have he : (fun θ => (G.indicator (fun θ => qOf n (ccP n) θ - 1) θ) ^ 2) =
      G.indicator (fun θ => (qOf n (ccP n) θ - 1) ^ 2) := by
    funext θ
    by_cases hθ : θ ∈ G <;> simp [hθ]
  have hi := (calibration_integrable hn mG hG).1
  have hs := h.int_sq
  have hb := h.le
  rw [he] at hs hb
  rw [integral_indicator mG] at hb
  exact ⟨(integrable_indicator_iff mG).1 hi, (integrable_indicator_iff mG).1 hs, hb⟩

end BstLean.Part210
#print BstLean.Part210.qLtwo
#print BstLean.Part210.calibration_integrable
#print axioms BstLean.Part210.qLtwo
#print axioms BstLean.Part210.calibration_integrable
#print axioms BstLean.Part210.calibration_restrict
