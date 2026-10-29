import BstLean.Part211First
import BstLean.Part198HS

/-! The sharp HS source bound as a scalar function of retained noise. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC)

/-- This form uses nested square roots and avoids fractional powers. -/
noncomputable def hsRoot (n : ℕ) (θ v : ℝ) : ℝ :=
  √(√(4 * θ ^ 2 / (n : ℝ) ^ 3 * BstLean.Part194.CH n θ v)) +
    2 * √24 / ((n : ℝ) * √(n : ℝ))

noncomputable def hsProfile (n : ℕ) (θ v : ℝ) : ℝ :=
  (n : ℝ) ^ 3 / (4 * θ ^ 2) * hsRoot n θ v ^ 4

lemma hsProfile_nonneg (n : ℕ) (θ v : ℝ) : 0 ≤ hsProfile n θ v := by
  unfold hsProfile
  positivity

/-- The original HS event supplies a scalar noise profile without a new event. -/
theorem HS_profile_on_source {n : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v)
    (hθ : 1 / 4 ≤ thetaC c τ)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A ∉ BstLean.Part154.BadH n c τ 12) :
    BstLean.Part154.hsH A c τ ≤
      4 * τ ^ 4 * hsProfile n (thetaC c τ) v / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP (by omega : 1 ≤ n) c hτ
  have hθp : 0 < thetaC c τ := by linarith
  have ht : τ ^ 2 = rhoC c τ ^ 2 * thetaC c τ / n := by
    unfold thetaC
    field_simp
  have ht4 : τ ^ 4 = rhoC c τ ^ 4 * thetaC c τ ^ 2 / (n : ℝ) ^ 2 := by
    calc τ ^ 4 = (τ ^ 2) ^ 2 := by ring
         _ = _ := by rw [ht]; ring
  have he : 4 * τ ^ 4 / n * BstLean.Part194.CH n (thetaC c τ) v =
      rhoC c τ ^ 4 * (4 * thetaC c τ ^ 2 / (n : ℝ) ^ 3 *
        BstLean.Part194.CH n (thetaC c τ) v) := by rw [ht4]; field_simp
  have hr4 : √(rhoC c τ ^ 4) = rhoC c τ ^ 2 := by
    rw [show rhoC c τ ^ 4 = (rhoC c τ ^ 2) ^ 2 by ring, sqrt_sq (sq_nonneg _)]
  have hroot : √(√(4 * τ ^ 4 / n * BstLean.Part194.CH n (thetaC c τ) v)) +
      2 * √24 * √(normSq c + n * τ ^ 2) / ((n : ℝ) * √(n : ℝ)) =
      rhoC c τ * hsRoot n (thetaC c τ) v := by
    rw [he, sqrt_mul (by positivity : 0 ≤ rhoC c τ ^ 4), hr4,
      sqrt_mul (sq_nonneg _), sqrt_sq hρ.le]
    change _ + 2 * √24 * rhoC c τ / _ = _
    unfold hsRoot
    ring
  have h := BstLean.Part198.sharp_HS_same_event hn hn1 c hc hτ hv hθ hA
  rw [hroot, mul_pow] at h
  convert h using 1
  unfold hsProfile
  rw [ht4]
  field_simp

#print axioms HS_profile_on_source
end BstLean.Part211
