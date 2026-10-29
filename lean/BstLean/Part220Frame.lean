import BstLean.Part172Good
import BstLean.Part216Weighted

/-! Fixed-order first-layer moments retain the dimension and row-order parameters. -/
namespace BstLean.Part220
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part172
open BstLean.Part161 (uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part53 (unitF53)
open BstLean.Part167 (latSq D1A1)

/-- The first-layer latitude statistic has an order64 bound from dimension four.
The row-order parameter is independent of the dimension. -/
theorem first_layer_moment64 {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (c : Ret n) (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ)
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2))
    (hadm : ∀ v, fr_Adm (xLat c s (unitF53 v)) (uHat c) (fun A => F A v))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ A v, normSq (F A v) ≤ B) :
    ∫⁻ v, ∫⁻ A, ENNReal.ofReal (|Tf c s F A v| ^ 64)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ∂stdGauss (Fin (n - 1)) ≤
        ENNReal.ofReal (((1 - s ^ 2) * fr_X n q B) ^ 64) := by
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have hz : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part168.stdGauss_zero (by omega)
    rw [ae_iff]; simpa using hz
  have h0 : 0 ≤ 1 - s ^ 2 := sub_nonneg.mpr hs
  calc
    _ ≤ ∫⁻ _v, ENNReal.ofReal (((1 - s ^ 2) * fr_X n q B) ^ 64)
        ∂stdGauss (Fin (n - 1)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hnz] with v hv
      have he : ∀ A, |Tf c s F A v| ^ 64 = (1 - s ^ 2) ^ 64 *
          latSq (vecMul (F A v) (D1A1 A (xLat c s (unitF53 v))))
            (uHat c) (dirW c (unitF53 v)) ^ 64 := by
        intro A
        rw [Even.pow_abs (by decide : Even 64)]
        simp only [Tf, mul_pow]
      simp_rw [he, ENNReal.ofReal_mul (pow_nonneg h0 64)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hm := frame_mom hn hq hc hs hv (fun A => F A v) (hadm v) hB0 (fun A => hB A v)
      rw [fr_X_pow hq B] at hm
      refine (mul_le_mul' le_rfl hm).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (pow_nonneg h0 64), ← mul_pow]
    _ = _ := by simp

/-- The same formula has no fixed numerical dimension floor. -/
lemma first_layer_constant_nonneg {n q : ℕ} (hn : 4 ≤ n) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ fr_X n q B := by
  unfold fr_X
  have hd : (0 : ℝ) < ((n - 1 - 1 : ℕ) : ℝ) - 1 := by
    have : 2 ≤ n - 1 - 1 := by omega
    have : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  positivity

#print axioms first_layer_moment64
#print axioms first_layer_constant_nonneg
end BstLean.Part220
