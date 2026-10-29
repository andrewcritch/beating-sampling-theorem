import BstLean.Part221FirstLayer
import BstLean.Part221CountEvent

/-! A closed LJ1 charge for one fixed admissible coefficient field. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part134 BstLean.Part167 BstLean.Part168 BstLean.Part212

noncomputable def firstLayerSquared160 (n : ℕ) (R2 : ℝ) : ℝ :=
  exactRadius (n - 1 - 1) 80 ^ 2 * (2 / (n : ℝ)) * R2

noncomputable def firstLayerThreshold160 (n : ℕ) (R2 : ℝ) : ℝ :=
  (10000 : ℝ) ^ (80 : ℝ)⁻¹ * firstLayerSquared160 n R2

lemma firstLayerSquared160_pos {n : ℕ} (hn : 4 ≤ n) {R2 : ℝ} (hR : 0 < R2) :
    0 < firstLayerSquared160 n R2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (2 : ℝ) ≤ (n - 1 - 1 : ℕ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hr : 0 < exactRadius (n - 1 - 1) 80 := by
    unfold exactRadius
    exact div_pos (rpow_pos_of_pos (radialProduct_pos (by omega) 80) _)
      (sqrt_pos.mpr (by linarith))
  unfold firstLayerSquared160
  positivity

theorem first_layer_active160_oneTenThousand {n : ℕ} (hn : 4 ≤ n)
    {R2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2)
    {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1)
    (C : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hCm : Measurable C) (hC : ∀ A, normSq (C A) ≤ 1)
    (hCinv : ∀ W W' : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ),
      (∀ i, (W i).1 = (W' i).1 ∧ (W i).2.1 = (W' i).2.1 ∧
        normSq (W i).2.2 = normSq (W' i).2.2) →
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W) =
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W')) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A | firstLayerThreshold160 n R2 < latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w}
      ≤ 1 / 10000 := by
  have hB := firstLayerSquared160_pos hn hR0
  have hT : 0 < firstLayerThreshold160 n R2 := by
    unfold firstLayerThreshold160
    positivity
  have h := first_layer_active160_charge hn hR hu hw huw hsc C hCm hC hCinv hT
  have hnum : exactRadius (n - 1 - 1) 80 ^ 160 * (2 / (n : ℝ)) ^ 80 * R2 ^ 80 =
      firstLayerSquared160 n R2 ^ 80 := by
    unfold firstLayerSquared160
    rw [mul_pow, mul_pow, ← pow_mul]
  have hpow : firstLayerThreshold160 n R2 ^ 80 = 10000 * firstLayerSquared160 n R2 ^ 80 := by
    unfold firstLayerThreshold160
    rw [mul_pow]
    have hr : ((10000 : ℝ) ^ (80 : ℝ)⁻¹) ^ (80 : ℕ) = 10000 := by
      simpa only [Nat.cast_ofNat] using rpow_inv_natCast_pow
        (by norm_num : (0 : ℝ) ≤ 10000) (by norm_num : (80 : ℕ) ≠ 0)
    rw [hr]
  rw [hnum, hpow] at h
  refine h.trans_eq ?_
  field_simp [pow_ne_zero 80 hB.ne']

/-- This event is for the displayed field C, not a simultaneous event over all fields. -/
theorem first_layer_automatic160_oneTenThousand {n : ℕ} (hn : 8000 ≤ n)
    {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1)
    (C : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hCm : Measurable C) (hC : ∀ A, normSq (C A) ≤ 1)
    (hCinv : ∀ W W' : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ),
      (∀ i, (W i).1 = (W' i).1 ∧ (W i).2.1 = (W' i).2.1 ∧
        normSq (W i).2.2 = normSq (W' i).2.2) →
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W) =
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W')) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A | firstLayerThreshold160 n (automaticRadiusSquared160 n) <
        latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w} ≤ 1 / 10000 :=
  first_layer_active160_oneTenThousand (by omega) (automaticRadiusSquared160_properties hn).1
    (automatic_activeRadialMoment160 hn) hu hw huw hsc C hCm hC hCinv

end BstLean.Part221
