import BstLean.Part221Inner

/-! LJ1 for an actual first-layer matrix and an admissible coefficient field. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part134
open BstLean.Part167 BstLean.Part168
open BstLean.Part151 (mask)
open BstLean.Part212 (exactRadius)

theorem first_layer_active160 {n : ℕ} (hn : 4 ≤ n)
    {R2 : ℝ} (hR : ActiveRadialMoment160 n R2)
    {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1)
    (C : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hC : ∀ A, normSq (C A) ≤ 1)
    (hCinv : ∀ W W' : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ),
      (∀ i, (W i).1 = (W' i).1 ∧ (W i).2.1 = (W' i).2.1 ∧
        normSq (W i).2.2 = normSq (W' i).2.2) →
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W) =
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W')) :
    (∫⁻ A, ENNReal.ofReal (latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w ^ 80)
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤
      ENNReal.ofReal (exactRadius (n - 1 - 1) 80 ^ 160 * (2 / (n : ℝ)) ^ 80 * R2 ^ 80) := by
  have hn2 : 2 ≤ n := by omega
  have hm : 0 < mA n := by
    unfold mA
    exact pow_pos (by omega : 0 < n) 2
  let F := Aframe (m := mA n) (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs)
  let κ := fun (W : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) i =>
    sqrt (2 / (n : ℝ)) * C (F W) i * mask ((F W *ᵥ (s • u + cs • w)) i)
  have hg : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have hκ : ∀ W W', (∀ i, (W i).1 = (W' i).1 ∧ (W i).2.1 = (W' i).2.1 ∧
      normSq (W i).2.2 = normSq (W' i).2.2) → κ W = κ W' := by
    intro W W' he
    have hce := hCinv W W' he
    funext i
    dsimp [κ, F]
    rw [hce, (frame_reads (m := mA n) hn2 hu hw huw hsc hg W i).1,
      (frame_reads (m := mA n) hn2 hu hw huw hsc hg W' i).1, (he i).1]
  have hoff : ∀ W i, (W i).1 ≤ 0 → κ W i = 0 := by
    intro W i hi
    dsimp [κ, F]
    rw [(frame_reads (m := mA n) hn2 hu hw huw hsc hg W i).1,
      BstLean.Part151.mask_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sqrt_nonneg _) hi), mul_zero]
  have hB : ∀ W, normSq (κ W) ≤ 2 / (n : ℝ) := by
    intro W
    exact (normSq_coef_le hg (C (F W)) (F W *ᵥ (s • u + cs • w))).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hC (F W)) hg)
  rw [gaussMat_frame hn2 (2 / (n : ℝ)) (s • u + cs • w) (eprime hn2 u w s cs)]
  refine (lintegral_map_le _ (measurable_Aframe _ _ _).aemeasurable).trans ?_
  have he : ∀ W, ENNReal.ofReal
      (latSq (vecMul (C (F W)) (D1A1 (F W) (s • u + cs • w))) u w ^ 80) =
      ENNReal.ofReal (normSq (∑ i, κ W i • (W i).2.2) ^ 80) := by
    intro W
    rw [latSq_vecMul_frame hn2 hu hw huw hsc (2 / (n : ℝ)) W]
  change (∫⁻ W, ENNReal.ofReal
    (latSq (vecMul (C (F W)) (D1A1 (F W) (s • u + cs • w))) u w ^ 80) ∂_) ≤ _
  rw [lintegral_congr he]
  exact polar_active160 hm (by omega) κ hκ hoff hg hB
    (hR hm)

/-- One fixed admissible coefficient field has a direct first-layer charge. -/
theorem first_layer_active160_charge {n : ℕ} (hn : 4 ≤ n)
    {R2 : ℝ} (hR : ActiveRadialMoment160 n R2)
    {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1)
    (C : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hCm : Measurable C) (hC : ∀ A, normSq (C A) ≤ 1)
    (hCinv : ∀ W W' : Fin (mA n) → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ),
      (∀ i, (W i).1 = (W' i).1 ∧ (W i).2.1 = (W' i).2.1 ∧
        normSq (W i).2.2 = normSq (W' i).2.2) →
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W) =
      C (Aframe (2 / (n : ℝ)) (s • u + cs • w) (eprime (by omega) u w s cs) W'))
    {T : ℝ} (hT : 0 < T) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A | T < latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w} ≤
      (exactRadius (n - 1 - 1) 80 ^ 160 * (2 / (n : ℝ)) ^ 80 * R2 ^ 80) / T ^ 80 := by
  let F := fun A : Matrix (Fin (mA n)) (Fin n) ℝ =>
    ENNReal.ofReal (latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w ^ 80)
  have hD := measurable_D1A1 (s • u + cs • w)
  have hF : Measurable F := by
    dsimp [F]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    unfold latSq vecMul dotProduct
    fun_prop
  have hB : 0 ≤ exactRadius (n - 1 - 1) 80 ^ 160 *
      (2 / (n : ℝ)) ^ 80 * R2 ^ 80 :=
    mul_nonneg (mul_nonneg (Even.pow_nonneg (by decide) _)
      (Even.pow_nonneg (by decide) _)) (Even.pow_nonneg (by decide) _)
  have hmark := BstLean.Part149.markov_real
    (gaussMat (mA n) n (2 / (n : ℝ))) hF (pow_pos hT 80) hB
    (first_layer_active160 hn hR hu hw huw hsc C hC hCinv)
  refine (measureReal_mono ?_).trans hmark
  intro A hA
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (pow_nonneg hT.le 80)).mpr
  exact pow_lt_pow_left₀ hA hT.le (by norm_num)

end BstLean.Part221
