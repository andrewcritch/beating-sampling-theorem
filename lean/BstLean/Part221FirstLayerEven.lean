import BstLean.Part221FirstLayer
import BstLean.Part221PolarEven

/-! The actual first-layer bound permits order 1664 as well as order 160. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part134
open BstLean.Part167 BstLean.Part168
open BstLean.Part151 (mask)
open BstLean.Part212 (exactRadius)

theorem first_layer_active_even {n j : ℕ} (hj : 1 ≤ j) (hn : 4 ≤ n)
    {M : ℝ}
    (hR : ∀ hm : 0 < mA n,
      (∫⁻ Z, ∫⁻ G, ENNReal.ofReal (activeRadius (d := n - 1 - 1) hm Z G ^ (2 * j))
        ∂Measure.pi (fun _ : Fin (mA n) => BstLean.Part29.stdGauss (Fin (n - 1 - 1)))
        ∂Measure.pi (fun _ : Fin (mA n) => gaussianReal 0 1)) ≤ ENNReal.ofReal M)
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
    (∫⁻ A, ENNReal.ofReal (latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w ^ j)
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤
      ENNReal.ofReal (exactRadius (n - 1 - 1) j ^ (2 * j) * (2 / (n : ℝ)) ^ j * M) := by
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
      (latSq (vecMul (C (F W)) (D1A1 (F W) (s • u + cs • w))) u w ^ j) =
      ENNReal.ofReal (normSq (∑ i, κ W i • (W i).2.2) ^ j) := by
    intro W
    rw [latSq_vecMul_frame hn2 hu hw huw hsc (2 / (n : ℝ)) W]
  change (∫⁻ W, ENNReal.ofReal
    (latSq (vecMul (C (F W)) (D1A1 (F W) (s • u + cs • w))) u w ^ j) ∂_) ≤ _
  rw [lintegral_congr he]
  exact polar_active_even hj hm (by omega) κ hκ hoff hg hB
    (hR hm)

noncomputable def firstLayerMomentMajorant (n j : ℕ) : ℝ :=
  let a := automaticRadius (mA n) (n - 1 - 1)
  exactRadius (n - 1 - 1) j ^ (2 * j) * (2 / (n : ℝ)) ^ j *
    factorialMoment (2 * j) a (a - ((n - 1 - 1 : ℕ) : ℝ) / a)

theorem first_layer_automatic_even {n j : ℕ} (hj : 1 ≤ j) (hn : 4 ≤ n)
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
    (∫⁻ A, ENNReal.ofReal (latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w ^ j)
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤ ENNReal.ofReal (firstLayerMomentMajorant n j) := by
  have hm : 0 < mA n := by unfold mA; exact pow_pos (by omega : 0 < n) 2
  obtain ⟨ha, ha2, hcal⟩ := automaticRadius_guards hm (by omega : 1 ≤ n - 1 - 1)
  apply first_layer_active_even hj hn _ hu hw huw hsc C hC hCinv
  intro hm'
  exact activeRadius_factorial_moment hm' (by omega) ha ha2 hcal (2 * j)

end BstLean.Part221
