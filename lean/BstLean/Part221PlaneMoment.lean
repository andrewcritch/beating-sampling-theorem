import BstLean.Part221PlaneCount
import BstLean.Part221EigenSupply
import BstLean.Part209MomentTools

/-! The first sharp gated-plane moment in plane-b, under the actual plane distribution. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part209
open BstLean.Part151 (mask)

theorem planeEigen_moment_count {n P : ℕ} (hn : 1 ≤ n) (hP : 1 ≤ P) :
    (∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (planeEigen ξ₁ ξ₂ ^ (2 * P))
      ∂stdGauss (Fin (n ^ 2)) ∂stdGauss (Fin (n ^ 2))) ≤
      ENNReal.ofReal ((√((n : ℝ) ^ 2 / 2 + activeB n P) + √2 +
        BstLean.Part152.gaussMomConst (2 * P)) ^ (4 * P)) := by
  let Φ : (Fin (n ^ 2) → Bool) ×
      (Fin (n ^ 2) → Matrix (Fin 2) (Fin 2) ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (outerPlaneEigen q.1 q.2 ^ (2 * P))
  have hΦ : Measurable Φ := (measurable_outerPlaneEigen.pow_const _).ennreal_ofReal
  have hh : (![1,0] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hd := halfGate_array_even_lintegral hh
    (show Measurable (outerProduct (d := 2)) by unfold outerProduct; fun_prop)
    (by intro z; funext i j; simp [outerProduct]) Φ hΦ
  change (∫⁻ Z, Φ ((fun i => halfGate ![1,0] (Z i)), (fun i => outerProduct (Z i)))
    ∂planeRows (n ^ 2)) = _ at hd
  let Ψ : (Fin (n ^ 2) → ℝ) × (Fin (n ^ 2) → ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (planeEigen q.1 q.2 ^ (2 * P))
  have hΨ : Measurable Ψ := (measurable_planeEigen.pow_const _).ennreal_ofReal
  have hc : (∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (planeEigen ξ₁ ξ₂ ^ (2 * P))
      ∂stdGauss (Fin (n ^ 2)) ∂stdGauss (Fin (n ^ 2))) =
      ∫⁻ Z, ENNReal.ofReal (planeEigen (fun i => Z i 0) (fun i => Z i 1) ^ (2 * P))
        ∂planeRows (n ^ 2) := by
    rw [← lintegral_prod _ hΨ.aemeasurable, ← plane_coordinates_map,
      lintegral_map hΨ (by fun_prop)]
  rw [hc]
  have hgate : ∀ Z : Fin (n ^ 2) → Fin 2 → ℝ,
      ENNReal.ofReal (planeEigen (fun i => Z i 0) (fun i => Z i 1) ^ (2 * P)) =
        Φ ((fun i => halfGate ![1,0] (Z i)), (fun i => outerProduct (Z i))) := by
    intro Z
    dsimp only [Φ]
    rw [outerPlaneEigen_gated]
  simp_rw [hgate]
  rw [hd]
  have hinner : ∀ Z : Fin (n ^ 2) → Fin 2 → ℝ,
      (∫⁻ Z', Φ ((fun i => halfGate ![1,0] (Z i)), (fun i => outerProduct (Z' i)))
        ∂planeRows (n ^ 2)) ≤ ENNReal.ofReal
        ((√(∑ i, mask (Z i 0)) + √2 + BstLean.Part152.gaussMomConst (2 * P)) ^ (4 * P)) := by
    intro Z
    dsimp only [Φ]
    simp_rw [outerPlaneEigen_selected]
    rw [planeRows_gaussMat]
    have h := selected_plane_moment (show 1 ≤ 2 * P by omega)
      (fun i => if halfGate ![1,0] (Z i) then 1 else 0)
      (fun i => by cases halfGate ![1,0] (Z i) <;> simp)
    have he : ∀ i, (if halfGate ![1,0] (Z i) then (1 : ℝ) else 0) = mask (Z i 0) := by
      intro i
      simp only [halfGate_first]
      by_cases hi : 0 < Z i 0 <;> simp [mask, hi]
    simp only [he, show 2 * (2 * P) = 4 * P by omega] at h ⊢
    exact h
  refine (lintegral_mono hinner).trans ?_
  let f : (Fin (n ^ 2) → ℝ) → ℝ≥0∞ := fun g => ENNReal.ofReal
    ((√(∑ i, mask (g i)) + √2 + BstLean.Part152.gaussMomConst (2 * P)) ^ (4 * P))
  have hf : Measurable f := by
    have hmask := BstLean.Part151.measurable_mask
    dsimp only [f]
    fun_prop
  change (∫⁻ Z, f (fun i => Z i 0) ∂planeRows (n ^ 2)) ≤ _
  rw [← lintegral_map hf (by fun_prop), plane_first_map]
  obtain ⟨hi, hb⟩ := active_sqrt_shift_moment hn hP
    (add_nonneg (sqrt_nonneg 2) (BstLean.Part152.gaussMomConst_nonneg (2 * P)))
  have h := lintegral_ofReal_le_of_integral_le
    (fun g => pow_nonneg (add_nonneg (sqrt_nonneg _) (add_nonneg (sqrt_nonneg 2)
      (BstLean.Part152.gaussMomConst_nonneg (2 * P)))) _) hi hb
  simpa only [f, add_assoc] using h

noncomputable def countPlaneSquared160 (n : ℕ) : ℝ :=
  (√((n : ℝ) ^ 2 / 2 + activeB n 40) + √2 + BstLean.Part152.gaussMomConst 80) ^ 2

theorem planeEigenMoment160_count {n : ℕ} (hn : 1 ≤ n) :
    PlaneEigenMoment160 (mA n) (countPlaneSquared160 n) := by
  have h := planeEigen_moment_count hn (by norm_num : 1 ≤ 40)
  simp only [PlaneEigenMoment160, mA, countPlaneSquared160, ← pow_mul,
    show 2 * 40 = 80 by rfl, show 4 * 40 = 160 by rfl, show 2 * 80 = 160 by rfl] at h ⊢
  exact h

lemma countPlaneSquared160_pos (n : ℕ) : 0 < countPlaneSquared160 n := by
  unfold countPlaneSquared160
  have := BstLean.Part152.gaussMomConst_nonneg 80
  have := sqrt_nonneg ((n : ℝ) ^ 2 / 2 + activeB n 40)
  positivity

end BstLean.Part221
