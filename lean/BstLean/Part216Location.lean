import BstLean.Part184BF1
import BstLean.Part153Lp

/-! Sharp even location moments for the complete transverse Gaussian array. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130 BstLean.Part170

/-- Gaussian concentration bounds both signs of the centred function. -/
theorem gaussian_centred_even {ι : Type} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hL : EuLip f L) (p : ℕ) :
    ∫⁻ x, ENNReal.ofReal (|f x - ∫ y, f y ∂stdGauss ι| ^ (2 * p)) ∂stdGauss ι ≤
      ENNReal.ofReal (2 * L ^ (2 * p) * (2 ^ p * (p.factorial : ℝ))) := by
  have hLn : EuLip (fun x => -f x) L := by
    intro x y
    simpa only [neg_sub_neg, abs_sub_comm] using hL x y
  obtain ⟨iP, hP⟩ := BstLean.Part152.gaussConc_moment hL0 hL p
  obtain ⟨iN, hN⟩ := BstLean.Part152.gaussConc_moment hL0 hLn p
  have hI := BstLean.Part184.euLip_dev_pow_int hL0 hL p
  have heven : Even (2 * p) := ⟨p, by omega⟩
  have habs : ∀ x, |f x - ∫ y, f y ∂stdGauss ι| ^ (2 * p) =
      (f x - ∫ y, f y ∂stdGauss ι) ^ (2 * p) := fun x => heven.pow_abs _
  rw [← ofReal_integral_eq_lintegral_ofReal (hI.congr (Eventually.of_forall fun x => (habs x).symm))
    (Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) _)]
  apply ENNReal.ofReal_le_ofReal
  have hpt : ∀ x, |f x - ∫ y, f y ∂stdGauss ι| ^ (2 * p) ≤
      max (f x - ∫ y, f y ∂stdGauss ι) 0 ^ (2 * p) +
        max (-f x - ∫ y, -f y ∂stdGauss ι) 0 ^ (2 * p) := by
    intro x
    rw [integral_neg]
    set d := f x - ∫ y, f y ∂stdGauss ι
    have he : -f x - -∫ y, f y ∂stdGauss ι = -d := by dsimp [d]; ring
    rw [he]
    rcases le_total 0 d with hd | hd
    · rw [abs_of_nonneg hd, max_eq_left hd]
      exact le_add_of_nonneg_right (pow_nonneg (le_max_right _ _) _)
    · rw [abs_of_nonpos hd, max_eq_left (neg_nonneg.mpr hd)]
      exact le_add_of_nonneg_left (pow_nonneg (le_max_right _ _) _)
  have h := integral_mono (hI.congr (Eventually.of_forall fun x => (habs x).symm))
    (iP.add iN) hpt
  change (∫ x, |f x - ∫ y, f y ∂stdGauss ι| ^ (2 * p) ∂stdGauss ι) ≤
    ∫ x, max (f x - ∫ y, f y ∂stdGauss ι) 0 ^ (2 * p) +
      max (-f x - ∫ y, -f y ∂stdGauss ι) 0 ^ (2 * p) ∂stdGauss ι at h
  rw [integral_add (f := fun x => max (f x - ∫ y, f y ∂stdGauss ι) 0 ^ (2 * p))
    (g := fun x => max (-f x - ∫ y, -f y ∂stdGauss ι) 0 ^ (2 * p)) iP iN] at h
  linarith

variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- Conditional subtraction centres the complete transverse fluctuation. -/
theorem location_mean_zero {a : V → Fin m → ℝ} (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ)
    (b ψ : Fin m → ℝ) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ N, (flE μ a h M₀ b ψ κ N -
      ∫ N', flE μ a h M₀ b ψ κ N' ∂gaussMat m m t) ∂gaussMat m m t = 0 := by
  have hi : Integrable (flE μ a h M₀ b ψ κ) (gaussMat m m t) := by
    rw [gaussMat_eq]
    apply (integrable_map_measure
      (continuous_flE ha hK hΛ0 hΛ h M₀ b ψ κ).aestronglyMeasurable
      (measurable_matOf t).aemeasurable).mpr
    exact BstLean.Part170.euLip_integrable (by positivity)
      (flE_euLip ha hK hΛ0 hΛ h M₀ b ψ κ ht)
  rw [integral_sub hi (integrable_const _)]
  simp

/-- The location fluctuation has the paper concentration moment at every even order.
The centre weights stay fixed until their norm cancels in the normalization. -/
theorem location_even {a : V → Fin m → ℝ} (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ)
    (b ψ : Fin m → ℝ) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : ℕ) :
    ∫⁻ N, ENNReal.ofReal (|flE μ a h M₀ b ψ κ N -
      ∫ N', flE μ a h M₀ b ψ κ N' ∂gaussMat m m t| ^ (2 * p)) ∂gaussMat m m t ≤
      ENNReal.ofReal (2 * (|κ| * sqrt (normSq b) * sqrt (t * Λ) / 2) ^ (2 * p) *
        (2 ^ p * (p.factorial : ℝ))) := by
  have hc := continuous_flE ha hK hΛ0 hΛ h M₀ b ψ κ
  have mo := measurable_matOf (m := m) t
  have hint : ∫ N', flE μ a h M₀ b ψ κ N' ∂gaussMat m m t =
      ∫ ξ, flE μ a h M₀ b ψ κ (matOf t ξ) ∂stdGauss (Fin m × Fin m) := by
    rw [gaussMat_eq, integral_map mo.aemeasurable hc.aestronglyMeasurable]
  rw [hint, gaussMat_eq, lintegral_map
    (f := fun N => ENNReal.ofReal (|flE μ a h M₀ b ψ κ N -
      ∫ ξ, flE μ a h M₀ b ψ κ (matOf t ξ) ∂stdGauss (Fin m × Fin m)| ^ (2 * p)))
    (ENNReal.measurable_ofReal.comp (((hc.measurable.sub_const _).abs).pow_const (2 * p))) mo]
  exact gaussian_centred_even (by positivity) (flE_euLip ha hK hΛ0 hΛ h M₀ b ψ κ ht) p

/-- The location order24 supply uses the same conditional distribution and centre. -/
theorem location_order24 {a : V → Fin m → ℝ} (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ)
    (b ψ : Fin m → ℝ) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ N, ENNReal.ofReal (|flE μ a h M₀ b ψ κ N -
      ∫ N', flE μ a h M₀ b ψ κ N' ∂gaussMat m m t| ^ 24) ∂gaussMat m m t ≤
      ENNReal.ofReal (2 * (|κ| * sqrt (normSq b) * sqrt (t * Λ) / 2) ^ 24 *
        (2 ^ 12 * ((12 : ℕ).factorial : ℝ))) :=
  location_even ha hK hΛ0 hΛ h M₀ b ψ κ ht 12

#print axioms gaussian_centred_even
#print axioms location_mean_zero
#print axioms location_even
#print axioms location_order24
end BstLean.Part216
