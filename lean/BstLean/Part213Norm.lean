import BstLean.Part213Rows
import BstLean.Part153Lp

/-! Row-averaged Taylor transfer with the centred correction inside the
location square root. All moments use the same distribution. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part186.RA (sum_split)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A finite moment bound is a bound on the corresponding `Lᵏ` norm. -/
lemma moment_norm_bound {f : X → ℝ} (hf : Measurable f) {k : ℕ} (hk : k ≠ 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hM : ∫⁻ x, ENNReal.ofReal (|f x| ^ k) ∂μ ≤ ENNReal.ofReal (A ^ k)) :
    eLpNorm f (k : ℝ≥0∞) μ ≤ ENNReal.ofReal A := by
  apply (ENNReal.pow_le_pow_left_iff hk).mp
  rw [BstLean.Part153.eLpNorm_nat_pow hk hf.aestronglyMeasurable,
    ← ENNReal.ofReal_pow hA]
  exact hM

/-- Minkowski combines two supplied moments, including zero bounds. -/
theorem moment_minkowski {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {k : ℕ} (hk : 1 ≤ k) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∫⁻ x, ENNReal.ofReal (|f x| ^ k) ∂μ ≤ ENNReal.ofReal (A ^ k))
    (hG : ∫⁻ x, ENNReal.ofReal (|g x| ^ k) ∂μ ≤ ENNReal.ofReal (B ^ k)) :
    ∫⁻ x, ENNReal.ofReal (|f x + g x| ^ k) ∂μ ≤ ENNReal.ofReal ((A + B) ^ k) := by
  have hk0 : k ≠ 0 := by omega
  have hnorm := eLpNorm_add_le (f := f) (g := g) (μ := μ)
    (show (1 : ℝ≥0∞) ≤ k by exact_mod_cast hk)
  have hsum : eLpNorm (f + g) (k : ℝ≥0∞) μ ≤ ENNReal.ofReal (A + B) := by
    refine hnorm.trans ?_
    rw [ENNReal.ofReal_add hA hB]
    exact add_le_add (moment_norm_bound hf hk0 hA hF) (moment_norm_bound hg hk0 hB hG)
  have hpow := pow_le_pow_left' hsum k
  rw [BstLean.Part153.eLpNorm_nat_pow hk0 (hf.add hg).aestronglyMeasurable,
    ← ENNReal.ofReal_pow (add_nonneg hA hB)] at hpow
  exact hpow

variable {ρ : Measure X} [IsProbabilityMeasure ρ]

/-- Row averaging adds its mean and its centred norm before taking a power. -/
theorem row_average_minkowski {m k : ℕ} (hk : 1 ≤ k) {f : X → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {mean correction : ℝ}
    (hmean : 0 ≤ mean) (hcorrection : 0 ≤ correction)
    (hC : ∫⁻ y, ENNReal.ofReal (|∑ j : Fin m, (f (y j) - mean)| ^ k)
      ∂(Measure.pi fun _ : Fin m => ρ) ≤ ENNReal.ofReal (correction ^ k)) :
    ∫⁻ y, ENNReal.ofReal ((∑ j : Fin m, f (y j)) ^ k)
      ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (((m : ℝ) * mean + correction) ^ k) := by
  have hZ : Measurable (fun y : Fin m → X => ∑ j, (f (y j) - mean)) :=
    Finset.measurable_sum _ fun j _ => (hf.comp (measurable_pi_apply j)).sub_const mean
  have hm : 0 ≤ (m : ℝ) * mean := by positivity
  have hA : ∫⁻ y : Fin m → X, ENNReal.ofReal (|(m : ℝ) * mean| ^ k)
      ∂(Measure.pi fun _ : Fin m => ρ) ≤ ENNReal.ofReal (((m : ℝ) * mean) ^ k) := by
    simp [abs_of_nonneg hm]
  have h := moment_minkowski measurable_const hZ hk hm hcorrection hA hC
  refine (le_of_eq (lintegral_congr fun y => ?_)).trans h
  rw [← sum_split, abs_of_nonneg (Finset.sum_nonneg fun j _ => hf0 _)]

/-- The location RA16 structure keeps the centred correction inside the root.
The correction premise concerns the full row product and no extra event. -/
theorem location_RA16 {m : ℕ} {β : X → ℝ} (hβ : Measurable β)
    {B : (Fin m → X) → ℝ} {N A2 A16 r : ℝ}
    (hN : 0 ≤ N) (hA2 : 0 ≤ A2) (hr : 0 ≤ r)
    (hpoint : ∀ y, B y ^ 16 ≤ N ^ 8 * (∑ j, β (y j) ^ 2) ^ 8)
    (hC : ∫⁻ y, ENNReal.ofReal
      (|∑ j : Fin m, (β (y j) ^ 2 - A2 ^ 2)| ^ 8)
        ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (((m : ℝ) * r * A16 ^ 2) ^ 8)) :
    ∫⁻ y, ENNReal.ofReal (B y ^ 16) ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (N ^ 8 * (m : ℝ) ^ 8 * (A2 ^ 2 + r * A16 ^ 2) ^ 8) := by
  have hM := row_average_minkowski (by norm_num : 1 ≤ 8) (hβ.pow_const 2)
    (fun x => sq_nonneg _) (sq_nonneg A2)
    (show 0 ≤ (m : ℝ) * r * A16 ^ 2 by positivity) hC
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (N ^ 8) *
        ENNReal.ofReal ((∑ j : Fin m, β (y j) ^ 2) ^ 8)
          ∂(Measure.pi fun _ : Fin m => ρ) := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [← ENNReal.ofReal_mul (pow_nonneg hN 8)]
      exact ENNReal.ofReal_le_ofReal (hpoint y)
    _ = ENNReal.ofReal (N ^ 8) * ∫⁻ y,
        ENNReal.ofReal ((∑ j : Fin m, β (y j) ^ 2) ^ 8)
          ∂(Measure.pi fun _ : Fin m => ρ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (N ^ 8) *
        ENNReal.ofReal (((m : ℝ) * A2 ^ 2 + (m : ℝ) * r * A16 ^ 2) ^ 8) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hN 8)]
      congr 1
      ring

/-- The energy RA16 structure adds the mean and the centred correction. -/
theorem energy_RA16 {m : ℕ} {β : X → ℝ} (hβ : Measurable β)
    (hβ0 : ∀ x, 0 ≤ β x) {B : (Fin m → X) → ℝ} {A1 A16 r : ℝ}
    (hA1 : 0 ≤ A1) (hA16 : 0 ≤ A16) (hr : 0 ≤ r)
    (hpoint : ∀ y, B y ^ 16 ≤ (∑ j, β (y j)) ^ 16)
    (hC : ∫⁻ y, ENNReal.ofReal (|∑ j : Fin m, (β (y j) - A1)| ^ 16)
      ∂(Measure.pi fun _ : Fin m => ρ) ≤
        ENNReal.ofReal (((m : ℝ) * r * A16) ^ 16)) :
    ∫⁻ y, ENNReal.ofReal (B y ^ 16) ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal ((m : ℝ) ^ 16 * (A1 + r * A16) ^ 16) := by
  have hM := row_average_minkowski (by norm_num : 1 ≤ 16) hβ hβ0 hA1
    (show 0 ≤ (m : ℝ) * r * A16 by positivity) hC
  refine (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpoint y)).trans ?_
  refine hM.trans (le_of_eq ?_)
  congr 1
  ring

#print axioms moment_minkowski
#print axioms row_average_minkowski
#print axioms location_RA16
#print axioms energy_RA16
end BstLean.Part213
