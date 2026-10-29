import BstLean.Part214World
import BstLean.Part214Integrable

/-! The sixth-moment to variance junction retains the exact World normalization. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137 BstLean.Part205

section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Cauchy--Schwarz bounds the fourth moment by the second and sixth moments. -/
theorem fourth_le_two_six {D : Ω → ℝ} (mD : Measurable D)
    (i2 : Integrable (fun x => D x ^ 2) P) (i6 : Integrable (fun x => D x ^ 6) P) :
    (∫ x, D x ^ 4 ∂P) ≤ √(∫ x, D x ^ 2 ∂P) * √(∫ x, D x ^ 6 ∂P) := by
  obtain ⟨_, hb⟩ := integral_mul_le_sqrt mD (mD.pow_const 3) i2
    (by simpa only [← pow_mul] using i6)
  have he : ∀ x, |D x| * |D x ^ 3| = D x ^ 4 := by
    intro x
    have hp : D x * D x ^ 3 = D x ^ 4 := by ring
    rw [← abs_mul, hp, abs_of_nonneg (by positivity)]
  simpa only [he, ← pow_mul] using hb

theorem fourth_le_energy {D : Ω → ℝ} (mD : Measurable D)
    (i2 : Integrable (fun x => D x ^ 2) P) (i6 : Integrable (fun x => D x ^ 6) P)
    {Q Δ F : ℝ} (hQ : 0 ≤ Q) (hΔ : 0 ≤ Δ) (hF : 0 ≤ F)
    (h2 : (∫ x, D x ^ 2 ∂P) ≤ Q * (Δ / 2))
    (h6 : √(∫ x, D x ^ 6 ∂P) ≤ Q * √Q * F) :
    (∫ x, D x ^ 4 ∂P) ≤ Q ^ 2 * √(Δ / 2) * F := by
  calc
    _ ≤ √(∫ x, D x ^ 2 ∂P) * √(∫ x, D x ^ 6 ∂P) := fourth_le_two_six mD i2 i6
    _ ≤ √(Q * (Δ / 2)) * (Q * √Q * F) :=
      mul_le_mul (sqrt_le_sqrt h2) h6 (sqrt_nonneg _) (sqrt_nonneg _)
    _ = _ := by
      rw [sqrt_mul hQ]
      have he := Real.mul_self_sqrt hQ
      calc
        _ = Q * (√Q * √Q) * √(Δ / 2) * F := by ring
        _ = _ := by rw [he]; ring

end

/-- The formula for `V_N` follows from a supplied sharp sixth-moment bound. -/
theorem paper_variance_of_sixth {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) {ε Δ F : ℝ}
    (hQ : 0 ≤ firstQ M₁) (hε : 0 ≤ 1 + ε) (hΔ : 0 ≤ Δ) (hF : 0 ≤ F)
    (hQup : firstQ M₁ ≤ (1 + ε) * (m : ℝ) / (N : ℝ))
    (hmean : worldDelta M₁ ≤ firstQ M₁ * Δ)
    (h6 : √(∫ ξ, rowDiscrepancy M₁ ξ ^ 6 ∂stdGauss (Fin m)) ≤
      firstQ M₁ * √(firstQ M₁) * F) :
    (4 * (N : ℝ) ^ 4 / (m : ℝ) ^ 3) *
      (∫ ξ, rowDiscrepancy M₁ ξ ^ 4 ∂stdGauss (Fin m)) ≤
      (4 * (N : ℝ) ^ 2 / (m : ℝ)) * (1 + ε) ^ 2 * √(Δ / 2) * F := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have i6 := rowDiscrepancy_six_integrable hN hm M₁
  have hrow := exact_row_distance (fun u => reluV (M₁.mulVec u)) hN
    (continuous_h1_u M₁) (h1bar M₁) (worldSigma M₁)
  have h2 : (∫ ξ, rowDiscrepancy M₁ ξ ^ 2 ∂stdGauss (Fin m)) ≤ firstQ M₁ * (Δ / 2) := by
    have he := hrow.2
    change 2 * (∫ ξ, rowDiscrepancy M₁ ξ ^ 2 ∂stdGauss (Fin m)) = worldDelta M₁ at he
    linarith
  have h4 := fourth_le_energy (measurable_rowDiscrepancy M₁) hrow.1 i6 hQ hΔ hF h2 h6
  have hQ2 := (sq_le_sq₀ hQ (by positivity : 0 ≤ (1 + ε) * (m : ℝ) / (N : ℝ))).mpr hQup
  calc
    _ ≤ (4 * (N : ℝ) ^ 4 / (m : ℝ) ^ 3) * (firstQ M₁ ^ 2 * √(Δ / 2) * F) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ (4 * (N : ℝ) ^ 4 / (m : ℝ) ^ 3) *
        (((1 + ε) * (m : ℝ) / (N : ℝ)) ^ 2 * √(Δ / 2) * F) := by
      gcongr
    _ = _ := by field_simp <;> ring

/-- The actual World charge follows from a charged first-layer event and its sharp sixth supply. -/
theorem direct_distance_from_sixth {n : ℕ} (hn : 4096 ≤ n)
    {E : Set (Matrix (Fin (mW n)) (Fin (2 * n)) ℝ)} (hE : MeasurableSet E)
    {ε Δ F Xc δ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hΔ : 0 ≤ Δ) (hF : 0 ≤ F)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + ε) * Δ < Xc)
    (hbad : (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).real Eᶜ ≤ δ)
    (hω : ∀ M₁ ∈ E, |firstOmega M₁ - 1| ≤ ε)
    (hTaylor : ∀ M₁ ∈ E, meanBound (normSq (h1bar M₁) / firstQ M₁)
      (worldT M₁) (worldNu M₁) ≤ Δ)
    (h6 : ∀ M₁ ∈ E, √(∫ ξ, rowDiscrepancy M₁ ξ ^ 6 ∂stdGauss (Fin (mW n))) ≤
      firstQ M₁ * √(firstQ M₁) * F) :
    (BstLean.Part136.hidGauss (2 * n) (mW n)).real (BstLean.Part140.goodDist n Xc)ᶜ ≤
      δ + ((4 * ((2 * n : ℕ) : ℝ) ^ 2 / (mW n : ℝ)) *
        (1 + ε) ^ 2 * √(Δ / 2) * F) /
        (Xc - ((2 * n : ℕ) : ℝ) * (1 + ε) * Δ) ^ 2 := by
  have hm : 1 ≤ mW n := by have := mW_ge hn; omega
  have hN : 1 ≤ 2 * n := by omega
  apply goodDist_direct_charge hn hE hX (by positivity) hbad
  · intro M₁ hM
    obtain ⟨hQ, _, hQu⟩ := energy_window hN hm M₁ hε1 (hω M₁ hM)
    exact normalized_mean_bound hn hm M₁ hQ hΔ hQu (hTaylor M₁ hM)
  · intro M₁ hM
    obtain ⟨hQ, _, hQu⟩ := energy_window hN hm M₁ hε1 (hω M₁ hM)
    have hmean : worldDelta M₁ ≤ firstQ M₁ * Δ := by
      have h := (world_mean_bound hn hm M₁ hQ).trans (hTaylor M₁ hM)
      exact (div_le_iff₀ hQ).mp h |>.trans_eq (mul_comm _ _)
    exact paper_variance_of_sixth hN hm M₁ hQ.le (by linarith) hΔ hF hQu hmean (h6 M₁ hM)

end BstLean.Part214
#print axioms BstLean.Part214.fourth_le_two_six
#print axioms BstLean.Part214.paper_variance_of_sixth
#print axioms BstLean.Part214.direct_distance_from_sixth
