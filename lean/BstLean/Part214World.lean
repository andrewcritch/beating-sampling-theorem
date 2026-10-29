import BstLean.Part214Charge
import BstLean.Part214Variance
import BstLean.Part205WorldMean
import BstLean.Part214Norm

/-! Direct distance at a variable threshold for the original World hidden distribution. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part136 BstLean.Part137
open BstLean.Part205

noncomputable def normalizedDistance (N m : ℕ) (θ : HidParam N m) : ℝ :=
  (N : ℝ) ^ 2 / 2 * BstLean.Part140.dist2 N m θ

noncomputable def normalizedMean {N m : ℕ} (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  (N : ℝ) ^ 2 / (m : ℝ) * worldDelta M₁

theorem firstQ_eq_omega {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    firstQ M₁ = (m : ℝ) / (N : ℝ) * firstOmega M₁ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [firstQ_rows hN hm]
  unfold firstOmega
  field_simp <;> ring

/-- The norm part of E1 supplies positive energy and both energy bounds. -/
theorem energy_window {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) {ε : ℝ} (hε : ε < 1)
    (hω : |firstOmega M₁ - 1| ≤ ε) :
    0 < firstQ M₁ ∧
      (1 - ε) * (m : ℝ) / (N : ℝ) ≤ firstQ M₁ ∧
      firstQ M₁ ≤ (1 + ε) * (m : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := abs_le.mp hω
  have hl : 1 - ε ≤ firstOmega M₁ := by linarith
  have hu : firstOmega M₁ ≤ 1 + ε := by linarith
  rw [firstQ_eq_omega hN hm]
  have hl' := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (m : ℝ) / (N : ℝ))
  have hu' := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ (m : ℝ) / (N : ℝ))
  refine ⟨mul_pos (by positivity) (by linarith), ?_, ?_⟩
  · convert hl' using 1 <;> ring
  · convert hu' using 1 <;> ring

lemma normalizedDistance_measurable {N m : ℕ} (hN : 1 ≤ N) :
    Measurable (normalizedDistance N m) :=
  (BstLean.Part140.measurable_dist2 hN).const_mul _

theorem normalized_mean_eq {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    (∫ M₂, normalizedDistance N m (M₁, M₂) ∂gaussMat m m (2 / (m : ℝ))) =
      normalizedMean M₁ := by
  unfold normalizedDistance normalizedMean
  rw [integral_const_mul, (exact_conditional_distance_paper hN hm M₁).2]
  ring

theorem normalized_variance_le {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun M₂ => (normalizedDistance N m (M₁, M₂) - normalizedMean M₁) ^ 2)
      (gaussMat m m (2 / (m : ℝ))) ∧
    (∫ M₂, (normalizedDistance N m (M₁, M₂) - normalizedMean M₁) ^ 2
      ∂gaussMat m m (2 / (m : ℝ))) ≤
      (4 * (N : ℝ) ^ 4 / (m : ℝ) ^ 3) *
        (∫ ξ, rowDiscrepancy M₁ ξ ^ 4 ∂stdGauss (Fin m)) := by
  obtain ⟨hi, hv⟩ := conditional_variance_paper hN hm M₁
  have he : ∀ M₂, (normalizedDistance N m (M₁, M₂) - normalizedMean M₁) ^ 2 =
      ((N : ℝ) ^ 2 / 2) ^ 2 *
        (BstLean.Part140.dist2 N m (M₁, M₂) - 2 / (m : ℝ) * worldDelta M₁) ^ 2 := by
    intro M₂
    unfold normalizedDistance normalizedMean
    ring
  simp_rw [he]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hv (sq_nonneg ((N : ℝ) ^ 2 / 2))
  convert h using 1 <;> dsimp [rowDiscrepancy] <;> ring

/-- S08 supplies the actual mean from a bound for `Q` and the Taylor expression. -/
theorem normalized_mean_bound {n m : ℕ} (hn : 4096 ≤ n) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin (2 * n)) ℝ) {ε D : ℝ}
    (hQ : 0 < firstQ M₁) (hD : 0 ≤ D)
    (hQup : firstQ M₁ ≤ (1 + ε) * (m : ℝ) / ((2 * n : ℕ) : ℝ))
    (hTaylor : meanBound (normSq (h1bar M₁) / firstQ M₁)
      (worldT M₁) (worldNu M₁) ≤ D) :
    normalizedMean M₁ ≤ ((2 * n : ℕ) : ℝ) * (1 + ε) * D := by
  have hN : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (show 0 < 2 * n by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hΔ : worldDelta M₁ ≤ firstQ M₁ * D := by
    have h := (world_mean_bound hn hm M₁ hQ).trans hTaylor
    exact (div_le_iff₀ hQ).mp h |>.trans_eq (mul_comm _ _)
  unfold normalizedMean
  calc
    _ ≤ ((2 * n : ℕ) : ℝ) ^ 2 / (m : ℝ) * (firstQ M₁ * D) :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    _ ≤ ((2 * n : ℕ) : ℝ) ^ 2 / (m : ℝ) *
        (((1 + ε) * (m : ℝ) / ((2 * n : ℕ) : ℝ)) * D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQup hD) (by positivity)
    _ = _ := by field_simp <;> ring

/-- The direct charge is for exactly the existing non-strict `goodDist` event. -/
theorem goodDist_direct_charge {n : ℕ} (hn : 4096 ≤ n)
    {E : Set (Matrix (Fin (mW n)) (Fin (2 * n)) ℝ)} (hE : MeasurableSet E)
    {Xc μ V δ : ℝ} (hX : μ < Xc) (hV : 0 ≤ V)
    (hbad : (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).real Eᶜ ≤ δ)
    (hmean : ∀ M₁ ∈ E, normalizedMean M₁ ≤ μ)
    (hfour : ∀ M₁ ∈ E,
      (4 * ((2 * n : ℕ) : ℝ) ^ 4 / (mW n : ℝ) ^ 3) *
        (∫ ξ, rowDiscrepancy M₁ ξ ^ 4 ∂stdGauss (Fin (mW n))) ≤ V) :
    (hidGauss (2 * n) (mW n)).real (BstLean.Part140.goodDist n Xc)ᶜ ≤
      δ + V / (Xc - μ) ^ 2 := by
  have hm : 1 ≤ mW n := by have := mW_ge hn; omega
  have hN : 1 ≤ 2 * n := by omega
  have hNpos : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (show 0 < 2 * n by omega)
  have he : (BstLean.Part140.goodDist n Xc)ᶜ =
      {θ | Xc < normalizedDistance (2 * n) (mW n) θ} := by
    ext θ
    simp only [BstLean.Part140.goodDist, mem_compl_iff, mem_setOf_eq, not_le]
    unfold normalizedDistance
    have heq : 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) =
        Xc / (((2 * n : ℕ) : ℝ) ^ 2 / 2) := by field_simp <;> ring
    rw [heq, div_lt_iff₀ (by positivity)]
    rw [mul_comm]
  rw [he]
  apply conditional_distance_charge _ _ hE (normalizedDistance_measurable hN) hX hV hbad
  · exact fun M₁ _ => (normalized_variance_le hN hm M₁).1
  · exact hmean
  · exact fun M₁ hM => (normalized_variance_le hN hm M₁).2.trans (hfour M₁ hM)

end BstLean.Part214
#print axioms BstLean.Part214.normalized_variance_le
#print axioms BstLean.Part214.normalized_mean_bound
#print axioms BstLean.Part214.goodDist_direct_charge
