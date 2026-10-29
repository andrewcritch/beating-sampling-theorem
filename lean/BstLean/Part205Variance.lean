import BstLean.Part205Conditional
import BstLean.Part205Fourth

/-! Conditional variance from complete second-layer row independence. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137

lemma rows_variance_le {m k : ℕ} (v : ℝ) (f : (Fin k → ℝ) → ℝ)
    (hf : Measurable f)
    (hf2 : Integrable (fun ξ => f (√v • ξ) ^ 2) (stdGauss (Fin k))) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      ((∑ i, f (rowOf i M)) - (m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin k)) ^ 2)
      (gaussMat m k v) ∧
    (∫ M : Matrix (Fin m) (Fin k) ℝ,
      ((∑ i, f (rowOf i M)) - (m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin k)) ^ 2
      ∂gaussMat m k v) ≤ (m : ℝ) * ∫ ξ, f (√v • ξ) ^ 2 ∂stdGauss (Fin k) := by
  classical
  have hfi := ((memLp_two_iff_integrable_sq
    (hf.comp (measurable_const_smul _)).aestronglyMeasurable).mpr hf2).integrable one_le_two
  have hir : ∀ i : Fin m, Integrable (fun M => f (rowOf i M)) (gaussMat m k v) :=
    fun i => (row_integrable_iff v i hf).mpr hfi
  have hi : Integrable (fun M => ∑ i, f (rowOf i M)) (gaussMat m k v) :=
    integrable_finsetSum _ fun i _ => hir i
  have he : (∫ M : Matrix (Fin m) (Fin k) ℝ, ∑ i, f (rowOf i M) ∂gaussMat m k v) =
      (m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin k) := by
    rw [integral_finsetSum _ (fun i _ => hir i)]
    simp_rw [row_integral v _ hf]
    simp
  obtain ⟨hi2, he2⟩ := rows_sum_sq (m := m) v f hf hf2
  obtain ⟨hiv, hev⟩ := integral_sq_sub_const hi hi2
    ((m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin k))
  refine ⟨hiv, ?_⟩
  rw [hev, he, he2]
  have hn := mul_nonneg (Nat.cast_nonneg m)
    (sq_nonneg (∫ ξ, f (√v • ξ) ∂stdGauss (Fin k)))
  nlinarith [hn]

variable {N m : ℕ}

/-- The scaled row discrepancy has the exact conditional variance price `4/m`. -/
theorem conditional_variance_scaled (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun M₂ => (BstLean.Part140.dist2 N m (M₁, M₂) - conditionalDelta M₁) ^ 2)
      (gaussMat m m (2 / (m : ℝ))) ∧
    (∫ M₂, (BstLean.Part140.dist2 N m (M₁, M₂) - conditionalDelta M₁) ^ 2
      ∂gaussMat m m (2 / (m : ℝ))) ≤
      4 / (m : ℝ) * (∫ ξ, (rowMean (scaledInput M₁) ξ -
        rowSmooth (√(2 / (m : ℝ)) • h1bar M₁) (sS M₁) ξ) ^ 4 ∂stdGauss (Fin m)) := by
  let v : ℝ := 2 / (m : ℝ)
  let g : (Fin N → ℝ) → Fin m → ℝ := fun u => reluV (M₁.mulVec u)
  let h := h1bar M₁
  let s := sS M₁
  let f : (Fin m → ℝ) → ℝ := fun w => (rowMean g w - rowSmooth h s w) ^ 2
  have hg : Continuous g := continuous_h1_u M₁
  have hsg : Continuous (scaledInput M₁) := hg.const_smul (√(2 / (m : ℝ)))
  have hfm : Measurable f := by
    have hb : Measurable (rowSmooth h s) := measurable_psiS.comp
      (measurable_const.prodMk
        ((continuous_dotp.comp (continuous_id.prodMk continuous_const)).measurable))
    exact ((rowMean_measurable g hg).sub hb).pow_const 2
  have hs : ∀ ξ, f (√v • ξ) =
      (rowMean (scaledInput M₁) ξ - rowSmooth (√v • h) s ξ) ^ 2 := by
    intro ξ
    unfold f rowMean rowInput rowSmooth scaledInput
    simp_rw [dotp_scale_left_right]
    rfl
  have hfi2 : Integrable (fun ξ => f (√v • ξ) ^ 2) (stdGauss (Fin m)) := by
    simp_rw [hs, ← pow_mul]
    exact row_distance_four_integrable (scaledInput M₁) hN hsg (√v • h) s
  obtain ⟨hi, hv⟩ := rows_variance_le (m := m) v f hfm hfi2
  obtain ⟨-, he⟩ := exact_row_distance (scaledInput M₁) hN hsg (√v • h) s
  have hmean : v * (m : ℝ) * (∫ ξ, f (√v • ξ) ∂stdGauss (Fin m)) =
      conditionalDelta M₁ := by
    simp_rw [hs]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    dsimp [v, h, s, conditionalDelta] at he ⊢
    rw [div_mul_cancel₀ _ hm0]
    exact he
  have hx : ∀ M₂, (BstLean.Part140.dist2 N m (M₁, M₂) - conditionalDelta M₁) ^ 2 =
      v ^ 2 * ((∑ i, f (rowOf i M₂)) -
        (m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin m)) ^ 2 := by
    intro M₂
    rw [dist2_rows M₁ M₂, ← hmean]
    change (v * (∑ i, f (rowOf i M₂)) - v * (m : ℝ) * _) ^ 2 = _
    ring
  simp_rw [hx]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hbnd := mul_le_mul_of_nonneg_left hv (sq_nonneg v)
  have hc : v ^ 2 * (m : ℝ) = 4 / (m : ℝ) := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    dsimp [v]
    field_simp
    ring
  have hr : (∫ ξ, f (√v • ξ) ^ 2 ∂stdGauss (Fin m)) =
      ∫ ξ, (rowMean (scaledInput M₁) ξ - rowSmooth (√v • h) s ξ) ^ 4
        ∂stdGauss (Fin m) := by
    simp_rw [hs, ← pow_mul]
  rw [← mul_assoc, hc, hr] at hbnd
  exact hbnd

/-- Restore the paper's standard-row normalization and the exact factor `4v²/m`. -/
theorem conditional_variance_paper (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun M₂ => (BstLean.Part140.dist2 N m (M₁, M₂) -
      2 / (m : ℝ) * worldDelta M₁) ^ 2) (gaussMat m m (2 / (m : ℝ))) ∧
    (∫ M₂, (BstLean.Part140.dist2 N m (M₁, M₂) -
      2 / (m : ℝ) * worldDelta M₁) ^ 2 ∂gaussMat m m (2 / (m : ℝ))) ≤
      (4 * (2 / (m : ℝ)) ^ 2 / (m : ℝ)) *
        (∫ ξ, (rowMean (fun u => reluV (M₁.mulVec u)) ξ -
          rowSmooth (h1bar M₁) (worldSigma M₁) ξ) ^ 4 ∂stdGauss (Fin m)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  let c : ℝ := √(2 / (m : ℝ))
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = 2 / (m : ℝ) := Real.sq_sqrt (by positivity)
  have hs : sS M₁ = c * worldSigma M₁ := by
    unfold worldSigma
    dsimp [c]
    field_simp
  have hrow : ∀ ξ, (rowMean (scaledInput M₁) ξ -
      rowSmooth (c • h1bar M₁) (sS M₁) ξ) ^ 4 =
      (2 / (m : ℝ)) ^ 2 *
        (rowMean (fun u => reluV (M₁.mulVec u)) ξ -
          rowSmooth (h1bar M₁) (worldSigma M₁) ξ) ^ 4 := by
    intro ξ
    change (rowMean (fun u => c • reluV (M₁.mulVec u)) ξ -
      rowSmooth (c • h1bar M₁) (sS M₁) ξ) ^ 4 = _
    rw [rowMean_scale _ hc.le, hs, rowSmooth_scale hc.le]
    have hc4 : c ^ 4 = (2 / (m : ℝ)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc2]
    rw [← mul_sub, mul_pow, hc4]
  obtain ⟨hi, hv⟩ := conditional_variance_scaled hN hm M₁
  rw [conditionalDelta_scale hN hm] at hi hv
  refine ⟨hi, ?_⟩
  change _ ≤ 4 / (m : ℝ) *
    (∫ ξ, (rowMean (scaledInput M₁) ξ - rowSmooth (c • h1bar M₁) (sS M₁) ξ) ^ 4
      ∂stdGauss (Fin m)) at hv
  simp_rw [hrow] at hv
  rw [integral_const_mul] at hv
  convert hv using 1 <;> ring

end BstLean.Part205

#print axioms BstLean.Part205.rows_variance_le
#print axioms BstLean.Part205.conditional_variance_scaled
#print axioms BstLean.Part205.conditional_variance_paper
