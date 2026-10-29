import BstLean.Part205Variance

/-! Exact conditional variance with the squared mean correction. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137
open BstLean.Part205

theorem rows_variance_eq {m k : ℕ} (v : ℝ) (f : (Fin k → ℝ) → ℝ)
    (hf : Measurable f)
    (hf2 : Integrable (fun ξ => f (√v • ξ) ^ 2) (stdGauss (Fin k))) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      ((∑ i, f (rowOf i M)) - (m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin k)) ^ 2)
      (gaussMat m k v) ∧
    (∫ M : Matrix (Fin m) (Fin k) ℝ,
      ((∑ i, f (rowOf i M)) - (m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin k)) ^ 2
      ∂gaussMat m k v) = (m : ℝ) *
      ((∫ ξ, f (√v • ξ) ^ 2 ∂stdGauss (Fin k)) -
        (∫ ξ, f (√v • ξ) ∂stdGauss (Fin k)) ^ 2) := by
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
  ring

noncomputable def rowDiscrepancy {N m : ℕ}
    (M₁ : Matrix (Fin m) (Fin N) ℝ) (ξ : Fin m → ℝ) : ℝ :=
  rowMean (fun u => reluV (M₁.mulVec u)) ξ -
    rowSmooth (h1bar M₁) (worldSigma M₁) ξ

lemma measurable_rowDiscrepancy {N m : ℕ} (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Measurable (rowDiscrepancy M₁) := by
  exact (rowMean_measurable _ (continuous_h1_u M₁)).sub
    (measurable_psiS.comp (measurable_const.prodMk
      ((continuous_dotp.comp (continuous_id.prodMk continuous_const)).measurable)))

/-- The exact variance retains the negative squared conditional row mean. -/
theorem conditional_variance_exact {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun M₂ => (BstLean.Part140.dist2 N m (M₁, M₂) -
      2 / (m : ℝ) * worldDelta M₁) ^ 2) (gaussMat m m (2 / (m : ℝ))) ∧
    (∫ M₂, (BstLean.Part140.dist2 N m (M₁, M₂) -
      2 / (m : ℝ) * worldDelta M₁) ^ 2 ∂gaussMat m m (2 / (m : ℝ))) =
      (4 * (2 / (m : ℝ)) ^ 2 / (m : ℝ)) *
        ((∫ ξ, rowDiscrepancy M₁ ξ ^ 4 ∂stdGauss (Fin m)) -
          (worldDelta M₁ / 2) ^ 2) := by
  let v : ℝ := 2 / (m : ℝ)
  let g : (Fin N → ℝ) → Fin m → ℝ := fun u => reluV (M₁.mulVec u)
  let f : (Fin m → ℝ) → ℝ := fun w =>
    (rowMean g w - rowSmooth (h1bar M₁) (sS M₁) w) ^ 2
  let c : ℝ := √v
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < c := Real.sqrt_pos.mpr (by dsimp [v]; positivity)
  have hc2 : c ^ 2 = v := Real.sq_sqrt (by dsimp [v]; positivity)
  have hs : sS M₁ = c * worldSigma M₁ := by
    unfold worldSigma
    dsimp [c, v]
    field_simp
  have hf : Measurable f := by
    exact ((rowMean_measurable g (continuous_h1_u M₁)).sub
      (measurable_psiS.comp (measurable_const.prodMk
        ((continuous_dotp.comp (continuous_id.prodMk continuous_const)).measurable)))).pow_const 2
  have heq : ∀ ξ, f (√v • ξ) = v * rowDiscrepancy M₁ ξ ^ 2 := by
    intro ξ
    have he : rowMean g (c • ξ) = c * rowMean g ξ := by
      unfold rowMean rowInput
      simp_rw [dotp_scale_left_right, dotp_scale_right, relu_mul_of_nonneg hc.le]
      rw [integral_const_mul]
    have he' : rowSmooth (h1bar M₁) (sS M₁) (c • ξ) =
        c * rowSmooth (h1bar M₁) (worldSigma M₁) ξ := by
      unfold rowSmooth
      rw [dotp_scale_left_right, dotp_scale_right, hs, psiS_scale hc.le]
    change (rowMean g (c • ξ) - rowSmooth (h1bar M₁) (sS M₁) (c • ξ)) ^ 2 = _
    rw [he, he', ← mul_sub, mul_pow, hc2]
    rfl
  have i4 : Integrable (fun ξ => rowDiscrepancy M₁ ξ ^ 4) (stdGauss (Fin m)) :=
    row_distance_four_integrable g hN (continuous_h1_u M₁) _ _
  have if2 : Integrable (fun ξ => f (√v • ξ) ^ 2) (stdGauss (Fin m)) := by
    simp_rw [heq, mul_pow, ← pow_mul]
    exact i4.const_mul (v ^ 2)
  have i2 := (exact_row_distance g hN (continuous_h1_u M₁)
    (h1bar M₁) (worldSigma M₁)).1
  have e2 : (∫ ξ, rowDiscrepancy M₁ ξ ^ 2 ∂stdGauss (Fin m)) = worldDelta M₁ / 2 := by
    have h := (exact_row_distance g hN (continuous_h1_u M₁)
      (h1bar M₁) (worldSigma M₁)).2
    change 2 * (∫ ξ, rowDiscrepancy M₁ ξ ^ 2 ∂stdGauss (Fin m)) = worldDelta M₁ at h
    linarith
  have e1 : (∫ ξ, f (√v • ξ) ∂stdGauss (Fin m)) = v * (worldDelta M₁ / 2) := by
    simp_rw [heq]
    rw [integral_const_mul, e2]
  obtain ⟨hi, hv⟩ := rows_variance_eq (m := m) v f hf if2
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hx : ∀ M₂, (BstLean.Part140.dist2 N m (M₁, M₂) - v * worldDelta M₁) ^ 2 =
      v ^ 2 * ((∑ i, f (rowOf i M₂)) -
        (m : ℝ) * ∫ ξ, f (√v • ξ) ∂stdGauss (Fin m)) ^ 2 := by
    intro M₂
    rw [dist2_rows, e1]
    change (v * (∑ i, f (rowOf i M₂)) - v * worldDelta M₁) ^ 2 = _
    dsimp [v]
    field_simp
    <;> ring
  change Integrable (fun M₂ => (BstLean.Part140.dist2 N m (M₁, M₂) -
    v * worldDelta M₁) ^ 2) (gaussMat m m v) ∧
    (∫ M₂, (BstLean.Part140.dist2 N m (M₁, M₂) - v * worldDelta M₁) ^ 2
      ∂gaussMat m m v) = (4 * v ^ 2 / (m : ℝ)) *
        ((∫ ξ, rowDiscrepancy M₁ ξ ^ 4 ∂stdGauss (Fin m)) - (worldDelta M₁ / 2) ^ 2)
  simp_rw [hx]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, hv, e1]
  simp_rw [heq, mul_pow, ← pow_mul]
  rw [integral_const_mul]
  dsimp [v]
  field_simp
  <;> ring

end BstLean.Part214
#print axioms BstLean.Part214.rows_variance_eq
#print axioms BstLean.Part214.conditional_variance_exact
