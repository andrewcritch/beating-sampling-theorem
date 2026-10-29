import BstLean.Part205Row
import BstLean.Part140Dist

/-! Conditional distance for the actual World hidden matrices. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part136 BstLean.Part137

variable {N m : ℕ}

/-- The He-scaled first hidden vector. -/
noncomputable def scaledInput (M₁ : Matrix (Fin m) (Fin N) ℝ) (u : Fin N → ℝ) : Fin m → ℝ :=
  √(2 / (m : ℝ)) • reluV (M₁.mulVec u)

/-- The exact conditional kernel difference in scaled coordinates. -/
noncomputable def conditionalDelta (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  rowDelta (scaledInput M₁) (√(2 / (m : ℝ)) • h1bar M₁) (sS M₁)

/-- The standard-Gaussian smoothing scale. -/
noncomputable def worldSigma (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  sS M₁ / √(2 / (m : ℝ))

/-- The unscaled kernel difference in the paper's conditional identity. -/
noncomputable def worldDelta (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  rowDelta (fun u => reluV (M₁.mulVec u)) (h1bar M₁) (worldSigma M₁)

noncomputable def firstQ (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∫ u, normSq (reluV (M₁.mulVec u)) ∂uniformSphere N

lemma worldSigma_sq (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    worldSigma M₁ ^ 2 = firstQ M₁ - normSq (h1bar M₁) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : 0 < 2 / (m : ℝ) := by positivity
  have hG : GamS M₁ = 2 / (m : ℝ) * firstQ M₁ := by
    unfold GamS alphaU firstQ
    rw [integral_const_mul]
  unfold worldSigma
  rw [div_pow, Real.sq_sqrt hv.le, sS_sq hN, hG]
  field_simp

/-- Both augmented norms equal `Q`, and their inner product is the squared first-layer centre. -/
lemma world_smoothing_geometry (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    normSq (smoothP (h1bar M₁) (worldSigma M₁)) = firstQ M₁ ∧
    normSq (smoothP' (h1bar M₁) (worldSigma M₁)) = firstQ M₁ ∧
    dotp (smoothP (h1bar M₁) (worldSigma M₁))
      (smoothP' (h1bar M₁) (worldSigma M₁)) = normSq (h1bar M₁) := by
  rw [smoothP_normSq, smoothP'_normSq, worldSigma_sq hN hm, smoothing_dot]
  constructor
  · ring
  · exact ⟨by ring, rfl⟩

lemma world_smoothing_kernel (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    kernelPhi (smoothP (h1bar M₁) (worldSigma M₁))
      (smoothP' (h1bar M₁) (worldSigma M₁)) =
      firstQ M₁ * BstLean.Part130.kappa (normSq (h1bar M₁) / firstQ M₁) := by
  obtain ⟨hp, hq, hd⟩ := world_smoothing_geometry hN hm M₁
  have hQ : 0 ≤ firstQ M₁ := integral_nonneg fun _ => normSq_nonneg _
  unfold kernelPhi
  rw [hp, hq, hd, Real.mul_self_sqrt hQ]

lemma conditionalDelta_scale (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    conditionalDelta M₁ = 2 / (m : ℝ) * worldDelta M₁ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  let c : ℝ := √(2 / (m : ℝ))
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = 2 / (m : ℝ) := Real.sq_sqrt (by positivity)
  let g : (Fin N → ℝ) → Fin m → ℝ := fun u => reluV (M₁.mulVec u)
  have hg : Continuous g := continuous_h1_u M₁
  have hg' : Continuous (scaledInput M₁) := hg.const_smul c
  obtain ⟨hi, he⟩ := exact_row_distance g hN hg (h1bar M₁) (worldSigma M₁)
  obtain ⟨-, he'⟩ := exact_row_distance (scaledInput M₁) hN hg'
    (c • h1bar M₁) (sS M₁)
  have hs : sS M₁ = c * worldSigma M₁ := by
    unfold worldSigma
    dsimp [c]
    field_simp
  have hrow : ∀ ξ, (rowMean (scaledInput M₁) ξ -
      rowSmooth (c • h1bar M₁) (sS M₁) ξ) ^ 2 =
      c ^ 2 * (rowMean g ξ - rowSmooth (h1bar M₁) (worldSigma M₁) ξ) ^ 2 := by
    intro ξ
    change (rowMean (fun u => c • g u) ξ -
      rowSmooth (c • h1bar M₁) (sS M₁) ξ) ^ 2 = _
    rw [rowMean_scale g hcpos.le, hs, rowSmooth_scale hcpos.le]
    ring
  simp_rw [hrow] at he'
  rw [integral_const_mul, hc2] at he'
  change 2 * (∫ ξ, (rowMean g ξ - rowSmooth (h1bar M₁) (worldSigma M₁) ξ) ^ 2
    ∂stdGauss (Fin m)) = worldDelta M₁ at he
  change 2 * (2 / (m : ℝ) * _) = conditionalDelta M₁ at he'
  calc conditionalDelta M₁ = 2 * (2 / (m : ℝ) *
      (∫ ξ, (rowMean g ξ - rowSmooth (h1bar M₁) (worldSigma M₁) ξ) ^ 2
        ∂stdGauss (Fin m))) := he'.symm
    _ = 2 / (m : ℝ) * worldDelta M₁ := by rw [← he]; ring

lemma dotp_scale_left_right (c : ℝ) (ξ h : Fin m → ℝ) :
    dotp (c • ξ) h = dotp ξ (c • h) := by
  unfold dotp
  simp only [Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The network distance is the sum of the squared row discrepancies. -/
lemma dist2_rows (M₁ : Matrix (Fin m) (Fin N) ℝ) (M₂ : Matrix (Fin m) (Fin m) ℝ) :
    BstLean.Part140.dist2 N m (M₁, M₂) = 2 / (m : ℝ) *
      ∑ i, (rowMean (fun u => reluV (M₁.mulVec u)) (rowOf i M₂) -
        rowSmooth (h1bar M₁) (sS M₁) (rowOf i M₂)) ^ 2 := by
  unfold BstLean.Part140.dist2 normSq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hh : hbarW (M₁, M₂) i =
      rowMean (fun u => reluV (M₁.mulVec u)) (rowOf i M₂) := rfl
  have hb : bhat (M₁, M₂) i = rowSmooth (h1bar M₁) (sS M₁) (rowOf i M₂) := rfl
  simp only [Pi.sub_apply, hh, hb]
  ring

/-- Positive homogeneity gives the pointwise standard-row distance formula. -/
theorem dist2_standard_rows (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) (Ξ : Fin m → Fin m → ℝ) :
    BstLean.Part140.dist2 N m
      (M₁, fun i j => √(2 / (m : ℝ)) * Ξ i j) =
      (2 * (2 / (m : ℝ)) / (m : ℝ)) *
        ∑ i, (rowMean (fun u => reluV (M₁.mulVec u)) (Ξ i) -
          rowSmooth (h1bar M₁) (worldSigma M₁) (Ξ i)) ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  let c : ℝ := √(2 / (m : ℝ))
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = 2 / (m : ℝ) := Real.sq_sqrt (by positivity)
  have hs : sS M₁ = c * worldSigma M₁ := by
    unfold worldSigma
    dsimp [c]
    field_simp
  let g : (Fin N → ℝ) → Fin m → ℝ := fun u => reluV (M₁.mulVec u)
  have hrow : ∀ ξ, rowMean g (c • ξ) - rowSmooth (h1bar M₁) (sS M₁) (c • ξ) =
      c * (rowMean g ξ - rowSmooth (h1bar M₁) (worldSigma M₁) ξ) := by
    intro ξ
    have hmean : rowMean g (c • ξ) = c * rowMean g ξ := by
      unfold rowMean rowInput
      simp_rw [dotp_scale_left_right, dotp_scale_right, relu_mul_of_nonneg hc.le]
      rw [integral_const_mul]
    have hsmooth : rowSmooth (h1bar M₁) (sS M₁) (c • ξ) =
        c * rowSmooth (h1bar M₁) (worldSigma M₁) ξ := by
      unfold rowSmooth
      rw [dotp_scale_left_right, dotp_scale_right, hs, psiS_scale hc.le]
    rw [hmean, hsmooth]
    ring
  rw [dist2_rows M₁ (fun i j => √(2 / (m : ℝ)) * Ξ i j)]
  change (2 / (m : ℝ)) * (∑ i, (rowMean g (c • Ξ i) -
    rowSmooth (h1bar M₁) (sS M₁) (c • Ξ i)) ^ 2) = _
  simp_rw [hrow, mul_pow, hc2]
  rw [← Finset.mul_sum]
  ring

/-- Integrate the complete second-layer distribution before any hidden-event restriction. -/
theorem exact_conditional_distance (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun M₂ => BstLean.Part140.dist2 N m (M₁, M₂))
      (gaussMat m m (2 / (m : ℝ))) ∧
    (∫ M₂, BstLean.Part140.dist2 N m (M₁, M₂)
      ∂gaussMat m m (2 / (m : ℝ))) = conditionalDelta M₁ := by
  classical
  let v : ℝ := 2 / (m : ℝ)
  let g : (Fin N → ℝ) → Fin m → ℝ := fun u => reluV (M₁.mulVec u)
  let h := h1bar M₁
  let s := sS M₁
  let f : (Fin m → ℝ) → ℝ := fun w => (rowMean g w - rowSmooth h s w) ^ 2
  have hg : Continuous g := continuous_h1_u M₁
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
  have hsg : Continuous (scaledInput M₁) := hg.const_smul (√(2 / (m : ℝ)))
  obtain ⟨hi, he⟩ := exact_row_distance (scaledInput M₁) hN hsg (√v • h) s
  have hfi : Integrable (fun ξ => f (√v • ξ)) (stdGauss (Fin m)) := by
    simp_rw [hs]
    exact hi
  have hir : ∀ i : Fin m, Integrable (fun M₂ => f (rowOf i M₂)) (gaussMat m m v) :=
    fun i => (row_integrable_iff v i hfm).mpr hfi
  have hei : ∀ i : Fin m, ∫ M₂, f (rowOf i M₂) ∂gaussMat m m v =
      (conditionalDelta M₁) / 2 := by
    intro i
    rw [row_integral v i hfm]
    simp_rw [hs]
    dsimp [conditionalDelta, v, h, s] at he ⊢
    linarith
  have hdist : (fun M₂ => BstLean.Part140.dist2 N m (M₁, M₂)) =
      fun M₂ => v * ∑ i, f (rowOf i M₂) := by
    funext M₂
    exact dist2_rows M₁ M₂
  rw [hdist]
  refine ⟨(integrable_finsetSum _ (fun i _ => hir i)).const_mul v, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hir i)]
  simp_rw [hei]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  dsimp [v]
  field_simp

/-- The paper normalization gives `E[dist2 | M₁] = v Δ`, with `v = 2/m`. -/
theorem exact_conditional_distance_paper (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun M₂ => BstLean.Part140.dist2 N m (M₁, M₂))
      (gaussMat m m (2 / (m : ℝ))) ∧
    (∫ M₂, BstLean.Part140.dist2 N m (M₁, M₂)
      ∂gaussMat m m (2 / (m : ℝ))) = 2 / (m : ℝ) * worldDelta M₁ := by
  obtain ⟨hi, he⟩ := exact_conditional_distance hN hm M₁
  exact ⟨hi, he.trans (conditionalDelta_scale hN hm M₁)⟩

end BstLean.Part205

#print axioms BstLean.Part205.dist2_rows
#print axioms BstLean.Part205.exact_conditional_distance
#print axioms BstLean.Part205.exact_conditional_distance_paper
