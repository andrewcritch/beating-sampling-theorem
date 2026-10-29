import BstLean.Part205KernelMean
import BstLean.Part205Ratio
import BstLean.Part205Matrix

/-! The deterministic conditional mean bound for the actual World first-layer field. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (uniformSphere uniformSphere_ae_sphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137 BstLean.Part139

section congruence
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {m : ℕ} {g g' : Ω → Fin m → ℝ}

lemma meanV_ae (he : g =ᵐ[μ] g') : meanV μ g = meanV μ g' := by
  ext j
  exact integral_congr_ae (he.mono fun x hx => congrFun hx j)

lemma covarianceT_ae (he : g =ᵐ[μ] g') (Q : ℝ) : covarianceT μ g Q = covarianceT μ g' Q := by
  have hm := meanV_ae he
  have hc : ∀ i j, covV μ g i j = covV μ g' i j := by
    intro i j
    unfold covV
    rw [hm]
    exact integral_congr_ae (he.mono fun x hx => by dsimp only; rw [hx])
  unfold covarianceT
  simp_rw [hc]
  rw [hm]

lemma radialNu_ae (he : g =ᵐ[μ] g') (Q : ℝ) : radialNu μ Q g = radialNu μ Q g' := by
  unfold radialNu
  congr 1
  exact integral_congr_ae (he.mono fun x hx => by dsimp only; rw [hx])

lemma kernelDifference_ae (he : g =ᵐ[μ] g') (σ : ℝ) :
    kernelDifference μ g σ = kernelDifference μ g' σ := by
  have hm := meanV_ae he
  have hp : (∫ p : Ω × Ω, kernelPhi (g p.1) (g p.2) ∂μ.prod μ) =
      ∫ p : Ω × Ω, kernelPhi (g' p.1) (g' p.2) ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
      Measure.quasiMeasurePreserving_snd.ae he] with p h1 h2
    rw [h1, h2]
  have hs : (∫ x, kernelPhi (Fin.cons 0 (g x)) (Fin.cons σ (meanV μ g')) ∂μ) =
      ∫ x, kernelPhi (Fin.cons 0 (g' x)) (Fin.cons σ (meanV μ g')) ∂μ := by
    exact integral_congr_ae (he.mono fun x hx => by dsimp only; rw [hx])
  unfold kernelDifference
  rw [hm, hp, hs]

end congruence

variable {N m : ℕ}

/-- A bounded version of the same first-layer field, equal on the input sphere. -/
noncomputable def boundedFirst (M₁ : Matrix (Fin m) (Fin N) ℝ) (u : Fin N → ℝ) : Fin m → ℝ :=
  reluV (M₁.mulVec (sphPt u))

lemma boundedFirst_bm (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ) (j : Fin m) :
    BM (fun u => boundedFirst M₁ u j) := by
  have hc : Continuous (fun u : Fin N → ℝ => reluV (M₁.mulVec u) j) :=
    (continuous_apply j).comp (continuous_h1_u M₁)
  obtain ⟨B, hB⟩ := isCompact_unit.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨hc.measurable.comp measurable_sphPt, B, ?_⟩
  intro u
  have h := hB (sphPt u) (normSq_sphPt hN u)
  simpa only [Real.norm_eq_abs, boundedFirst] using h

lemma boundedFirst_ae (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    boundedFirst M₁ =ᵐ[uniformSphere N] (fun u => reluV (M₁.mulVec u)) := by
  filter_upwards [uniformSphere_ae_sphere N] with u hu
  have huNorm : normSq u = 1 := hu
  have hs : sphPt u = u := by
    rw [sphPt_of_ne u (by rw [huNorm]; exact one_ne_zero)]
    unfold BstLean.Part105.sphProj
    have hu' : ∑ j, u j ^ 2 = 1 := hu
    rw [hu']
    simp
  simp only [boundedFirst, hs]

noncomputable def worldT (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  covarianceT (uniformSphere N) (fun u => reluV (M₁.mulVec u)) (firstQ M₁)

noncomputable def worldNu (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  radialNu (uniformSphere N) (firstQ M₁) (fun u => reluV (M₁.mulVec u))

lemma worldNu_sq (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ) (hQ : 0 < firstQ M₁) :
    worldNu M₁ ^ 2 =
      (∫ u, (normSq (reluV (M₁.mulVec u)) - firstQ M₁) ^ 2 ∂uniformSphere N) / firstQ M₁ ^ 2 := by
  have := uniformSphere_isProbability N hN
  unfold worldNu
  rw [radialNu_sq]
  have he : ∀ u : Fin N → ℝ, (normSq (reluV (M₁.mulVec u)) / firstQ M₁ - 1) ^ 2 =
      (normSq (reluV (M₁.mulVec u)) - firstQ M₁) ^ 2 / firstQ M₁ ^ 2 := by
    intro u
    field_simp
    <;> ring
  simp_rw [he]
  rw [integral_div]

/-- The P10e deterministic mean estimate, for every frontier dimension and every hidden width. -/
theorem world_mean_bound {n : ℕ} (hn : 4096 ≤ n) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin (2 * n)) ℝ) (hQ : 0 < firstQ M₁) :
    worldDelta M₁ / firstQ M₁ ≤
      meanBound (normSq (h1bar M₁) / firstQ M₁) (worldT M₁) (worldNu M₁) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  let μ := uniformSphere (2 * n)
  let g : (Fin (2 * n) → ℝ) → Fin m → ℝ := fun u => reluV (M₁.mulVec u)
  let b := boundedFirst M₁
  have hb : ∀ j, BM (fun u => b u j) := boundedFirst_bm hN M₁
  have he : b =ᵐ[μ] g := boundedFirst_ae hN M₁
  have hmean : meanV μ b = h1bar M₁ := meanV_ae he
  have hQeq : (∫ u, normSq (b u) ∂μ) = firstQ M₁ :=
    integral_congr_ae (he.mono fun u hu => congrArg normSq hu)
  have hσ : normSq (meanV μ b) + worldSigma M₁ ^ 2 = firstQ M₁ := by
    rw [hmean, worldSigma_sq hN hm]
    ring
  obtain ⟨hr0, hr1⟩ := world_ratio_window hn hm M₁ hQ
  have h := kernel_mean_bound μ b hb hm hQ hQeq hσ
    (by rw [hmean]; linarith) (by rw [hmean]; linarith)
  rw [kernelDifference_ae he, covarianceT_ae he, radialNu_ae he, hmean] at h
  exact h

/-- Combine the exact conditional mean and the deterministic Taylor mean estimate. -/
theorem world_conditional_mean_bound {n : ℕ} (hn : 4096 ≤ n) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin (2 * n)) ℝ) (hQ : 0 < firstQ M₁) :
    (∫ M₂, BstLean.Part140.dist2 (2 * n) m (M₁, M₂) ∂gaussMat m m (2 / (m : ℝ))) ≤
      (2 / (m : ℝ)) * firstQ M₁ *
        meanBound (normSq (h1bar M₁) / firstQ M₁) (worldT M₁) (worldNu M₁) := by
  rw [(exact_conditional_distance_paper (by omega) hm M₁).2]
  have h := (div_le_iff₀ hQ).mp (world_mean_bound hn hm M₁ hQ)
  have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 / (m : ℝ))
  convert h' using 1 <;> ring

end BstLean.Part205

#print axioms BstLean.Part205.world_mean_bound
#print axioms BstLean.Part205.world_conditional_mean_bound
