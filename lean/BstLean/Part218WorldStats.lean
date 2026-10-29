import BstLean.Part218Distance

/-! Deterministic transfer from actual covariance, direction and norm-fluctuation statistics. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part139 BstLean.Part205

lemma meanBound_mono {r T T' ν ν' : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2)
    (hT : T ≤ T') (hν0 : 0 ≤ ν) (hν : ν ≤ ν') :
    meanBound r T ν ≤ meanBound r T' ν' := by
  have hk := endpointK_nonneg hr0 hr1
  have hs : 0 ≤ slopeK r := div_nonneg (sub_nonneg.mpr (arccos_le_pi r)) pi_pos.le
  have hκ := (kappa_mem (by linarith : -1 ≤ r) (by linarith : r ≤ 1)).1
  have hc : 0 ≤ slopeK r + BstLean.Part130.kappa r + 4 := by linarith
  have hν1 : 0 ≤ ν' := hν0.trans hν
  unfold meanBound
  gcongr <;> positivity

noncomputable def worldDirection {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  centeredGram M (h1bar M)

noncomputable def worldInputVariance {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∫ u, (normSq (reluV (M.mulVec u)) - firstQ M) ^ 2 ∂uniformSphere N

lemma worldT_stats {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    worldT M = (worldFrobSq M + 2 * worldDirection M) / firstQ M ^ 2 := by
  have h := BstLean.Part109.gram_expand (uniformSphere N) (centeredFirst M)
    (centeredFirst_memLp hN M) (h1bar M)
  change worldDirection M = _ at h
  rw [h]
  unfold worldT covarianceT worldFrobSq
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change h1bar M i * covV (uniformSphere N) (fun u => reluV (M.mulVec u)) i j * h1bar M j =
    h1bar M i * h1bar M j * covV (uniformSphere N) (fun u => reluV (M.mulVec u)) i j
  ring

lemma world_stats_bounds {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ)
    {q F H V : ℝ} (hq : 0 < q) (hQ : q ≤ firstQ M)
    (hC : worldFrobSq M ≤ F ^ 2) (hH : worldDirection M ≤ H)
    (hV : worldInputVariance M ≤ V) :
    worldT M ≤ (F ^ 2 + 2 * H) / q ^ 2 ∧
      worldNu M ≤ √V / q := by
  have hQ0 : 0 < firstQ M := hq.trans_le hQ
  have hH0 : 0 ≤ H := (centeredGram_nonneg M _).trans hH
  have hV0 : 0 ≤ V := (integral_nonneg fun _ => sq_nonneg _).trans hV
  have hden : q ^ 2 ≤ firstQ M ^ 2 := pow_le_pow_left₀ hq.le hQ 2
  constructor
  · rw [worldT_stats hN]
    exact (div_le_div_of_nonneg_right (add_le_add hC (by linarith)) (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hq) hden)
  · have hν : 0 ≤ worldNu M := sqrt_nonneg _
    have hsq := worldNu_sq hN M hQ0
    have hb : worldNu M ^ 2 ≤ V / q ^ 2 := by
      rw [hsq]
      exact (div_le_div_of_nonneg_right hV (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left hV0 (sq_pos_of_pos hq) hden)
    apply (sq_le_sq₀ hν (by positivity : 0 ≤ √V / q)).mp
    rw [div_pow, sq_sqrt hV0]
    exact hb

/-- The actual S08 Taylor quantity is bounded by the three first-layer statistics. -/
theorem world_mean_from_stats {n m : ℕ} (hn : 4096 ≤ n)
    (M : Matrix (Fin m) (Fin (2 * n)) ℝ) {q F H V : ℝ}
    (hq : 0 < q) (hQ : q ≤ firstQ M)
    (hC : worldFrobSq M ≤ F ^ 2) (hH : worldDirection M ≤ H)
    (hV : worldInputVariance M ≤ V) (hm : 1 ≤ m) :
    meanBound (normSq (h1bar M) / firstQ M) (worldT M) (worldNu M) ≤
      meanBound (normSq (h1bar M) / firstQ M) ((F ^ 2 + 2 * H) / q ^ 2) (√V / q) := by
  obtain ⟨hr0, hr1⟩ := world_ratio_window hn hm M (hq.trans_le hQ)
  obtain ⟨hT, hν⟩ := world_stats_bounds (by omega) M hq hQ hC hH hV
  exact meanBound_mono (by linarith) (by linarith) hT (sqrt_nonneg _) hν

end BstLean.Part218
#print axioms BstLean.Part218.world_mean_from_stats
