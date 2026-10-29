import BstLean.Part218EventBounds

/-! The concrete E1 supply and sharp sixth moment give the variable-threshold distance charge. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part130 BstLean.Part133 BstLean.Part137 BstLean.Part205 BstLean.Part214

noncomputable def firstRatio (N : ℕ) : ℝ := 2 * (N : ℝ) * cN N ^ 2
noncomputable def e1CovarianceRatio (N m : ℕ) (εω : ℝ) (ε : Fin 4 → ℝ) : ℝ :=
  e1FrobBound N m ε / (e1EnergyLower N m εω * (1 - firstRatio N))
noncomputable def e1MeanBound (N m : ℕ) (εω ph : ℝ) (ε : Fin 4 → ℝ) : ℝ :=
  meanBound (firstRatio N)
    ((e1FrobBound N m ε ^ 2 + 2 * (directionMean N m / ph)) / e1EnergyLower N m εω ^ 2)
    (√(e1InputVarianceBound N m ε) / e1EnergyLower N m εω)
noncomputable def e1Charge (N m : ℕ) (εω ph : ℝ) (ε : Fin 4 → ℝ) : ℝ :=
  (exp (-((m : ℝ) * N) / 2 * (εω - log (1 + εω))) +
    exp (-((m : ℝ) * N) / 2 * (-εω - log (1 - εω)))) +
    (∑ i, e1Variances N m i / (ε i * e1MeanBounds N m i) ^ 2) + ph

lemma firstRatio_lt_one {N : ℕ} (hN : 2 ≤ N) : firstRatio N < 1 := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have hr := (BstLean.Part159.rN_window hN).2
  have hb : (N : ℝ) / (π * (N - 1)) < 1 := by
    apply (div_lt_one (by positivity : 0 < π * ((N : ℝ) - 1))).mpr
    nlinarith [pi_gt_three]
  exact hr.trans_lt hb

lemma e1CovarianceRatio_nonneg {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m)
    {εω : ℝ} (hεω : εω < 1) (ε : Fin 4 → ℝ) : 0 ≤ e1CovarianceRatio N m εω ε := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr := firstRatio_lt_one hN
  unfold e1CovarianceRatio e1EnergyLower e1FrobBound
  positivity

lemma e1_ratio_identity {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    {M : Matrix (Fin m) (Fin N) ℝ} {εω ph : ℝ} {ε : Fin 4 → ℝ}
    (hεω : εω < 1) (hM : M ∈ concreteFirstLayerEvent N m εω ph ε) :
    normSq (h1bar M) = firstQ M * firstRatio N := by
  have hQ := (energy_window hN hm M hεω hM.1).1
  have h := (div_eq_iff hQ.ne').mp (world_ratio hN hm M hQ)
  change normSq (h1bar M) = firstRatio N * firstQ M at h
  nlinarith

theorem e1_worldCovarianceRatio {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m)
    {M : Matrix (Fin m) (Fin N) ℝ} {εω ph : ℝ} {ε : Fin 4 → ℝ}
    (hεω : εω < 1) (hM : M ∈ concreteFirstLayerEvent N m εω ph ε) :
    worldFrobSq M ≤ (e1CovarianceRatio N m εω ε * worldSigma M ^ 2) ^ 2 := by
  have hn : 1 ≤ N := by omega
  have hn' : (0 : ℝ) < N := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : 0 < 1 - firstRatio N := sub_pos.mpr (firstRatio_lt_one hN)
  have hq : 0 < e1EnergyLower N m εω := by unfold e1EnergyLower; positivity
  have hQ := (energy_window hn hm M hεω hM.1).2.1
  have hs : worldSigma M ^ 2 = firstQ M * (1 - firstRatio N) := by
    rw [worldSigma_sq hn hm, e1_ratio_identity hn hm hεω hM]
    ring
  have hlow : e1EnergyLower N m εω * (1 - firstRatio N) ≤ worldSigma M ^ 2 := by
    rw [hs]
    exact mul_le_mul_of_nonneg_right hQ hr.le
  have he := e1CovarianceRatio_nonneg hN hm hεω ε
  have heq : e1CovarianceRatio N m εω ε * (e1EnergyLower N m εω * (1 - firstRatio N)) =
      e1FrobBound N m ε := by
    unfold e1CovarianceRatio
    exact div_mul_cancel₀ _ (mul_pos hq hr).ne'
  have hF := mul_le_mul_of_nonneg_left hlow he
  rw [heq] at hF
  exact (e1_worldFrob hn hM).trans (pow_le_pow_left₀ (by unfold e1FrobBound; positivity) hF 2)

/-- Only explicit scalar bounds and a positive mean reserve remain as premises. -/
theorem concrete_distance_charge {n : ℕ} (hn : 4096 ≤ n)
    {εω ph Δ Xc : ℝ} {ε : Fin 4 → ℝ} (hεω : 0 < εω) (hεω1 : εω < 1)
    (hph : 0 < ph) (hε : ∀ i, 0 < ε i) (hΔ0 : 0 ≤ Δ)
    (hΔ : e1MeanBound (2 * n) (mW n) εω ph ε ≤ Δ)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ < Xc) :
    (BstLean.Part136.hidGauss (2 * n) (mW n)).real (BstLean.Part140.goodDist n Xc)ᶜ ≤
      e1Charge (2 * n) (mW n) εω ph ε +
      ((4 * ((2 * n : ℕ) : ℝ) ^ 2 / (mW n : ℝ)) * (1 + εω) ^ 2 * √(Δ / 2) *
        ((1 - firstRatio (2 * n)) * √(1 - firstRatio (2 * n)) *
          sixthConstant (e1CovarianceRatio (2 * n) (mW n) εω ε))) /
        (Xc - ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ) ^ 2 := by
  have hN : 2 ≤ 2 * n := by omega
  have hm : 2 ≤ mW n := by have := BstLean.Part132.mW_ge hn; omega
  have hm1 : 1 ≤ mW n := by omega
  have hE := concreteFirstLayerEvent_charge hN hm hεω hεω1 hph hε
  apply direct_distance_from_covariance hn hE.1 hεω.le hεω1
    (e1CovarianceRatio_nonneg hN hm1 hεω1 ε) (sub_nonneg.mpr (firstRatio_lt_one hN).le)
    hΔ0 hX hE.2
  · intro M hM
    exact hM.1
  · intro M hM
    have hQ := (energy_window (by omega) hm1 M hεω1 hM.1).1
    rw [world_ratio (by omega) hm1 M hQ]
    exact (e1_worldMean hn hm1 hεω1 hM).trans hΔ
  · intro M hM
    exact e1_ratio_identity (by omega) hm1 hεω1 hM
  · intro M hM
    exact e1_worldCovarianceRatio hN hm1 hεω1 hM

end BstLean.Part218
#print BstLean.Part218.concrete_distance_charge
#print axioms BstLean.Part218.concrete_distance_charge
