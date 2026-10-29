import BstLean.Part154Win

/-!
# Part 154: the window of `θ_in` for `n ≥ 8192`
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150
open BstLean.Part141 (cenA tauWA)

/-- The set of the stand-in inputs `(c, τ)` with `0.457 ≤ θ_in ≤ 0.555`. -/
def Wd8 (n : ℕ) : Set ((Fin n → ℝ) × ℝ) :=
  {p | 457 / 1000 ≤ thetaC p.1 p.2 ∧ thetaC p.1 p.2 ≤ 555 / 1000}

theorem measurableSet_Wd8 (n : ℕ) : MeasurableSet (Wd8 n) := by
  have hθ : Measurable (fun p : (Fin n → ℝ) × ℝ => thetaC p.1 p.2) := by
    unfold thetaC rhoC
    exact ((measurable_snd.pow_const 2).const_mul _).div
      ((((measurable_normSq.comp measurable_fst).add
        ((measurable_snd.pow_const 2).const_mul _)).sqrt).pow_const 2)
  exact (measurableSet_le measurable_const hθ).inter (measurableSet_le hθ measurable_const)

/-- The lower tail of `|M b|²` for a Gaussian matrix (the analogue of `lemmaEc_gen`). -/
private lemma lowerWin8 {n m : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : 0 ≤ v) (b : Fin m → ℝ)
    (hK : 0 < v * normSq b) {L : ℝ} (hL : 0 ≤ L) :
    (gaussMat n m v).real {M | normSq (M *ᵥ b) ≤ v * normSq b * ((n : ℝ) - 2 * √((n : ℝ) * L))} ≤
      Real.exp (-L) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set K : ℝ := v * normSq b with hKd
  have hS : MeasurableSet {y : Fin n → ℝ | normSq y ≤ K * ((n : ℝ) - 2 * √((n : ℝ) * L))} :=
    measurableSet_le measurable_normSq measurable_const
  have e : {M : Matrix (Fin n) (Fin m) ℝ | normSq (M *ᵥ b) ≤ K * ((n : ℝ) - 2 * √((n : ℝ) * L))} =
      (fun M : Matrix (Fin n) (Fin m) ℝ => M *ᵥ b) ⁻¹'
        {y | normSq y ≤ K * ((n : ℝ) - 2 * √((n : ℝ) * L))} := rfl
  rw [e, ← map_measureReal_apply (measurable_mulVec_right b) hS, gaussMat_mulVec,
    map_measureReal_apply (by fun_prop) hS]
  have hc2 : (√v * √(normSq b)) ^ 2 = K := by
    rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (normSq_nonneg _)]
  have hLM := BstLean.Part152.chiSq_lower_LM (ι := Fin n) hL
  rw [Fintype.card_fin] at hLM
  refine le_trans (measureReal_mono ?_) hLM
  intro ξ hξ
  simp only [mem_preimage, mem_ofPred_eq] at hξ ⊢
  rw [normSq_smul, hc2] at hξ
  have hns : normSq ξ = ∑ i, ξ i ^ 2 := rfl
  rw [← hns]
  exact le_of_mul_le_mul_left hξ hK

/-- **The window of `θ_in`**: `Pr_W(θ_in ∉ [0.457, 0.555]) ≤ 1/n + 2e^{−8}` for `n ≥ 8192`. -/
theorem Wd8_prob {n : ℕ} (hn : 8192 ≤ n) :
    (mlpGauss (2 * n) (mW n) n).real {W | (cenA W, tauWA W) ∉ Wd8 n} ≤
      1 / (n : ℝ) + 2 * rexp (-8) := by
  have hn1 : 1 ≤ n := by omega
  have hn4 : 4096 ≤ n := by omega
  have hnR : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmpos : (0 : ℝ) ≤ 2 / (mW n : ℝ) := by positivity
  -- the two chi-square bad sets
  set U : Set (MlpParam (2 * n) (mW n) n) :=
    {W | 2 / (mW n : ℝ) * normSq (BstLean.Part141.bA n (W.1, W.2.1)) * n *
      (1 + BstLean.Part151.deltaC n 8) < normSq (cenA W)} with hU
  set Lo : Set (MlpParam (2 * n) (mW n) n) :=
    {W | 0 < 2 / (mW n : ℝ) * normSq (BstLean.Part141.bA n (W.1, W.2.1)) ∧
      normSq (cenA W) ≤ 2 / (mW n : ℝ) * normSq (BstLean.Part141.bA n (W.1, W.2.1)) *
        ((n : ℝ) - 2 * √((n : ℝ) * 8))} with hLo
  have hθm : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ((W.1, W.2.1) : BstLean.Part136.HidParam (2 * n) (mW n))) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hKm : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      2 / (mW n : ℝ) * normSq (BstLean.Part141.bA n (W.1, W.2.1))) :=
    (measurable_normSq.comp ((BstLean.Part141.measurable_bA n).comp hθm)).const_mul _
  have hNm : Measurable (fun W : MlpParam (2 * n) (mW n) n => normSq (cenA W)) :=
    measurable_normSq.comp BstLean.Part141.measurable_cenA
  have hUm : MeasurableSet U :=
    measurableSet_lt ((hKm.mul measurable_const).mul measurable_const) hNm
  have hLom : MeasurableSet Lo :=
    (measurableSet_lt measurable_const hKm).inter
      (measurableSet_le hNm (hKm.mul measurable_const))
  have hUp : (mlpGauss (2 * n) (mW n) n).real U ≤ rexp (-8) := by
    unfold mlpGauss
    refine BstLean.Part153.prod_real_le_of_fibre hUm (by positivity) fun M₁ => ?_
    refine BstLean.Part153.prod_real_le_of_fibre (measurable_prodMk_left hUm) (by positivity)
      fun M₂ => ?_
    exact BstLean.Part151.lemmaEc_gen hn1 hmpos (BstLean.Part141.bA n (M₁, M₂)) (by norm_num)
  have hLop : (mlpGauss (2 * n) (mW n) n).real Lo ≤ rexp (-8) := by
    unfold mlpGauss
    refine BstLean.Part153.prod_real_le_of_fibre hLom (by positivity) fun M₁ => ?_
    refine BstLean.Part153.prod_real_le_of_fibre (measurable_prodMk_left hLom) (by positivity)
      fun M₂ => ?_
    by_cases hK : 0 < 2 / (mW n : ℝ) * normSq (BstLean.Part141.bA n (M₁, M₂))
    · refine le_trans (measureReal_mono ?_)
        (lowerWin8 hn1 hmpos (BstLean.Part141.bA n (M₁, M₂)) hK (L := 8) (by norm_num))
      intro M₃ h
      exact h.2
    · have hsub0 : {M₃ : Matrix (Fin n) (Fin (mW n)) ℝ | (M₂, M₃) ∈ Prod.mk M₁ ⁻¹' Lo} ⊆ ∅ :=
        fun M₃ h => hK h.1
      have h0 := measureReal_mono (μ := gaussMat n (mW n) (2 / (mW n : ℝ))) hsub0
        (measure_ne_top _ _)
      rw [measureReal_empty] at h0
      exact h0.trans (by positivity)
  have hGp := BstLean.Part151.wBadW151 hn4
  -- the inclusion
  have hsub : {W : MlpParam (2 * n) (mW n) n | (cenA W, tauWA W) ∉ Wd8 n} ⊆
      ((BstLean.Part145.goodWAG (BstLean.Part145.Gwin n))ᶜ ∪ U) ∪ Lo := by
    intro W hW
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
    obtain ⟨⟨hg, hnU⟩, hnLo⟩ := hc
    apply hW
    obtain ⟨hB, hτ, h3, h4⟩ :=
      BstLean.Part149.winA (BstLean.Part145.goodEvFR hn4).to0 hn4 (θ := (W.1, W.2.1)) hg
    have hτe : tauWA W = BstLean.Part141.tauA n (W.1, W.2.1) := rfl
    simp only [hU, hLo, mem_ofPred_eq, not_lt, not_and, not_le] at hnU hnLo
    have hnLo' := hnLo hB
    set B : ℝ := 2 / (mW n : ℝ) * normSq (BstLean.Part141.bA n (W.1, W.2.1)) with hBd
    set T : ℝ := BstLean.Part141.tauA n (W.1, W.2.1) ^ 2 with hTd
    set N : ℝ := normSq (cenA W) with hNd
    have hT : 0 < T := by positivity
    have hN0 : 0 ≤ N := normSq_nonneg _
    have hBT : 0 < B + T := by linarith
    rw [le_div_iff₀ hBT] at h3
    rw [div_le_iff₀ hBT] at h4
    -- numerics
    have hs1 : √(8 / (n : ℝ)) ≤ 1 / 32 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      rw [div_le_iff₀ hn0]
      nlinarith
    have hs2 : √((n : ℝ) * 8) ≤ 1 / 32 * n := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith
    have hs3 : 2 * 8 / (n : ℝ) ≤ 1 / 512 := by
      rw [div_le_iff₀ hn0]
      linarith
    have hδ : BstLean.Part151.deltaC n 8 ≤ 64454 / 1000000 := by
      unfold BstLean.Part151.deltaC
      linarith
    have hBn : 0 < B * n := by positivity
    have hNu : N ≤ B * n * (1064454 / 1000000) := by
      refine hnU.trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith) hBn.le
    have hNl : B * n * (9375 / 10000) ≤ N := by
      refine le_trans ?_ hnLo'.le
      have : B * ((n : ℝ) * (9375 / 10000)) ≤ B * ((n : ℝ) - 2 * √((n : ℝ) * 8)) :=
        mul_le_mul_of_nonneg_left (by linarith) hB.le
      linarith
    have h3n : 462 / 1000 * (B * n + T * n) ≤ B * n := by nlinarith
    have h4n : B * n ≤ 527 / 1000 * (B * n + T * n) := by nlinarith
    have hTn : 0 < T * n := by positivity
    have hden : 0 < N + (n : ℝ) * T := by nlinarith
    show 457 / 1000 ≤ thetaC (cenA W) (tauWA W) ∧ thetaC (cenA W) (tauWA W) ≤ 555 / 1000
    unfold thetaC
    rw [rhoC_sqP, hτe]
    constructor
    · rw [le_div_iff₀ hden]
      linarith
    · rw [div_le_iff₀ hden]
      linarith
  have h1 := measureReal_mono (μ := mlpGauss (2 * n) (mW n) n) hsub (measure_ne_top _ _)
  have h2 := measureReal_union_le (μ := mlpGauss (2 * n) (mW n) n)
    ((BstLean.Part145.goodWAG (BstLean.Part145.Gwin n))ᶜ ∪ U) Lo
  have h3 := measureReal_union_le (μ := mlpGauss (2 * n) (mW n) n)
    (BstLean.Part145.goodWAG (BstLean.Part145.Gwin n))ᶜ U
  linarith

end BstLean.Part154
