import BstLean.Part264Direction
import BstLean.Part264HS
import BstLean.Part277Caps

/-! Part 277, monotone comparisons: the dimension comparisons of `Part264HS`,
`Part264DirectionError` and `Part264Direction` on a base `n0 ≥ 8000`.
Each `fooP` says `X n ≤ X n0` for `n0 ≤ n`. The caps `X n0` are the explicit functions already
in the project. The numeric caps at a given `n0` come from the generator (they are data), so
`direction_budget_leP` takes them as hypotheses at `n0`. -/
namespace BstLean.Part277
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part209 BstLean.Part194 BstLean.Part211
  BstLean.Part215 BstLean.Part219

/-! ## Part 264HS: the Hilbert--Schmidt profile -/

theorem S0_comparisonsP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) :
    S0 n0 ≤ S0 n ∧ (n : ℝ) / S0 n ≤ n0 / S0 n0 := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n0 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hfrac : 12 * ((n : ℝ) - 1) / (n : ℝ)^2 ≤ 12 * ((n0 : ℝ) - 1) / (n0 : ℝ)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hnpos) (sq_pos_of_pos hn0)).mpr
    have hprod : 0 ≤ ((n : ℝ) - n0) * (((n0 : ℝ) - 1) * (n : ℝ) - n0) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith only [hprod]
  have hnorm : √(12 * ((n : ℝ) - 1) / (n : ℝ)^2) = √(12 * ((n : ℝ) - 1)) / n := by
    rw [sqrt_div (by nlinarith), sqrt_sq hnpos.le]
  have hnorm0 : √(12 * ((n0 : ℝ) - 1) / (n0 : ℝ)^2) = √(12 * ((n0 : ℝ) - 1)) / n0 := by
    rw [sqrt_div (by nlinarith), sqrt_sq hn0.le]
  have hs := sqrt_le_sqrt hfrac
  rw [hnorm, hnorm0] at hs
  have hi : 1 / (n : ℝ) ≤ 1 / (n0 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hn0 hnR
  have hscaled : S0 n0 / n0 ≤ S0 n / n := by
    unfold S0
    have he : ((n : ℝ) - 1 - 2 * √(12 * ((n : ℝ) - 1))) / n =
        1 - 1 / (n : ℝ) - 2 * (√(12 * ((n : ℝ) - 1)) / n) := by
      field_simp
      <;> ring
    have he0 : ((n0 : ℝ) - 1 - 2 * √(12 * ((n0 : ℝ) - 1))) / n0 =
        1 - 1 / (n0 : ℝ) - 2 * (√(12 * ((n0 : ℝ) - 1)) / n0) := by
      field_simp
      <;> ring
    rw [he, he0]
    linarith
  have hS0 : 0 < S0 n0 := lt_trans (by norm_num) (S0_gt_one (by omega : 64 ≤ n0))
  have hnScaled := (le_div_iff₀ hnpos).mp hscaled
  have hSn : S0 n0 ≤ S0 n := by
    calc
      _ = S0 n0 / n0 * n0 := by field_simp
      _ ≤ S0 n0 / n0 * n := mul_le_mul_of_nonneg_left hnR (by positivity)
      _ ≤ _ := hnScaled
  refine ⟨hSn, ?_⟩
  apply (div_le_div_iff₀ (hS0.trans_le hSn) hS0).mpr
  have hcross := (div_le_div_iff₀ hn0 hnpos).mp hscaled
  nlinarith only [hcross]

theorem J0_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    J0 n0 θ ≤ J0 n θ := by
  obtain ⟨hS, hRatio⟩ := S0_comparisonsP h8 hn
  have hS0 : 0 < S0 n0 := lt_trans (by norm_num) (S0_gt_one (by omega : 64 ≤ n0))
  have hSn := hS0.trans_le hS
  have hAx : 0 ≤ axialC θ := by
    unfold axialC
    exact div_nonneg (by linarith) (by positivity)
  have hInner : 2 * axialC θ * n / S0 n ≤ 2 * axialC θ * n0 / S0 n0 := by
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hRatio (by positivity : 0 ≤ 2 * axialC θ)
  have hDen : √(1 + 2 * axialC θ * n / S0 n) ≤
      √(1 + 2 * axialC θ * n0 / S0 n0) := sqrt_le_sqrt (by linarith)
  have hDen0 : 0 < √(1 + 2 * axialC θ * n / S0 n) := by positivity
  have he : 0 ≤ 1 - exp (-12 : ℝ) := by
    have h := exp_le_one_iff.mpr (by norm_num : (-12 : ℝ) ≤ 0)
    linarith
  have hInv : 1 / S0 n ≤ 1 / S0 n0 := div_le_div_of_nonneg_left (by norm_num) hS0 hS
  have hNum : (1 - exp (-12)) * (1 - 1 / S0 n0) ≤
      (1 - exp (-12)) * (1 - 1 / S0 n) := mul_le_mul_of_nonneg_left (by linarith) he
  have hInv1 : 1 / S0 n ≤ 1 := by
    apply (div_le_one hSn).mpr
    have := S0_gt_one (by omega : 64 ≤ n)
    linarith
  unfold J0
  exact div_le_div₀ (mul_nonneg he (by linarith)) hNum hDen0 hDen

theorem hsProfile_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) : hsProfile n θ 0.006 ≤ hsProfile n0 θ 0.006 := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hj := J0_leP h8 hn hθ hθ1
  have hq : qHS n θ ≤ qHS n0 θ := by unfold qHS; linarith
  have hq0 : 0 ≤ qHS n θ := by
    have h := J0_bounds (by omega : 64 ≤ n) hθ hθ1
    unfold qHS
    linarith [h.2.2.1]
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hch : CH n θ 0.006 ≤ CH n0 θ 0.006 := by
    unfold CH
    gcongr
  have hroot : √(n0 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hroot2 : √(√(n0 : ℝ)) ≤ √(√(n : ℝ)) := sqrt_le_sqrt hroot
  have ha : a0 n ≤ a0 n0 := by unfold a0; gcongr
  have ha0 : 0 ≤ a0 n := by unfold a0; positivity
  rw [hsProfile_eq_paper (n := n) (by omega) hθ,
    hsProfile_eq_paper (n := n0) (by omega) hθ]
  gcongr

/-! ## Part 264DirectionError: the pair error allowance -/

theorem lengthAlpha_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) :
    lengthAlpha n P ≤ lengthAlpha n0 P := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hg := twoGaussConst_nonneg P
  unfold lengthAlpha
  gcongr

theorem pairQ_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) :
    pairQ n P ≤ pairQ n0 P := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hroot : √(n0 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hg := gaussMomConst_nonneg P
  rw [BstLean.Part264.pairQ_normalized (n := n) (by omega) P,
    BstLean.Part264.pairQ_normalized (n := n0) (by omega) P]
  gcongr

theorem tangentU_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) :
    tangentU n P ≤ tangentU n0 P := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hroot : √(n0 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hg := gaussMomConst_nonneg (2 * P)
  have ht := twoGaussConst_nonneg P
  rw [BstLean.Part264.tangentU_normalized (n := n) (by omega) P,
    BstLean.Part264.tangentU_normalized (n := n0) (by omega) P]
  gcongr

theorem overlapC_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) :
    overlapC n P ≤ overlapC n0 P := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  rw [BstLean.Part264.overlapC_normalized (n := n) (by omega) P,
    BstLean.Part264.overlapC_normalized (n := n0) (by omega) P]
  gcongr

theorem pairV_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) :
    pairV n P ≤ pairV n0 P := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hq := pairQ_leP h8 hn P
  have hlog : 0 ≤ log (162 : ℝ) := log_nonneg (by norm_num)
  have hf : 0 ≤ factorialRoot (2 * P) := by unfold factorialRoot; positivity
  rw [BstLean.Part264.pairV_normalized (n := n) (by omega) P,
    BstLean.Part264.pairV_normalized (n := n0) (by omega) P]
  gcongr

theorem pairDelta_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) (η : ℝ) :
    pairDelta n P η ≤ pairDelta n0 P η := by
  have ho := overlapC_leP h8 hn P
  have hl := lengthAlpha_leP h8 hn P
  have hl2 := lengthAlpha_leP h8 hn (2 * P)
  have hl0 := lengthAlpha_nonneg n (2 * P)
  unfold pairDelta
  gcongr

theorem lowLengthProb_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) :
    lowLengthProb n (1 / 100) ≤ lowLengthProb n0 (1 / 100) := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hdiv : 2 / (n : ℝ) ≤ 2 / (n0 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hn0p hnR
  have harg : (n0 : ℝ) * (1 / 100) - 2 / n0 ≤ (n : ℝ) * (1 / 100) - 2 / n := by
    linarith
  have h2n : 2 / (n0 : ℝ) ≤ 2 / 8000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  have hs := pow_le_pow_left₀ (by nlinarith : (0 : ℝ) ≤ n0 * (1 / 100) - 2 / n0) harg 2
  rw [BstLean.Part264.lowLengthProb_normalized (n := n) (by omega),
    BstLean.Part264.lowLengthProb_normalized (n := n0) (by omega)]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)

theorem complementRoot_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) :
    complementRoot n P ≤ complementRoot n0 P := by
  have ht := tangentU_leP h8 hn (4 * P)
  have hl := lengthAlpha_leP h8 hn (8 * P)
  have hl0 := lengthAlpha_nonneg n (8 * P)
  unfold complementRoot
  gcongr

theorem complementB_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (P : ℕ) :
    complementB n P (1 / 100) ≤ complementB n0 P (1 / 100) := by
  have hc := complementRoot_leP h8 hn P
  have hl := lowLengthProb_leP h8 hn
  have hc0 := complementRoot_nonneg n P
  have hlow0 : 0 ≤ lowLengthProb n (1 / 100) := by unfold lowLengthProb; positivity
  unfold complementB
  exact mul_le_mul hc (Real.rpow_le_rpow hlow0 hl (by positivity))
    (rpow_nonneg hlow0 _) (complementRoot_nonneg n0 P)

theorem pairEpsilon_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) :
    pairEpsilon n 16 (1 / 100) ≤ pairEpsilon n0 16 (1 / 100) := by
  have hV := pairV_leP h8 hn 32
  have hQ := pairQ_leP h8 hn 32
  have hd := pairDelta_leP h8 hn 16 (1 / 100)
  have ht := tangentU_leP h8 hn 32
  have hl := lengthAlpha_leP h8 hn 64
  have hc := complementB_leP h8 hn 16
  have hV0 := pairV_nonneg n 32
  have hVOld0 := pairV_nonneg n0 32
  have hQ0 := pairQ_nonneg n 32
  have hl0 := lengthAlpha_nonneg n 64
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  unfold pairEpsilon meanEpsilon fluctuationRoot
  norm_num only [Nat.reduceMul] at *
  gcongr <;> positivity

/-! ## Part 264Direction: the direction budget -/

theorem radius_nonneg_and_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (j : ℕ) (hj : j ≤ 96)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) :
    0 ≤ radiusCoefficient n j θ ∧ radiusCoefficient n j θ ≤ radiusCoefficient n0 j θ := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hc : (2 * j + 2 : ℝ) * θ / n ≤ 194 * (54 / 100 : ℝ) / 8000 := by
    rw [div_le_div_iff₀ hnp (by norm_num)]
    have h1 : (2 * j + 2 : ℝ) * θ ≤ 194 * (54 / 100) := by
      apply mul_le_mul (by linarith) hθhi hθ (by norm_num)
    nlinarith
  have hc0 : (2 * j + 2 : ℝ) * θ / n0 ≤ 194 * (54 / 100 : ℝ) / 8000 := by
    rw [div_le_div_iff₀ hn0p (by norm_num)]
    have h1 : (2 * j + 2 : ℝ) * θ ≤ 194 * (54 / 100) := by
      apply mul_le_mul (by linarith) hθhi hθ (by norm_num)
    nlinarith
  have hd : (2 * j + 2 : ℝ) * θ / n ≤ (2 * j + 2 : ℝ) * θ / n0 := by gcongr
  unfold radiusCoefficient
  exact ⟨div_nonneg hθ (by linarith),
    div_le_div_of_nonneg_left hθ (by linarith) (by linarith)⟩

theorem amplitude_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) : paperAmplitude n θ ≤ paperAmplitude n0 θ := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hd : 4 * θ / n ≤ 4 * θ / n0 := by gcongr
  have hdd : 4 * θ / (n0 : ℝ) ≤ 4 * (54 / 100) / 8000 := by
    rw [div_le_div_iff₀ hn0p (by norm_num)]
    nlinarith
  have hnum : 0 ≤ 1 - θ := by linarith
  unfold paperAmplitude
  apply sqrt_le_sqrt
  exact div_le_div_of_nonneg_left hnum (by linarith) (by linarith)

theorem bias_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) : paperBias n θ ≤ paperBias n0 θ := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hr := radius_nonneg_and_leP h8 hn 4 (by norm_num) hθ hθhi
  have hr0 := hr.1
  have hrle := hr.2
  have hrold0 := hr.1.trans hr.2
  unfold paperBias
  gcongr <;> positivity

theorem paperIdeal_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θ e : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) (he : 0 < e) :
    paperIdeal n θ e ≤ paperIdeal n0 θ e := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hroot : √(n0 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have h1 := radius_nonneg_and_leP h8 hn 1 (by norm_num) hθ hθhi
  have h24 := radius_nonneg_and_leP h8 hn 24 (by norm_num) hθ hθhi
  have h48 := radius_nonneg_and_leP h8 hn 48 (by norm_num) hθ hθhi
  have h96 := radius_nonneg_and_leP h8 hn 96 (by norm_num) hθ hθhi
  have h4 := radius_nonneg_and_leP h8 hn 4 (by norm_num) hθ hθhi
  have h40 := h4.1
  have h10 := h1.1
  have h240 := h24.1
  have h480 := h48.1
  have h960 := h96.1
  have h1le := h1.2
  have h24le := h24.2
  have h48le := h48.2
  have h96le := h96.2
  have h24old0 := h24.1.trans h24.2
  have h1old0 := h1.1.trans h1.2
  have h48old0 := h48.1.trans h48.2
  have h96old0 := h96.1.trans h96.2
  have ha := amplitude_leP h8 hn hθ hθhi
  have hb := bias_leP h8 hn hθ hθhi
  have hk := kernelSlope_nonneg (1 - θ)
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  have hb0 : 0 ≤ paperBias n θ := by unfold paperBias; positivity
  have hbold0 := hb0.trans hb
  have ha0 : 0 ≤ paperAmplitude n θ := sqrt_nonneg _
  have haold0 : 0 ≤ paperAmplitude n0 θ := sqrt_nonneg _
  unfold paperIdeal
  gcongr <;> positivity

/-- **The direction budget on `n ≥ n0`.** The numeric inputs at `n0` are hypotheses:
`I0` bounds the ideal term on the window, `ε0` bounds the pair error at `n0`, and `Rc`
bounds the radius coefficient at `n0`. `sR`, `ρ0` and `MP`, `xi0` are rational witnesses. -/
theorem direction_budget_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞) {θlo θhi e0 xi0 MP I0 ε0 Rc sR ρ0 : ℝ}
    (hθhi : θhi ≤ 54 / 100) (hw : BstLean.Part150.thetaC c τ ∈ Icc θlo θhi)
    (hθlo : 0 ≤ θlo) (he0 : 0 < e0) (he : e0 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ xi0)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ MP) (hMP : 0 ≤ MP)
    (hI : ∀ θ ∈ Icc θlo θhi, ∀ e' : ℝ, e0 ≤ e' → paperIdeal n0 θ e' ≤ I0)
    (hRc : ∀ θ ∈ Icc θlo θhi, radiusCoefficient n0 12 θ ≤ Rc)
    (hε : pairEpsilon n0 16 (1 / 100) ≤ ε0) (hsR : Rc / e0 ≤ sR ^ 2) (hsR0 : 0 ≤ sR)
    (hρ0 : 0 < ρ0) (hρ : ρ0 ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ)) :
    paperDirectionBudget c τ e xi eta δ ≤
      (I0 + ε0 * sR / ρ0 + √(MP * xi0 / ((n0 : ℝ) * e0))) ^ 2 := by
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0p : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hep : 0 < e := lt_of_lt_of_le he0 he
  let θ := BstLean.Part150.thetaC c τ
  have hθ : 0 ≤ θ := hθlo.trans hw.1
  have hθ1 : θ ≤ 54 / 100 := hw.2.trans hθhi
  have hrad := radius_nonneg_and_leP h8 hn 12 (by norm_num) hθ hθ1
  have hR : radiusCoefficient n 12 θ ≤ Rc := hrad.2.trans (hRc θ hw)
  have hRs : √(radiusCoefficient n 12 θ / e) ≤ sR := by
    apply sqrt_le_iff.mpr
    refine ⟨hsR0, ?_⟩
    have hRc0 : 0 ≤ Rc := hrad.1.trans hR
    exact (div_le_div₀ hRc0 hR he0 he).trans hsR
  have heps := (pairEpsilon_leP h8 hn).trans hε
  have heps0 := BstLean.Part209.meanEpsilon_nonneg n 16
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1)
  have hEp0 : 0 ≤ BstLean.Part209.pairEpsilon n 16 (1 / 100) :=
    add_nonneg heps0 (BstLean.Part209.fluctuationRoot_nonneg _ _)
  have hMPxi : operatorAllowance c τ eta δ ^ 2 * xi ≤ MP * xi0 := by
    exact mul_le_mul hop hxi1 hxi hMP
  have htransfer : √(operatorAllowance c τ eta δ ^ 2 * xi / ((n : ℝ) * e)) ≤
      √(MP * xi0 / ((n0 : ℝ) * e0)) := by
    apply sqrt_le_sqrt
    have h1 : operatorAllowance c τ eta δ ^ 2 * xi / ((n : ℝ) * e) ≤
        MP * xi0 / ((n : ℝ) * e) := by gcongr
    have hMX : 0 ≤ MP * xi0 := hMPxi.trans' (by positivity)
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left hMX (by positivity) (by gcongr)
  have hi := hI θ hw e he
  have hi' := (paperIdeal_leP h8 hn hθ hθ1 hep).trans hi
  have hi0 : 0 ≤ paperIdeal n θ e := by
    have hr (j : ℕ) (hj : j ≤ 96) := (radius_nonneg_and_leP h8 hn j hj hθ hθ1).1
    have hr48 := hr 48 (by norm_num)
    have hr96 := hr 96 (by norm_num)
    have hr4 := hr 4 (by norm_num)
    have hk := kernelSlope_nonneg (1 - θ)
    have hrot := BstLean.Part195.rotationConstant_nonneg 24
    unfold paperIdeal paperAmplitude paperBias
    positivity
  unfold paperDirectionBudget
  change (paperIdeal n θ e + _ + _) ^ 2 ≤ _
  have hmid : BstLean.Part209.pairEpsilon n 16 (1 / 100) *
      √(radiusCoefficient n 12 θ / e) / ((7 / 25000 : ℝ) ^ (1 / 64 : ℝ)) ≤ ε0 * sR / ρ0 := by
    have hq : 0 ≤ ε0 := hEp0.trans heps
    calc _ ≤ ε0 * sR / ((7 / 25000 : ℝ) ^ (1 / 64 : ℝ)) := by gcongr
      _ ≤ _ := by gcongr
  have hmid0 : 0 ≤ BstLean.Part209.pairEpsilon n 16 (1 / 100) *
      √(radiusCoefficient n 12 θ / e) / ((7 / 25000 : ℝ) ^ (1 / 64 : ℝ)) := by positivity
  have htr0 : 0 ≤ √(operatorAllowance c τ eta δ ^ 2 * xi / ((n : ℝ) * e)) := sqrt_nonneg _
  have hsum := add_le_add (add_le_add hi' hmid) htransfer
  exact pow_le_pow_left₀ (by positivity) hsum 2

end BstLean.Part277
