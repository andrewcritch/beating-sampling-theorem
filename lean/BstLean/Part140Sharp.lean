import BstLean.Part140Final

/-!
# Part 140: the bad hidden event with its true rate, and level `99/100` at the explicit scale

Role: `delegations/statements/p140-spec.md`, item 3 (more). `goodHat_prob` has the bound
`0.002 + 70/n` of the bad hidden event; the two events of the computed centre have in fact a
probability of order `n²/m_W ≤ n^{−3/2}`.

* `goodDist_prob_sharp`, `goodT_prob_sharp`, `goodHat_prob_sharp`, `badHat_prob_sharp`:
  `Pr(goodHat n fails) ≤ 0.002 + 3635·ρ + 3212000·ρ/n`, `ρ = n²/m_W`.
* **`hatExplicit140_sharp`**: `Pr(|ĝ − B| ≤ ε·scale139 n) ≥
  1 − (0.002 + 3635·ρ + 3212000·ρ/n + 9/(ε²n))`.
* **`hatExplicit140_99`**: for every `n ≥ 10000`:
  `Pr(|ĝ − B| ≤ (1/2)·scale139 n) ≥ 99/100` (the explicit scale `√(S(1 − Q))`, NOT the realized
  spread; the range overlaps the frontier interval).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM

section sharp

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `Pr(t|b̂ − h̄|² > γ·Xc/N) ≤ 672·(n²/m_W)/(Xc − 8/25)²`. -/
theorem goodDist_prob_sharp {Xc : ℝ} (hXc : 8 / 25 < Xc) :
    (hidGauss (2 * n) (mW n)).real (goodDist n Xc)ᶜ ≤
      672 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (Xc - 8 / 25) ^ 2 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hX0 : 0 < Xc - 8 / 25 := by linarith
  have e : (goodDist n Xc)ᶜ = {θ | 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) <
      dist2 (2 * n) (mW n) θ} := by
    ext θ
    simp [goodDist, not_le]
  rw [e]
  refine (distBad_gen (N := 2 * n) (m := mW n) (by omega) hm hXc).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [hNcast, mul_pow]
  have a := mul_le_mul_of_nonneg_left (cDst_sq_le hn) (sq_nonneg (2 * (n : ℝ)))
  have e1 : (2 * (n : ℝ)) ^ 2 * (168 / (mW n : ℝ)) = 672 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
  rw [e1] at a
  exact a

/-- `Pr(goodT n dT fails) ≤ 8.03·(n²/m_W)/(n·dT)`. -/
theorem goodT_prob_sharp {dT : ℝ} (hdT : 0 < dT) :
    (hidGauss (2 * n) (mW n)).real (goodT n dT)ᶜ ≤
      803 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set B : ℝ := (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT / (n : ℝ) with hB
  have hBpos : 0 < B := by rw [hB, hNcast]; positivity
  have hsub : (goodT n dT)ᶜ ⊆ {θ | B < errT θ} := by
    intro θ hθ
    have h1 : ¬ (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT := hθ
    rw [not_le] at h1
    change B < errT θ
    rw [hB, div_lt_iff₀ hnpos]
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (errT_bad (N := 2 * n) (m := mW n) hN hm hBpos).trans ?_
  have hc := cHat2_sq_le (N := 2 * n) (m := mW n) (by omega) hmM
  have e : (2 / ((2 * n : ℕ) : ℝ) * cHat2 (2 * n) (mW n)) ^ 2 / B =
      (n : ℝ) * cHat2 (2 * n) (mW n) ^ 2 / dT := by
    rw [hB, hNcast]
    field_simp
  rw [e]
  have h2 : (n : ℝ) * cHat2 (2 * n) (mW n) ^ 2 ≤ (n : ℝ) * (803 / 100 / (mW n : ℝ)) :=
    mul_le_mul_of_nonneg_left hc hnpos.le
  have h3 : (n : ℝ) * (803 / 100 / (mW n : ℝ)) / dT =
      803 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) := by
    field_simp
  rw [← h3]
  exact div_le_div_of_nonneg_right h2 hdT.le

/-- **The bad hidden event with its true rate**:
`Pr(goodHat n fails) ≤ 0.002 + 3635·ρ + 3212000·ρ/n`, `ρ = n²/m_W`. -/
theorem goodHat_prob_sharp :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤
      2 / 1000 + 3635 * ((n : ℝ) ^ 2 / (mW n : ℝ)) +
        3212000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have hρ : (0 : ℝ) ≤ (n : ℝ) ^ 2 / (mW n : ℝ) := by positivity
  set P := hidGauss (2 * n) (mW n) with hP
  have h1 : P.real (good136 n)ᶜ ≤ 2 / 1000 := by
    rw [measureReal_compl (good136_meas hn1), probReal_univ]
    have := good136_prob hn
    linarith
  have h2 : P.real (goodDist n (3 / 4))ᶜ ≤ 3635 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by
    refine (goodDist_prob_sharp hn (by norm_num)).trans ?_
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have h3 : P.real (goodT n (1 / 400000))ᶜ ≤
      3212000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) := by
    refine (goodT_prob_sharp hn (by norm_num)).trans (le_of_eq ?_)
    field_simp
    ring
  have hsub : (goodHat n)ᶜ ⊆
      ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ := by
    intro θ hθ
    simp only [goodHat, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add
      ((measureReal_union_le _ _).trans (add_le_add h1 h2)) h3))

/-- The same as an event of `(W, A, F)`. -/
theorem badHat_prob_sharp :
    (mlpTriple 2 n).real {t | t.1 ∉ goodWH n} ≤
      2 / 1000 + 3635 * ((n : ℝ) ^ 2 / (mW n : ℝ)) +
        3212000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have mG := goodWH_meas (n := n) hn1
  have hmS := goodHat_meas (n := n) hn1
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have e1 : {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWH n} = (goodWH n)ᶜ ×ˢ (Set.univ : Set (MlpParam n (mA n) n ×
        MlpParam n (mF n) 1)) := by
    ext t; simp
  have e : goodWH n =
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) ⁻¹' goodHat n := rfl
  have hmap : (mlpGauss (2 * n) (mW n) n).map
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) = hidGauss (2 * n) (mW n) := by
    unfold mlpGauss hidGauss
    have h1 : (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) =
        Prod.map id Prod.fst := by
      funext W; rfl
    rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod]
    simp
  have hf : Measurable (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have e2 : (mlpGauss (2 * n) (mW n) n).real (goodWH n) =
      (hidGauss (2 * n) (mW n)).real (goodHat n) := by
    rw [e, ← map_measureReal_apply hf hmS, hmap]
  rw [e0, e1, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def,
    measureReal_compl mG, probReal_univ, e2]
  have h := goodHat_prob_sharp hn
  rw [measureReal_compl hmS, probReal_univ] at h
  exact h

/-- **The explicit scale, with the true rate of the bad hidden event.** For `n ≥ 4096`, `ε > 0`,
`ρ = n²/m_W`: `Pr(|ĝ − B| ≤ ε·scale139 n) ≥
  1 − (0.002 + 3635·ρ + 3212000·ρ/n + 9/(ε²n))`. -/
theorem hatExplicit140_sharp {ε : ℝ} (hε : 0 < ε) :
    1 - (2 / 1000 + 3635 * ((n : ℝ) ^ 2 / (mW n : ℝ)) +
        3212000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) + 9 / (ε ^ 2 * (n : ℝ))) ≤
      (mlpTriple 2 n).real
        {t | |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} :=
  hatExplicit140_core hn hε (badHat_prob_sharp hn)

end sharp

/-- **Level `99/100` at the explicit scale, inside the frontier interval.** For every
`n ≥ 10000`: `Pr_{W,A,F}(|ĝ − B| ≤ (1/2)·scale139 n) ≥ 99/100`, with
`scale139 n = √((4/n)(1 − κ^{∘6}(0)))` (NOT the realized spread `sd`). -/
theorem hatExplicit140_99 {n : ℕ} (hn : 10000 ≤ n) :
    99 / 100 ≤ (mlpTriple 2 n).real
      {t | |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ 1 / 2 * scale139 n} := by
  have hx : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := hatExplicit140_sharp (n := n) (by omega) (ε := 1 / 2) (by norm_num)
  have hρ : (n : ℝ) ^ 2 / (mW n : ℝ) ≤ 1 / 1000000 :=
    ratio_le (n0 := 10000) (by norm_num) hn (by norm_num) (by norm_num)
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million (by omega : 4096 ≤ n)
    linarith
  have hρ0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / (mW n : ℝ) := by positivity
  have t1 : 3635 * ((n : ℝ) ^ 2 / (mW n : ℝ)) ≤ 3635 / 1000000 := by nlinarith
  have t2 : 3212000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) ≤ 322 / 1000000 := by
    rw [div_le_iff₀ hx0]
    nlinarith
  have t3 : 9 / ((1 / 2 : ℝ) ^ 2 * (n : ℝ)) ≤ 3600 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end BstLean.Part140

open BstLean.Part140 in
#print axioms goodHat_prob_sharp
open BstLean.Part140 in
#print axioms badHat_prob_sharp
open BstLean.Part140 in
#print axioms hatExplicit140_sharp
open BstLean.Part140 in
#print axioms hatExplicit140_99
