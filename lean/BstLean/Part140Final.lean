import BstLean.Part140Err

/-!
# Part 140, item 3 (the headline): the mean over the cheap stand-in with the COMPUTED centre is
within `sd/2` of `B`

Role: `delegations/statements/p140-spec.md`, item 3. Paper sources: `MM-best-result.md`
Theorem 3(a), `onW17c-cx.md` §§5–6.

`(W, A, F)` has the distribution `mlpTriple 2 n` (three independent random ReLU networks, the
widths of the Focus, `r = 2`). `B = Bn W A F`, `sd = sdn W A F` (Part 130).
`ĝ = gHat W A F = E F(A(x))`, `x = sphPt(M₃ b̂ + τ̂₀γ)`, with the computed centre
`b̂ = ψ_s(M₂ h̄₁)` (`bhat`, Part 137) and the scalar `τ̂₀² = t|b̂|²·max(0, t|b̂|²/(γκ₁²) − 1)`
(`tauHat`): both are functions of first-pass quantities of `(M₁, M₂)`; no exact `h̄` is used.

* `okHat n`: the event `|ĝ − B| ≤ sd/2`.
* **`hatSucceeds140_formula`**: for `0 < θ < 1`, `0 < ζ < 1`, `η > 0`:
  `Pr(|ĝ − B| ≤ sd/2) ≥ 1 − (0.002 + 70/n +
     4((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ)/(θ(1 − Q)) + vSpread n/((1 − θ)(1 − Q))²)`,
  `Q = κ^{∘6}(0)`.
* **`hatSucceeds140`** (the headline): `Pr(|ĝ − B| ≤ sd/2) ≥ 1 − (0.002 + 2022/n)`, every
  `n ≥ 4096` (`θ = 1/10`, `ζ = η = 1/20`). `hatSucceeds140_all`: `≥ 1/2` for `n ≥ 4096`;
  `hatSucceeds140_frontier`: `≥ 87/100` for `n ≥ 16384`; `hatSucceeds140_99`: `≥ 99/100` for
  `n ≥ 252750`.
* **`hatExplicit140`**: with the explicit scale `scale139 n = √(S(1 − Q))` in the place of `sd`:
  `Pr(|ĝ − B| ≤ ε·scale139 n) ≥ 1 − (0.002 + 70/n + 9/(ε²n))`.
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

/-- **The success event of the estimate with the computed centre**: `|ĝ − B| ≤ sd/2`. -/
def okHat (n : ℕ) : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ sdn t.1 t.2.1 t.2.2 / 2}

/-- The probability that `W` is not in the good hidden event, as an event of `(W, A, F)`. -/
lemma badHat_prob {n : ℕ} (hn : 4096 ≤ n) :
    (mlpTriple 2 n).real {t | t.1 ∉ goodWH n} ≤ 2 / 1000 + 70 / (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have mG := goodWH_meas (n := n) hn1
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have e1 : {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWH n} = (goodWH n)ᶜ ×ˢ (Set.univ : Set (MlpParam n (mA n) n ×
        MlpParam n (mF n) 1)) := by
    ext t; simp
  rw [e0, e1, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def,
    measureReal_compl mG, probReal_univ]
  have := goodWH_prob hn
  linarith

/-- **The headline in formula form.** For `n ≥ 4096`, `0 < θ < 1`, `0 < ζ < 1` and `η > 0`,
with `Q = κ^{∘6}(0)`, `v_n = vSpread n`:
`Pr_{W,A,F}(|ĝ − B| ≤ sd/2) ≥ 1 − (0.002 + 70/n +
  4·((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ)/(θ(1 − Q)) + v_n/((1 − θ)(1 − Q))²)`. -/
theorem hatSucceeds140_formula {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
    1 - (2 / 1000 + 70 / (n : ℝ) +
        4 * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) /
          (θ * (1 - kappa^[6] 0)) +
        vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2) ≤
      (mlpTriple 2 n).real (okHat n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set S : ℝ := 4 / (n : ℝ) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set s : ℝ := θ * (S * (1 - kappa^[6] 0)) / 4 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  set T := mlpTriple 2 n with hT
  have h1 := badHat_prob hn
  have h2 := errTailHat hn hζ0 hζ1 hη hs0
  have h3 := spreadLow139 hn hθ1
  have hcov : (okHat n)ᶜ ⊆ {t | t.1 ∉ goodWH n} ∪ ({t | s ≤ errGH n t} ∪
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))}) := by
    intro t ht
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_le, not_lt] at hc
    obtain ⟨hg, he, hsd⟩ := hc
    apply ht
    change |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ sdn t.1 t.2.1 t.2.2 / 2
    unfold errGH at he
    rw [Set.indicator_of_mem hg] at he
    have hsd0 := sdn_nonneg' t.1 t.2.1 t.2.2
    have hsq : (gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2 ≤
        (sdn t.1 t.2.1 t.2.2 / 2) ^ 2 := by
      rw [hs] at he; nlinarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
  have hle : T.real (okHat n)ᶜ ≤ 2 / 1000 + 70 / (n : ℝ) +
      (((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ)) / s +
        vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2) := by
    calc T.real (okHat n)ᶜ ≤ T.real ({t | t.1 ∉ goodWH n} ∪ ({t | s ≤ errGH n t} ∪
          {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))})) :=
          measureReal_mono hcov (measure_ne_top _ _)
      _ ≤ T.real {t | t.1 ∉ goodWH n} + T.real ({t | s ≤ errGH n t} ∪
          {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))}) := measureReal_union_le _ _
      _ ≤ T.real {t | t.1 ∉ goodWH n} + (T.real {t | s ≤ errGH n t} +
          T.real {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))}) :=
          add_le_add le_rfl (measureReal_union_le _ _)
      _ ≤ _ := add_le_add h1 (add_le_add h2 h3)
  have hcompl : T.real (okHat n) + T.real (okHat n)ᶜ ≥ 1 := by
    have a1 := measureReal_union_le (μ := T) (okHat n) (okHat n)ᶜ
    rw [Set.union_compl_self, probReal_univ] at a1
    exact a1
  have e : ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ)) / s =
      4 * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) / (θ * (1 - kappa^[6] 0)) := by
    rw [hs, hS]
    field_simp
  rw [e] at hle
  linarith

section rate

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `EHH n (1/20) ≤ (250/262144)/n`. -/
lemma EHH_scale : EHH n (1 / 20) ≤ 250 / 262144 * (1 / (n : ℝ)) := by
  have hEH := EHH_le hn
  have hnm := n_div_mW_scale hn
  have e : 250 * (n : ℝ) / (mW n : ℝ) = 250 * ((n : ℝ) / (mW n : ℝ)) := by ring
  rw [e] at hEH
  have e2 : (1 : ℝ) / 262144 / (n : ℝ) = 1 / 262144 * (1 / (n : ℝ)) := by ring
  rw [e2] at hnm
  linarith

/-- **`hatSucceeds140`** (item 3, the headline). For every `n ≥ 4096`, with `(W, A, F)` three
independent random ReLU networks of the widths of the Focus (`r = 2`), `B = Bn W A F` the target,
`sd = sdn W A F` the realized spread, and `ĝ = gHat W A F` the exact mean of `F∘A` over the
distribution of `sphPt(M₃ b̂ + τ̂₀γ)` (computed centre `b̂ = ψ_s(M₂ h̄₁)`, scalar
`τ̂₀² = t|b̂|²·max(0, t|b̂|²/(γκ₁²) − 1)`):
`Pr_{W,A,F}(|ĝ − B| ≤ sd/2) ≥ 1 − (0.002 + 2022/n)`. -/
theorem hatSucceeds140 :
    1 - (2 / 1000 + 2022 / (n : ℝ)) ≤ (mlpTriple 2 n).real (okHat n) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := hatSucceeds140_formula hn (θ := 1 / 10) (by norm_num) (by norm_num)
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20) (by norm_num)
  have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
  have e105 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
  rw [e84, e105] at h
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hv := vSpread_scale hn
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  have hEH' := EHH_scale hn
  have hEH0 := EHH_nonneg hn (1 / 20)
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * t := by rw [ht]; ring
  have e64 : 64 / (n : ℝ) = 64 * t := by rw [ht]; ring
  have e70 : 70 / (n : ℝ) = 70 * t := by rw [ht]; ring
  have e2022 : 2022 / (n : ℝ) = 2022 * t := by rw [ht]; ring
  rw [e64] at hv
  -- the Markov term
  have t1 : 4 * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) /
      (1 / 10 * (1 - kappa^[6] 0)) ≤ 3595 / 10 * t := by
    rw [e183, div_le_iff₀ (by nlinarith)]
    nlinarith
  -- the Chebyshev term
  have t2 : vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤ 15924 / 10 * t := by
    have hden : ((1 - 1 / 10) * (222757 / 1000000 : ℝ)) ^ 2 ≤
        ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  rw [e2022]
  rw [e70] at h
  linarith

/-- For every `n ≥ 4096`: `Pr(|ĝ − B| ≤ sd/2) ≥ 1/2`. -/
theorem hatSucceeds140_all : 1 / 2 ≤ (mlpTriple 2 n).real (okHat n) := by
  have h := hatSucceeds140 hn
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have : 2022 / (n : ℝ) ≤ 2022 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

/-- In the frontier interval: for `n ≥ 16384`, `Pr(|ĝ − B| ≤ sd/2) ≥ 87/100`. -/
theorem hatSucceeds140_frontier (h16 : 16384 ≤ n) :
    87 / 100 ≤ (mlpTriple 2 n).real (okHat n) := by
  have h := hatSucceeds140 hn
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast h16
  have : 2022 / (n : ℝ) ≤ 2022 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

/-- **Level `99/100`.** For `n ≥ 252750`: `Pr(|ĝ − B| ≤ sd/2) ≥ 99/100`. -/
theorem hatSucceeds140_99 (hbig : 252750 ≤ n) :
    99 / 100 ≤ (mlpTriple 2 n).real (okHat n) := by
  have h := hatSucceeds140 hn
  have hx : (252750 : ℝ) ≤ n := by exact_mod_cast hbig
  have : 2022 / (n : ℝ) ≤ 2022 / 252750 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

/-- The explicit scale, with the probability `p₁` of the bad hidden event as a hypothesis. -/
theorem hatExplicit140_core {ε : ℝ} (hε : 0 < ε) {p₁ : ℝ}
    (h1 : (mlpTriple 2 n).real {t | t.1 ∉ goodWH n} ≤ p₁) :
    1 - (p₁ + 9 / (ε ^ 2 * (n : ℝ))) ≤
      (mlpTriple 2 n).real
        {t | |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set S : ℝ := 4 / (n : ℝ) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set s : ℝ := ε ^ 2 * (S * (1 - kappa^[6] 0)) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  set T := mlpTriple 2 n with hT
  set ok : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
    {t | |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} with hok
  have h2 := errTailHat hn (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
    (by norm_num) hs0
  have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
  have e105 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
  rw [e84, e105] at h2
  have hsc : scale139 n ^ 2 = S * (1 - kappa^[6] 0) := by
    unfold scale139
    rw [Real.sq_sqrt (by positivity)]
  have hsc0 : 0 ≤ scale139 n := by unfold scale139; exact Real.sqrt_nonneg _
  have hcov : okᶜ ⊆ {t | t.1 ∉ goodWH n} ∪ {t | s ≤ errGH n t} := by
    intro t ht
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_le] at hc
    obtain ⟨hg, he⟩ := hc
    apply ht
    change |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n
    unfold errGH at he
    rw [Set.indicator_of_mem hg] at he
    have hsq : (gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2 ≤ (ε * scale139 n) ^ 2 := by
      rw [mul_pow, hsc]
      rw [hs] at he
      exact he.le
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
  have hle : T.real okᶜ ≤ p₁ +
      (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) * (4 / (n : ℝ)) / s :=
    (measureReal_mono hcov (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add h1 h2))
  have hcompl : T.real ok + T.real okᶜ ≥ 1 := by
    have a1 := measureReal_union_le (μ := T) ok okᶜ
    rw [Set.union_compl_self, probReal_univ] at a1
    exact a1
  have hEH' := EHH_scale hn
  have hEH0 := EHH_nonneg hn (1 / 20)
  have ht0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hterm : (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) * (4 / (n : ℝ)) / s ≤
      9 / (ε ^ 2 * (n : ℝ)) := by
    have e : (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) * (4 / (n : ℝ)) / s =
        (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) /
          (ε ^ 2 * (1 - kappa^[6] 0)) := by
      rw [hs, hS]
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * (1 / (n : ℝ)) := by ring
    rw [e183]
    have hnum : 21 / 20 * (183 / 100 * (1 / (n : ℝ))) + 84 * EHH n (1 / 20) ≤
        2002 / 1000 * (1 / (n : ℝ)) := by nlinarith
    have hε2 : 0 < ε ^ 2 := by positivity
    have h5 : (21 / 20 * (183 / 100 * (1 / (n : ℝ))) + 84 * EHH n (1 / 20)) *
        (ε ^ 2 * (n : ℝ)) ≤ 2002 / 1000 * (1 / (n : ℝ)) * (ε ^ 2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    have e5 : 2002 / 1000 * (1 / (n : ℝ)) * (ε ^ 2 * (n : ℝ)) = 2002 / 1000 * ε ^ 2 := by
      field_simp
    rw [e5] at h5
    have h6 : 2002 / 1000 * ε ^ 2 ≤ 9 * (ε ^ 2 * (1 - kappa^[6] 0)) := by nlinarith
    linarith
  linarith

/-- **The explicit scale.** With `scale139 n = √(S(1 − Q))`, `S = 4/n`, in the place of the
realized spread: for every `n ≥ 4096` and `ε > 0`:
`Pr(|ĝ − B| ≤ ε·scale139 n) ≥ 1 − (0.002 + 70/n + 9/(ε²n))`. -/
theorem hatExplicit140 {ε : ℝ} (hε : 0 < ε) :
    1 - (2 / 1000 + 70 / (n : ℝ) + 9 / (ε ^ 2 * (n : ℝ))) ≤
      (mlpTriple 2 n).real
        {t | |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} :=
  hatExplicit140_core hn hε (badHat_prob hn)

end rate

end BstLean.Part140

open BstLean.Part140 in
#print axioms hatSucceeds140_formula
open BstLean.Part140 in
#print axioms hatSucceeds140
open BstLean.Part140 in
#print axioms hatSucceeds140_all
open BstLean.Part140 in
#print axioms hatSucceeds140_frontier
open BstLean.Part140 in
#print axioms hatSucceeds140_99
open BstLean.Part140 in
#print axioms hatExplicit140
