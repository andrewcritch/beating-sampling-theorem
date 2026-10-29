import BstLean.Part139Err
import BstLean.Part139Spread

/-!
# Part 139, item 3: the mean over the cheap stand-in is within `sd/2` of `B`

Role: `delegations/statements/p139-spec.md`, item 3 (the headline). Compare with
`MM-best-result.md` Theorem 3 and `onW17c-cx.md` §6. The centre is the exact mean hidden vector
`h̄` (which no cheap program has); the estimate `gCheap` is an exact mean (no sampling).

* `okSet n`: the event `|g₀ − B| ≤ sd/2` of `(W, A, F)`.
* **`standInSucceeds139_formula`**: for `n ≥ 4096`, `0 < θ < 1`, `0 < ζ < 1`:
  `Pr(okSet) ≥ 1 − (0.002 + 4·(2·(0.99/n) + 8·EH n ζ)/(θ(1 − Q)) + v_n/((1 − θ)(1 − Q))²)`.
* **`standInSucceeds139`** (the headline): for every `n ≥ 4096`: `Pr(okSet) ≥ 51/100`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136 BstLean.Part138

/-- **The success event**: the cheap estimate `g₀ = E_{ν′_W} F(A(x))` is within half of the
realized spread of the target: `|g₀ − B| ≤ sd/2`. -/
def okSet (n : ℕ) : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | |gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ sdn t.1 t.2.1 t.2.2 / 2}

lemma sdn_nonneg' {N mW n mA mF : ℕ} (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) : 0 ≤ sdn W A F := Real.sqrt_nonneg _

/-- The probability that `W` is not in the good event, as an event of `(W, A, F)`. -/
lemma bad_prob {n : ℕ} (hn : 4096 ≤ n) :
    (mlpTriple 2 n).real {t | t.1 ∉ goodW n} ≤ 2 / 1000 := by
  have hn1 : 1 ≤ n := by omega
  have mG := goodW_meas (n := n) hn1
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have e1 : {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodW n} = (goodW n)ᶜ ×ˢ (Set.univ : Set (MlpParam n (mA n) n ×
        MlpParam n (mF n) 1)) := by
    ext t; simp
  rw [e0, e1, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def,
    measureReal_compl mG, probReal_univ]
  have := goodW_prob hn
  linarith

/-- **The headline in formula form.** For `n ≥ 4096`, `0 < θ < 1` and `0 < ζ < 1`, with
`Q = κ^{∘6}(0)`, `v_n = vSpread n`:
`Pr_{W,A,F}(|g₀ − B| ≤ sd/2) ≥
  1 − (0.002 + 4·(2·(0.99/n) + 8·EH n ζ)/(θ(1 − Q)) + v_n/((1 − θ)(1 − Q))²)`. -/
theorem standInSucceeds139_formula {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    1 - (2 / 1000 + 4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) / (θ * (1 - kappa^[6] 0)) +
        vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2) ≤
      (mlpTriple 2 n).real (okSet n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set S : ℝ := 4 / (n : ℝ) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set s : ℝ := θ * (S * (1 - kappa^[6] 0)) / 4 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  set T := mlpTriple 2 n with hT
  have h1 := bad_prob hn
  have h2 := errTail139 hn hζ0 hζ1 hs0
  have h3 := spreadLow139 hn hθ1
  have hcov : (okSet n)ᶜ ⊆ {t | t.1 ∉ goodW n} ∪ ({t | s ≤ errG n t} ∪
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))}) := by
    intro t ht
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_le, not_lt] at hc
    obtain ⟨hg, he, hsd⟩ := hc
    apply ht
    change |gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ sdn t.1 t.2.1 t.2.2 / 2
    unfold errG at he
    rw [Set.indicator_of_mem hg] at he
    have hsd0 := sdn_nonneg' t.1 t.2.1 t.2.2
    have hsq : (gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2 ≤
        (sdn t.1 t.2.1 t.2.2 / 2) ^ 2 := by
      rw [hs] at he; nlinarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
  have hle : T.real (okSet n)ᶜ ≤ 2 / 1000 +
      ((2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) * (4 / (n : ℝ)) / s +
        vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2) := by
    calc T.real (okSet n)ᶜ ≤ T.real ({t | t.1 ∉ goodW n} ∪ ({t | s ≤ errG n t} ∪
          {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))})) :=
          measureReal_mono hcov (measure_ne_top _ _)
      _ ≤ T.real {t | t.1 ∉ goodW n} + T.real ({t | s ≤ errG n t} ∪
          {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))}) := measureReal_union_le _ _
      _ ≤ T.real {t | t.1 ∉ goodW n} + (T.real {t | s ≤ errG n t} +
          T.real {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (S * (1 - kappa^[6] 0))}) :=
          add_le_add le_rfl (measureReal_union_le _ _)
      _ ≤ _ := add_le_add h1 (add_le_add h2 h3)
  have hcompl : T.real (okSet n) + T.real (okSet n)ᶜ ≥ 1 := by
    have a1 := measureReal_union_le (μ := T) (okSet n) (okSet n)ᶜ
    rw [Set.union_compl_self, probReal_univ] at a1
    exact a1
  have e : (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) * (4 / (n : ℝ)) / s =
      4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) / (θ * (1 - kappa^[6] 0)) := by
    rw [hs, hS]
    field_simp
  rw [e] at hle
  linarith

/-- `n/m_W ≤ 2⁻³⁰` for `n ≥ 4096`. -/
lemma n_div_mW_le {n : ℕ} (hn : 4096 ≤ n) : (n : ℝ) / (mW n : ℝ) ≤ 1 / 1073741824 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < mW n := by
    have := mW_ge hn
    exact_mod_cast (by omega : 0 < mW n)
  have h := n_div_mW_sq hn
  have h5 : (4096 : ℝ) ^ 5 ≤ (n : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hn' 5
  have h2 : ((n : ℝ) / (mW n : ℝ)) ^ 2 ≤ (1 / 1073741824) ^ 2 := by
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h0 : 0 ≤ (n : ℝ) / (mW n : ℝ) := by positivity
  exact (abs_le_of_sq_le_sq' h2 (by norm_num)).2

/-- **The headline (`standInSucceeds139`).** For every `n ≥ 4096`, with `(W, A, F)` three
independent random ReLU networks of the widths of the Focus (`r = 2`), `B = Bn W A F` the
target, `sd = sdn W A F` the realized spread and `g₀ = gCheap W A F` the exact mean of `F∘A`
over the cheap stand-in of `W`:
`Pr_{W,A,F}(|g₀ − B| ≤ sd/2) ≥ 51/100` (failure probability `p_n ≤ 49/100`). -/
theorem standInSucceeds139 {n : ℕ} (hn : 4096 ≤ n) :
    51 / 100 ≤ (mlpTriple 2 n).real (okSet n) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := standInSucceeds139_formula hn (θ := 1 / 10) (by norm_num) (by norm_num)
    (ζ := 1 / 20) (by norm_num) (by norm_num)
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy : (222 : ℝ) / 1000 ≤ 1 - kappa^[6] 0 := by linarith
  have hv := vSpread_le hn
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  have hEH := EH_le hn
  have hEH0 := (EH_pos hn (by norm_num : (0 : ℝ) < 1 / 20)).le
  have hnm := n_div_mW_le hn
  have hEH' : EH n (1 / 20) ≤ 470 / 1073741824 := by
    have e : 470 * (n : ℝ) / (mW n : ℝ) = 470 * ((n : ℝ) / (mW n : ℝ)) := by ring
    rw [e] at hEH
    linarith
  have hinv : 99 / 100 / (n : ℝ) ≤ 99 / 100 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
  have hinv0 : (0 : ℝ) ≤ 99 / 100 / (n : ℝ) := by positivity
  -- the Markov term
  have t1 : 4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20)) /
      (1 / 10 * (1 - kappa^[6] 0)) ≤ 88 / 1000 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  -- the Chebyshev term
  have t2 : vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤ 392 / 1000 := by
    have hden : ((1 - 1 / 10) * (222 / 1000 : ℝ)) ^ 2 ≤
        ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  linarith

end BstLean.Part139

open BstLean.Part139 in
#print axioms standInSucceeds139_formula
open BstLean.Part139 in
#print axioms standInSucceeds139
