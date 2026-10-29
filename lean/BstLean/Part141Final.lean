import BstLean.Part141Err
import BstLean.Part140All

/-!
# Part 141, item 3 (the headline `arithSucceeds141`): the estimate with the ARITHMETIC centre and
the ARITHMETIC scalar is within `sd/2` of `B`

Role: `delegations/statements/p141-spec.md`, item 3. Compare `MM-best-result.md` Theorem 3(a)
and `onW17c-cx.md` §§5–6.

`(W, A, F)` has the distribution `mlpTriple 2 n` (three independent random ReLU networks, the
widths of the Focus, `r = 2`). `B = Bn W A F`, `sd = sdn W A F` (Part 130).
`g̃ = gA W A F = E F(A(x))`, `x = sphPt(M₃ b̃ + τ̃₀γ)`, with the arithmetic centre `b̃ = bA`
(a finite ReLU sum with rational atoms and weights, the rational constant `cA n`) and the
arithmetic scalar `τ̃₀ = tauA` (`τ̃₀² = t|b̃|²·max(0, t|b̃|²·c̃₁ − 1)`, `c̃₁ = c1A n` rational).

* `badA_prob`: `Pr(W not in goodWA n) ≤ 0.002 + 70/n + 68·10⁶/(qA n)²`.
* **`arithSucceeds141_formula`**: free `θ`, `ζ`, `η`, `η′`.
* **`arithSucceeds141`** (the headline): `Pr(|g̃ − B| ≤ sd/2) ≥ 1 − (0.002 + 2031/n)`, every
  `n ≥ 4096` (`θ = 1/10`, `ζ = η = 1/20`, `η′ = 1/100`).
* `arithSucceeds141_all` (`≥ 1/2`, `n ≥ 4096`), `arithSucceeds141_frontier` (`≥ 87/100`,
  `n ≥ 16384`), `arithSucceeds141_99` (`≥ 99/100`, `n ≥ 253875`).
* **`arithExplicit141`**, `arithExplicit141_sharp`, **`arithExplicit141_99`**: the explicit
  scale `scale139 n = √(S(1 − Q))` in the place of `sd`: level `99/100` at `ε = 1/2` for every
  `n ≥ 10000`.
* `optA141`, `optA141_explicit`: the two-stage forms (the order of Option A).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-- **The success event of the estimate with the arithmetic centre and scalar**:
`|g̃ − B| ≤ sd/2`. -/
def okA (n : ℕ) : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ sdn t.1 t.2.1 t.2.2 / 2}

/-- The probability that `W` is not in the good hidden event, as an event of `(W, A, F)`, from a
bound for `goodHat n`. -/
lemma badA_prob_gen {n : ℕ} (hn : 4096 ≤ n) {p : ℝ}
    (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p) :
    (mlpTriple 2 n).real {t | t.1 ∉ goodWA n} ≤ p + 68000000 / (qA n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have mG := goodWA_meas (n := n) hn1
  have hmS := goodA_meas (n := n) hn1
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have e1 : {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWA n} = (goodWA n)ᶜ ×ˢ (Set.univ : Set (MlpParam n (mA n) n ×
        MlpParam n (mF n) 1)) := by
    ext t; simp
  rw [e0, e1, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]
  have e : (goodWA n)ᶜ =
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) ⁻¹' (goodA n)ᶜ := rfl
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
  rw [e, ← map_measureReal_apply hf hmS.compl, hmap]
  exact goodA_prob_gen hn h1

/-- `Pr(W not in goodWA n) ≤ 0.002 + 70/n + 68·10⁶/(qA n)²`. -/
lemma badA_prob {n : ℕ} (hn : 4096 ≤ n) :
    (mlpTriple 2 n).real {t | t.1 ∉ goodWA n} ≤
      2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  refine badA_prob_gen hn ?_
  have := goodHat_prob hn
  rw [measureReal_compl (goodHat_meas hn1), probReal_univ]
  linarith

/-- `pertA n = (27501/10⁸)/n`. -/
lemma pertA_eq {n : ℕ} (hn : 1 ≤ n) : pertA n = 27501 / 100000000 * (1 / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pertA
  rw [qA_cast]
  field_simp
  ring

/-- `68·10⁶/(qA n)² ≤ (1/5000)/n` for `n ≥ 4096`. -/
lemma qTerm_le {n : ℕ} (hn : 4096 ≤ n) :
    68000000 / (qA n : ℝ) ^ 2 ≤ 1 / 5000 * (1 / (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  rw [qA_cast]
  have e : 68000000 / (10000 * (n : ℝ)) ^ 2 = 68 / 100 * (1 / (n : ℝ)) * (1 / (n : ℝ)) := by
    field_simp
    ring
  rw [e]
  have h1 : 1 / (n : ℝ) ≤ 1 / 4096 := one_div_le_one_div_of_le (by norm_num) hx
  have h0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  nlinarith

section formula

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- **The headline in formula form**, with the probability `p₁` of the bad hidden event as a
hypothesis. For `0 < θ < 1`, `0 < ζ < 1`, `η > 0`, `η′ > 0`, `Q = κ^{∘6}(0)`:
`Pr(|g̃ − B| ≤ sd/2) ≥ 1 − (p₁ + 4·((1 + η′)·((1 + η)(1.83/n) + 4(1 + 1/η)·EHH n ζ) +
  (1 + 1/η′)·pertA n)/(θ(1 − Q)) + vSpread n/((1 − θ)(1 − Q))²)`. -/
theorem arithSucceeds141_core {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {p₁ : ℝ}
    (h1 : (mlpTriple 2 n).real {t | t.1 ∉ goodWA n} ≤ p₁) :
    1 - (p₁ +
        4 * ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) +
          (1 + 1 / η') * pertA n) / (θ * (1 - kappa^[6] 0)) +
        vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2) ≤
      (mlpTriple 2 n).real (okA n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set S : ℝ := 4 / (n : ℝ) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set s : ℝ := θ * (S * (1 - kappa^[6] 0)) / 4 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have h2 : (mlpTriple 2 n).real
      {t | t ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
          t.1 ∈ goodWA n} ∧
        s ≤ (gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2} ≤
      ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) +
        (1 + 1 / η') * pertA n) * (4 / (n : ℝ)) / s := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (errTailA hn hζ0 hζ1 hη hη' hs0)
    rintro t ⟨hg, he⟩
    change s ≤ errGA n t
    unfold errGA
    rw [Set.indicator_of_mem (show t.1 ∈ goodWA n from hg)]
    exact he
  have h3 : (mlpTriple 2 n).real
      {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        sdn t.1 t.2.1 t.2.2 ^ 2 < 4 * s} ≤
      vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 := by
    have e : 4 * s = θ * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by rw [hs, hS]; ring
    rw [e]
    exact spreadLow139 hn hθ1
  have h := ok_of_three (mlpTriple 2 n)
    (G := {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∈ goodWA n})
    (d := fun t => gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2)
    (sd := fun t => sdn t.1 t.2.1 t.2.2) (fun t => sdn_nonneg' _ _ _) h1 h2 h3
  have e : ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) +
        (1 + 1 / η') * pertA n) * (4 / (n : ℝ)) / s =
      4 * ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) +
        (1 + 1 / η') * pertA n) / (θ * (1 - kappa^[6] 0)) := by
    rw [hs, hS]
    field_simp
  rw [e] at h
  exact h

/-- **The headline in formula form.** -/
theorem arithSucceeds141_formula {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    1 - (2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 +
        4 * ((1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) +
          (1 + 1 / η') * pertA n) / (θ * (1 - kappa^[6] 0)) +
        vSpread n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2) ≤
      (mlpTriple 2 n).real (okA n) :=
  arithSucceeds141_core hn hθ0 hθ1 hζ0 hζ1 hη hη' (badA_prob hn)

/-- The Markov term at `θ = 1/10`, `ζ = η = 1/20`, `η′ = 1/100`: at most `368.1/n`. -/
lemma markovA_le :
    4 * ((1 + 1 / 100) * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) +
        (1 + 1 / (1 / 100)) * pertA n) / (1 / 10 * (1 - kappa^[6] 0)) ≤
      3681 / 10 * (1 / (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hEH' := EHH_scale hn
  have hEH0 := EHH_nonneg hn (1 / 20)
  have hp := pertA_eq (n := n) (by omega)
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * t := by rw [ht]; ring
  rw [e183, hp, div_le_iff₀ (by nlinarith)]
  nlinarith

/-- The Chebyshev term at `θ = 1/10`: at most `1592.4/n`. -/
lemma chebA_le :
    vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤ 15924 / 10 * (1 / (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hv := vSpread_scale hn
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have e64 : 64 / (n : ℝ) = 64 * t := by rw [ht]; ring
  rw [e64] at hv
  have hden : ((1 - 1 / 10) * (222757 / 1000000 : ℝ)) ^ 2 ≤
      ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by nlinarith) 2
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

/-- **`arithSucceeds141`** (item 3, the headline). For every `n ≥ 4096`, with `(W, A, F)` three
independent random ReLU networks of the widths of the Focus (`r = 2`), `B = Bn W A F` the
target, `sd = sdn W A F` the realized spread, and `g̃ = gA W A F` the exact mean of `F∘A` over
the distribution of `sphPt(M₃ b̃ + τ̃₀γ)` (arithmetic centre `b̃`: a finite ReLU sum with rational
atoms, rational weights and the rational constant `cA n`; arithmetic scalar
`τ̃₀² = t|b̃|²·max(0, t|b̃|²·c̃₁ − 1)` with the rational constant `c̃₁ = c1A n`):
`Pr_{W,A,F}(|g̃ − B| ≤ sd/2) ≥ 1 − (0.002 + 2031/n)`. -/
theorem arithSucceeds141 :
    1 - (2 / 1000 + 2031 / (n : ℝ)) ≤ (mlpTriple 2 n).real (okA n) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := arithSucceeds141_formula hn (θ := 1 / 10) (by norm_num) (by norm_num)
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20) (by norm_num)
    (η' := 1 / 100) (by norm_num)
  have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
  have e105 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
  rw [e84, e105] at h
  have t1 := markovA_le hn
  have t2 := chebA_le hn
  have t3 := qTerm_le hn
  have e70 : 70 / (n : ℝ) = 70 * (1 / (n : ℝ)) := by ring
  have e2031 : 2031 / (n : ℝ) = 2031 * (1 / (n : ℝ)) := by ring
  have ht0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  rw [e2031]
  rw [e70] at h
  linarith

/-- For every `n ≥ 4096`: `Pr(|g̃ − B| ≤ sd/2) ≥ 1/2`. -/
theorem arithSucceeds141_all : 1 / 2 ≤ (mlpTriple 2 n).real (okA n) := by
  have h := arithSucceeds141 hn
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have : 2031 / (n : ℝ) ≤ 2031 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

/-- In the frontier interval: for `n ≥ 16384`, `Pr(|g̃ − B| ≤ sd/2) ≥ 87/100`. -/
theorem arithSucceeds141_frontier (h16 : 16384 ≤ n) :
    87 / 100 ≤ (mlpTriple 2 n).real (okA n) := by
  have h := arithSucceeds141 hn
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast h16
  have : 2031 / (n : ℝ) ≤ 2031 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

/-- **Level `99/100`.** For `n ≥ 253875`: `Pr(|g̃ − B| ≤ sd/2) ≥ 99/100`. -/
theorem arithSucceeds141_99 (hbig : 253875 ≤ n) :
    99 / 100 ≤ (mlpTriple 2 n).real (okA n) := by
  have h := arithSucceeds141 hn
  have hx : (253875 : ℝ) ≤ n := by exact_mod_cast hbig
  have : 2031 / (n : ℝ) ≤ 2031 / 253875 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

/-- The explicit scale, with the probability `p₁` of the bad hidden event as a hypothesis:
`Pr(|g̃ − B| ≤ ε·scale139 n) ≥ 1 − (p₁ + 9.3/(ε²n))`. -/
theorem arithExplicit141_core {ε : ℝ} (hε : 0 < ε) {p₁ : ℝ}
    (h1 : (mlpTriple 2 n).real {t | t.1 ∉ goodWA n} ≤ p₁) :
    1 - (p₁ + 93 / 10 / (ε ^ 2 * (n : ℝ))) ≤
      (mlpTriple 2 n).real
        {t | |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set S : ℝ := 4 / (n : ℝ) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set s : ℝ := ε ^ 2 * (S * (1 - kappa^[6] 0)) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hT := errTailA hn (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
    (by norm_num) (η' := 1 / 100) (by norm_num) hs0
  have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
  have e105 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
  rw [e84, e105] at hT
  have h2 : (mlpTriple 2 n).real
      {t | t ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
          t.1 ∈ goodWA n} ∧
        s ≤ (gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2} ≤
      ((1 + 1 / 100) * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) +
        (1 + 1 / (1 / 100)) * pertA n) * (4 / (n : ℝ)) / s := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hT
    rintro t ⟨hg, he⟩
    change s ≤ errGA n t
    unfold errGA
    rw [Set.indicator_of_mem (show t.1 ∈ goodWA n from hg)]
    exact he
  have h := ok_of_two (mlpTriple 2 n)
    (G := {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∈ goodWA n})
    (d := fun t => gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) h1 h2
  rw [eps_scale hε.le]
  refine le_trans ?_ h
  have hEH' := EHH_scale hn
  have hEH0 := EHH_nonneg hn (1 / 20)
  have hp := pertA_eq (n := n) (by omega)
  have ht0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hterm : ((1 + 1 / 100) * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) +
        (1 + 1 / (1 / 100)) * pertA n) * (4 / (n : ℝ)) / s ≤ 93 / 10 / (ε ^ 2 * (n : ℝ)) := by
    have e : ((1 + 1 / 100) * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) +
        (1 + 1 / (1 / 100)) * pertA n) * (4 / (n : ℝ)) / s =
        ((1 + 1 / 100) * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) +
          (1 + 1 / (1 / 100)) * pertA n) / (ε ^ 2 * (1 - kappa^[6] 0)) := by
      rw [hs, hS]
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * (1 / (n : ℝ)) := by ring
    rw [e183, hp]
    have hnum : (1 + 1 / 100) * (21 / 20 * (183 / 100 * (1 / (n : ℝ))) + 84 * EHH n (1 / 20)) +
        (1 + 1 / (1 / 100)) * (27501 / 100000000 * (1 / (n : ℝ))) ≤
        2050 / 1000 * (1 / (n : ℝ)) := by nlinarith
    have hε2 : 0 < ε ^ 2 := by positivity
    have h5 := mul_le_mul_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ ε ^ 2 * (n : ℝ))
    have e5 : 2050 / 1000 * (1 / (n : ℝ)) * (ε ^ 2 * (n : ℝ)) = 2050 / 1000 * ε ^ 2 := by
      field_simp
    rw [e5] at h5
    have h6 : 2050 / 1000 * ε ^ 2 ≤ 93 / 10 * (ε ^ 2 * (1 - kappa^[6] 0)) := by nlinarith
    linarith
  linarith

/-- **The explicit scale.** For every `n ≥ 4096` and `ε > 0`:
`Pr(|g̃ − B| ≤ ε·scale139 n) ≥ 1 − (0.002 + 70/n + 68·10⁶/(qA n)² + 9.3/(ε²n))`. -/
theorem arithExplicit141 {ε : ℝ} (hε : 0 < ε) :
    1 - (2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + 93 / 10 / (ε ^ 2 * (n : ℝ))) ≤
      (mlpTriple 2 n).real
        {t | |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} :=
  arithExplicit141_core hn hε (badA_prob hn)

/-- **The explicit scale, with the true rate of the bad hidden event**, `ρ = n²/m_W`. -/
theorem arithExplicit141_sharp {ε : ℝ} (hε : 0 < ε) :
    1 - (2 / 1000 + 3635 * ((n : ℝ) ^ 2 / (mW n : ℝ)) +
        3212000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 +
        93 / 10 / (ε ^ 2 * (n : ℝ))) ≤
      (mlpTriple 2 n).real
        {t | |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} :=
  arithExplicit141_core hn hε (badA_prob_gen hn (goodHat_prob_sharp hn))

end formula

/-- **Level `99/100` at the explicit scale, inside the frontier interval.** For every
`n ≥ 10000`: `Pr_{W,A,F}(|g̃ − B| ≤ (1/2)·scale139 n) ≥ 99/100`, with
`scale139 n = √((4/n)(1 − κ^{∘6}(0)))` (NOT the realized spread `sd`). -/
theorem arithExplicit141_99 {n : ℕ} (hn : 10000 ≤ n) :
    99 / 100 ≤ (mlpTriple 2 n).real
      {t | |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ 1 / 2 * scale139 n} := by
  have hx : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := arithExplicit141_sharp (n := n) (by omega) (ε := 1 / 2) (by norm_num)
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
  have t3 : 93 / 10 / ((1 / 2 : ℝ) ^ 2 * (n : ℝ)) ≤ 3720 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have t4 := qTerm_le (n := n) (by omega)
  have t5 : 1 / 5000 * (1 / (n : ℝ)) ≤ 1 / 1000000 := by
    have : 1 / (n : ℝ) ≤ 1 / 10000 := one_div_le_one_div_of_le (by norm_num) hx
    linarith
  linarith

/-! ## Two stages: the order of Option A -/

lemma measurableSet_okA {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (okA n) := by
  have hN : 1 ≤ 2 * n := by omega
  exact measurableSet_le ((measurable_gA.sub (BstLean.Part131.measurable_Bn hN)).abs)
    ((BstLean.Part131.measurable_sdn hN).div_const 2)

/-- **Option A form, relative to the realized spread.** For `n ≥ 4096` and `q > 0`:
`Pr_{W,F}(Pr_A(|g̃ − B| ≤ sd/2) > 1 − q) ≥ 1 − (0.002 + 2031/n)/q`. -/
theorem optA141 {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq : 0 < q) :
    1 - (2 / 1000 + 2031 / (n : ℝ)) / q ≤ (BstLean.Part131.lawWF (2 * n) (mW n) n (mF n)).real
      {x | 1 - q < (mlpGauss n (mA n) n).real
        {A | |gA x.1 A x.2 - Bn x.1 A x.2| ≤ sdn x.1 A x.2 / 2}} :=
  twoStage139 (measurableSet_okA (by omega)) hq (arithSucceeds141 hn)

/-- **Option A form, relative to the explicit scale.** For `n ≥ 4096`, `ε > 0`, `q > 0`. -/
theorem optA141_explicit {n : ℕ} (hn : 4096 ≤ n) {ε : ℝ} (hε : 0 < ε) {q : ℝ} (hq : 0 < q) :
    1 - (2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 +
        93 / 10 / (ε ^ 2 * (n : ℝ))) / q ≤
      (BstLean.Part131.lawWF (2 * n) (mW n) n (mF n)).real
        {x | 1 - q < (mlpGauss n (mA n) n).real
          {A | |gA x.1 A x.2 - Bn x.1 A x.2| ≤ ε * scale139 n}} := by
  have hN : 1 ≤ 2 * n := by omega
  have hE : MeasurableSet {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 | |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} :=
    measurableSet_le ((measurable_gA.sub (BstLean.Part131.measurable_Bn hN)).abs)
      measurable_const
  exact twoStage139 hE hq (arithExplicit141 hn hε)

end BstLean.Part141

open BstLean.Part141 in
#print axioms arithSucceeds141_formula
open BstLean.Part141 in
#print axioms arithSucceeds141
open BstLean.Part141 in
#print axioms arithSucceeds141_all
open BstLean.Part141 in
#print axioms arithSucceeds141_frontier
open BstLean.Part141 in
#print axioms arithSucceeds141_99
open BstLean.Part141 in
#print axioms arithExplicit141
open BstLean.Part141 in
#print axioms arithExplicit141_sharp
open BstLean.Part141 in
#print axioms arithExplicit141_99
open BstLean.Part141 in
#print axioms optA141
open BstLean.Part141 in
#print axioms optA141_explicit
