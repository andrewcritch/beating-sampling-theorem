import BstLean.Part151Weak

/-!
# Part 151, item 3 (second half): the hypotheses H1 and H3 from existing Lean theorems, and the
conditional program theorem with H2 as the only hypothesis

Role: `delegations/statements/p151-spec.md`, item 3 ("say which existing Lean theorems already
give H1 and H3 at which constants"). Here they are proved as instances of the `Prop`s `H1`, `H3`
of `Part151Cond`, for every `n ≥ 4096`. `q₀ = 0.222757` (a lower bound of `1 − κ^{∘6}(0)`),
`c₀ = (4/n)·q₀`, `e₀ = 0.78728`, `w₀ = 4849/20000`.

* `spreadLean151`, **`H3_lean`**: `Pr(sd² < θ·c₀) ≤ 2e₀²/((1 − θ)q₀)²/n` (Chebyshev's inequality
  with the second moment `spread_L2_dist2` of Part 143 and the constants of Part 145).
* `wBad151`: `Pr(W not in the good hidden event of Part 145) ≤ 1/n`.
* `wStageLean151`: `Pr(W good, sd² ≥ θc₀, |B′ − B| > ε_W·sd) ≤ w₀/(ε_W²·θ·q₀)/n` (Chebyshev's
  inequality with `errVecAF_lint` of Part 145).
* **`H1_lean`**: `H1 n ε_W (1/n + 2e₀²/((1 − θ)q₀)²/n + w₀/(ε_W²θq₀)/n)`.
* `finalStepR`: the union bound of `Part151Gauss` with the first term restricted to the event
  `E` and to `sd ≥ d`.
* **`condLean151`**: for every `n ≥ 4096`: if `H2` holds for an event `E` with the constant
  `c_V` and the charge `p₂`, then
  `Pr(|g − B| ≤ sd/2) ≥ 1 − (1/n + w₀/(ε_W²θq₀)/n + p₂ + 2e₀²/((1 − θ)q₀)²/n
  + 2Φ̄((1/2 − ε_W)·√(n·θ·q₀/c_V)))`. The ONLY hypothesis that is not a Lean theorem is `H2`.
* `condLeanProg151`: the same for the straight-line program `fullProg150 k n J`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143 BstLean.Part145
open BstLean.Part149 BstLean.Part150

variable {k n : ℕ}

/-! ## H3: the lower tail of the spread -/

/-- **The lower tail of the spread in Lean, every `n ≥ 4096`**:
`Pr(sd² < θ·(4/n)·0.222757) ≤ 2·0.78728²/((1 − θ)·0.222757)²/n`. -/
theorem spreadLean151 (hn : 4096 ≤ n) {θ : ℝ} (hθ1 : θ < 1) :
    (mlpTriple 2 n).real {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (222757 / 1000000))} ≤
      2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have h1θ : 0 < 1 - θ := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hcc : c₀ ≤ c := by
    rw [hc, hc₀]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have he0 := eDBq_nonneg (biasK (mF n)) (tau143sC n) (pWC n) n
  have heR := eD145_R hn
  set e : ℝ := eDBq (biasK (mF n)) (tau143sC n) (pWC n) n with hed
  have msd3 : Measurable (fun t : Trip n => sdn t.1 t.2.1 t.2.2) :=
    measurable_sdn (mA := mA n) (mF := mF n) hN
  have mFs : Measurable (fun t : Trip n =>
      ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((msd3.pow_const 2).sub measurable_const).pow_const 2)
  have hV : ∫⁻ t, ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    have mπ : Measurable (fun r : Rest (2 * n) (mW n) n (mA n) (mF n) =>
        (r.1, r.2.1, r.2.2.2)) := by fun_prop
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
        ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
    rw [e0, ← lawR_drop, lintegral_map mFs mπ]
    exact spread_L2_dist2 hn1 hN hmF (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ) * e) (kernR hn)
  have hε : 0 < ((1 - θ) * c₀) ^ 2 := by positivity
  have hm := markov_real (mlpTriple 2 n) mFs hε
    (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) hV
  have hsub : {t : Trip n | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c₀} ⊆
      {t : Trip n | ENNReal.ofReal (((1 - θ) * c₀) ^ 2) <
        ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2)} := by
    intro t ht
    simp only [mem_ofPred_eq] at ht ⊢
    have h3 : (1 - θ) * c₀ < c - sdn t.1 t.2.1 t.2.2 ^ 2 := by linarith
    have h5 : 0 < (1 - θ) * c₀ := by positivity
    have h6 := pow_lt_pow_left₀ h3 h5.le (n := 2) (by norm_num)
    have e6 : (sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2 = (c - sdn t.1 t.2.1 t.2.2 ^ 2) ^ 2 := by ring
    rw [e6]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans hε h6)).mpr h6
  refine (measureReal_mono hsub).trans (hm.trans ?_)
  have he2 : (4 / (n : ℝ) * e) ^ 2 ≤ (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left heR (by positivity)) 2
  refine (div_le_div_of_nonneg_right (by linarith :
    2 * (4 / (n : ℝ) * e) ^ 2 ≤ 2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2)
    hε.le).trans (le_of_eq ?_)
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hx0.le
  rw [hc₀]
  field_simp
  rw [hsq]

/-- **H3 in Lean**, every `n ≥ 4096`, every `θ < 1`: `d₀ = θ·0.222757`,
`p₃ = 2·0.78728²/((1 − θ)·0.222757)²/n` (about `24.98/((1 − θ)²·n)`). -/
theorem H3_lean (hn : 4096 ≤ n) {θ : ℝ} (hθ1 : θ < 1) :
    H3 n univ (θ * (222757 / 1000000))
      (2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n) := by
  unfold H3
  have h := spreadLean151 hn hθ1
  have e : (univ : Set (Trip n)) ∩ {t | sdn t.1 t.2.1 t.2.2 ^ 2 <
      θ * (222757 / 1000000) * (4 / (n : ℝ))} =
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (222757 / 1000000))} := by
    ext t
    simp only [univ_inter, mem_ofPred_eq]
    rw [show θ * (222757 / 1000000) * (4 / (n : ℝ)) = θ * (4 / (n : ℝ) * (222757 / 1000000)) by
      ring]
  rw [e]
  exact h

/-! ## H1: the population bound of the `W` stage -/

/-- The good hidden event of `W` of Part 145 fails with probability at most `1/n`. -/
theorem wBad151 (hn : 4096 ≤ n) :
    (mlpTriple 2 n).real {t | t.1 ∉ goodWAG (Gwin n)} ≤ 1 / (n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hG1 : (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ 1 / 50000 / (n : ℝ) := by
    have h := Gwin_compl_n hn
    unfold cW at h
    have e : (15640 : ℝ) / 1073741824 / (n : ℝ) ≤ 1 / 50000 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    linarith
  have hbadW := badAG0_prob_gen hn hG hG1
  have hq : (1 : ℝ) / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
    rw [qA_cast]
    have e1 : (68000000 : ℝ) / (10000 * (n : ℝ)) ^ 2 = 68 / 100 / (n : ℝ) ^ 2 := by
      field_simp; ring
    have e2 : (68 : ℝ) / 100 / (n : ℝ) ^ 2 ≤ 1 / 2 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hx0]
      nlinarith
    have e3 : (1 : ℝ) / 50000 / (n : ℝ) ≤ 1 / 2 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    rw [e1]
    have e4 : (1 : ℝ) / 2 / (n : ℝ) + 1 / 2 / (n : ℝ) = 1 / (n : ℝ) := by ring
    linarith
  linarith

/-- **The error of the `W` stage in Lean, every `n ≥ 4096`** (`B′ = gA`: the population mean
over the stand-in input of the arithmetic `W` stage of Part 141):
`Pr(W good, sd ≥ d, |B′ − B| > ε_W·sd) ≤ (4849/20000)·(1/n)·(4/n)/(ε_W·d)²`. -/
theorem wStageLean151 (hn : 4096 ≤ n) {εW d : ℝ} (hεW : 0 < εW) (hd : 0 < d) :
    (mlpTriple 2 n).real {t | t.1 ∈ goodWAG (Gwin n) ∧ d ≤ sdn t.1 t.2.1 t.2.2 ∧
        εW * sdn t.1 t.2.1 t.2.2 < |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2|} ≤
      4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) / (εW * d) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  obtain ⟨hΛi, hΛ⟩ := LamVR hn
  have hW := errVecAF_lint (goodEvFR hn) hn (by unfold Lam145R; norm_num) hΛi hΛ
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 7) (by norm_num) (η' := 1 / 29)
    (by norm_num)
  have hXA := XA145_R hn
  have hW' : ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) :=
    hW.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hXA (by positivity)))
  have hε : 0 < (εW * d) ^ 2 := by positivity
  have mf : Measurable (fun t : Trip n => ENNReal.ofReal (errGAG (Gwin n) t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGAG0 hG hn1)
  have hm := markov_real (mlpTriple 2 n) mf hε
    (by positivity : (0 : ℝ) ≤ 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) hW'
  refine (measureReal_mono ?_).trans hm
  rintro t ⟨hWg, hp2, hp3⟩
  simp only [mem_ofPred_eq]
  have e : errGAG (Gwin n) t = (gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2 := by
    unfold errGAG
    rw [indicator_of_mem hWg]
  rw [e]
  have h1 : εW * d ≤ εW * sdn t.1 t.2.1 t.2.2 := mul_le_mul_of_nonneg_left hp2 hεW.le
  have h2 : εW * d < |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| := lt_of_le_of_lt h1 hp3
  have h3 : (εW * d) ^ 2 < (gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2 := by
    rw [← sq_abs (gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2)]
    exact pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans hε h3)).mpr h3

/-- **H1 in Lean**, every `n ≥ 4096`, `ε_W > 0`, `0 < θ < 1`:
`Pr(|B′ − B| > ε_W·sd) ≤ 1/n + 2·0.78728²/((1 − θ)·0.222757)²/n
+ (4849/20000)/(ε_W²·θ·0.222757)/n`. -/
theorem H1_lean (hn : 4096 ≤ n) {εW θ : ℝ} (hεW : 0 < εW) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    H1 n εW (1 / (n : ℝ) + 2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
      4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n) := by
  unfold H1
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  set d : ℝ := √(θ * c₀) with hd
  have hd0 : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = θ * c₀ := Real.sq_sqrt (by positivity)
  have h1 := wBad151 hn
  have h2 := spreadLean151 hn hθ1
  have h3 := wStageLean151 hn hεW hd0
  have hsub : {t : Trip n | εW * sdn t.1 t.2.1 t.2.2 <
      |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2|} ⊆
      ({t | t.1 ∉ goodWAG (Gwin n)} ∪ {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c₀}) ∪
        {t | t.1 ∈ goodWAG (Gwin n) ∧ d ≤ sdn t.1 t.2.1 t.2.2 ∧
          εW * sdn t.1 t.2.1 t.2.2 < |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2|} := by
    intro t ht
    by_cases hW : t.1 ∈ goodWAG (Gwin n)
    swap
    · exact Or.inl (Or.inl hW)
    by_cases hs : sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c₀
    · exact Or.inl (Or.inr hs)
    refine Or.inr ⟨hW, ?_, ht⟩
    have h0 : 0 ≤ sdn t.1 t.2.1 t.2.2 := Real.sqrt_nonneg _
    rw [hd]
    exact (Real.sqrt_le_left h0).mpr (not_lt.mp hs)
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  have hu := measureReal_union_le (μ := mlpTriple 2 n) {t : Trip n | t.1 ∉ goodWAG (Gwin n)}
    {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c₀}
  have e3 : 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) / (εW * d) ^ 2 =
      4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n := by
    rw [mul_pow, hd2, hc₀]
    field_simp
  rw [e3] at h3
  linarith

/-! ## The union bound, refined -/

section final

variable {T Ω R : Type*} [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace R]

/-- **The final Gaussian step with the union bound, refined**: as `finalStep`, with the first
term restricted to the event `E` and to `sd ≥ d`. -/
theorem finalStepR (Q : Measure T) [IsProbabilityMeasure Q] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure R) [IsProbabilityMeasure ν] {rest : T → Ω}
    {row : T → R} (hrest : Measurable rest) (hrow : Measurable row)
    (hmap : Q.map (fun t => (rest t, row t)) = P.prod ν) {lin : Ω → R → ℝ}
    (hlin : Measurable fun p : Ω × R => lin p.1 p.2) {V : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet E) (hV0 : ∀ ω ∈ E, 0 ≤ V ω)
    (hg : ∀ ω ∈ E, ν.map (lin ω) = gaussianReal 0 (V ω).toNNReal) {v : ℝ} (hv : 0 < v)
    (hVE : ∀ ω ∈ E, V ω ≤ v) (g B B' sd : T → ℝ)
    (hst : ∀ t, rest t ∈ E → g t - B' t = lin (rest t) (row t)) (εW : ℝ) {εA d : ℝ}
    (hεA : 0 < εA) (hd : 0 < d) :
    Q.real {t | (εW + εA) * sd t < |g t - B t|} ≤
      Q.real {t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} + P.real Eᶜ +
        Q.real {t | sd t < d} + 2 * PhiBar (εA * d / √v) := by
  have hpair : Measurable fun t => (rest t, row t) := hrest.prodMk hrow
  have hincl : {t | (εW + εA) * sd t < |g t - B t|} ⊆
      (({t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} ∪ rest ⁻¹' Eᶜ) ∪
        {t | sd t < d}) ∪
        (fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|} := by
    intro t ht
    simp only [mem_ofPred_eq] at ht
    by_cases h2 : rest t ∈ E
    swap
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : sd t < d
    · exact Or.inl (Or.inr h3)
    have h3' : d ≤ sd t := not_lt.mp h3
    by_cases h1 : εW * sd t < |B' t - B t|
    · exact Or.inl (Or.inl (Or.inl ⟨h2, h3', h1⟩))
    refine Or.inr ⟨h2, ?_⟩
    show εA * d < |lin (rest t) (row t)|
    rw [← hst t h2]
    have h1' : |B' t - B t| ≤ εW * sd t := not_lt.mp h1
    have htri : |g t - B t| ≤ |g t - B' t| + |B' t - B t| := by
      have := abs_add_le (g t - B' t) (B' t - B t)
      rwa [sub_add_sub_cancel] at this
    have : εA * d ≤ εA * sd t := mul_le_mul_of_nonneg_left h3' hεA.le
    nlinarith
  have hEc : Q.real (rest ⁻¹' Eᶜ) = P.real Eᶜ := by
    have h1 : P = Q.map rest := by
      have h := congrArg (Measure.map Prod.fst) hmap
      rw [Measure.map_map measurable_fst hpair] at h
      have e : (Prod.fst ∘ fun t => (rest t, row t)) = rest := rfl
      rw [e] at h
      rw [h]; simp
    rw [h1, map_measureReal_apply hrest hE.compl]
  have hS : MeasurableSet {p : Ω × R | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|} :=
    (measurable_fst hE).inter (measurableSet_lt measurable_const hlin.abs)
  have hG4 : Q.real ((fun t => (rest t, row t)) ⁻¹'
      {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) ≤ 2 * PhiBar (εA * d / √v) := by
    rw [← map_measureReal_apply hpair hS, hmap]
    refine (gaussStep P ν hlin hE hV0 hg hv (mul_pos hεA hd) hVE).trans ?_
    have hb0 : 0 ≤ 2 * PhiBar (εA * d / √v) := mul_nonneg (by norm_num) (PhiBar_nonneg _)
    calc 2 * PhiBar (εA * d / √v) * P.real E ≤ 2 * PhiBar (εA * d / √v) * 1 :=
          mul_le_mul_of_nonneg_left measureReal_le_one hb0
      _ = _ := mul_one _
  calc Q.real {t | (εW + εA) * sd t < |g t - B t|}
      ≤ Q.real ((({t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} ∪ rest ⁻¹' Eᶜ) ∪
        {t | sd t < d}) ∪
        (fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) :=
        measureReal_mono hincl
    _ ≤ Q.real {t | rest t ∈ E ∧ d ≤ sd t ∧ εW * sd t < |B' t - B t|} + Q.real (rest ⁻¹' Eᶜ) +
          Q.real {t | sd t < d} +
        Q.real ((fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) := by
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        exact measureReal_union_le _ _
    _ ≤ _ := by rw [hEc]; linarith

end final

/-! ## The conditional program theorem with H2 as the only hypothesis -/

/-- **The conditional program theorem with H2 as the only hypothesis that is not a Lean
theorem.** For every `n ≥ 4096`, every measurable centre map `bh`, every event `E` of the fixed
variables with `H2 n k bh univ E c_V p₂` (`V′ ≤ c_V·S/n` on `E`, `Pr(Eᶜ) ≤ p₂`), every
`0 < ε_W < 1/2`, `0 < θ < 1`, and every estimator `g` equal to `gSampH bh k` on `E`:
`Pr(|g − B| ≤ sd/2) ≥ 1 − (1/n + w₀/(ε_W²θq₀)/n + p₂ + 2e₀²/((1 − θ)q₀)²/n
+ 2Φ̄((1/2 − ε_W)·√(n·θ·q₀/c_V)))`, `q₀ = 0.222757`, `e₀ = 0.78728`, `w₀ = 4849/20000`. -/
theorem condLean151 (hn : 4096 ≤ n) {bh : CMap n} (hbh : Measurable bh) {E : Set (Fix k n)}
    {cV p₂ : ℝ} (h2 : H2 n k bh univ E cV p₂) (hcV : 0 < cV) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) (gE : Joint k n → ℝ)
    (hgE : ∀ p : Joint k n, restJ p ∈ E → gE p = gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n + p₂ +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real {p | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  set d : ℝ := √(θ * c₀) with hd
  have hd0 : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = θ * c₀ := Real.sq_sqrt (by positivity)
  have hv : 0 < cV * (4 / (n : ℝ)) / n := by positivity
  have hεA : 0 < 1 / 2 - εW := by linarith
  have hfin := finalStepR (jointP k n) (fixP k n) (rowP n) measurable_restJ measurable_rowJ
    joint_map (measurable_linJ hbh k) h2.meas (fun ω _ => vHat_nonneg bh k ω)
    (fun ω _ => linJ_gauss bh k ω) hv h2.var gE
    (fun p => Bn p.1.1 p.1.2.1 p.1.2.2) (fun p => gA p.1.1 p.1.2.1 p.1.2.2)
    (fun p => sdn p.1.1 p.1.2.1 p.1.2.2)
    (fun p hp => by rw [hgE p hp]; exact struct151 hn1 bh p) εW hεA hd0
  -- the argument of `Φ̄`
  have harg : (1 / 2 - εW) * d / √(cV * (4 / (n : ℝ)) / n) =
      (1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV) := by
    rw [hd, mul_div_assoc, ← Real.sqrt_div (by positivity)]
    congr 2
    rw [hc₀]
    field_simp
  rw [harg] at hfin
  -- the first term
  have t1 : (jointP k n).real {p : Joint k n | restJ p ∈ E ∧ d ≤ sdn p.1.1 p.1.2.1 p.1.2.2 ∧
      εW * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ≤
      1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n := by
    have h1 := wBad151 hn
    have h3 := wStageLean151 hn hεW0 hd0
    have hsub : {p : Joint k n | restJ p ∈ E ∧ d ≤ sdn p.1.1 p.1.2.1 p.1.2.2 ∧
        εW * sdn p.1.1 p.1.2.1 p.1.2.2 <
          |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ⊆
        {p : Joint k n | p.1 ∈ ({t : Trip n | t.1 ∉ goodWAG (Gwin n)} ∪
          {t | t.1 ∈ goodWAG (Gwin n) ∧ d ≤ sdn t.1 t.2.1 t.2.2 ∧
            εW * sdn t.1 t.2.1 t.2.2 < |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2|})} := by
      rintro p ⟨-, hp2, hp3⟩
      by_cases hW : p.1.1 ∈ goodWAG (Gwin n)
      · exact Or.inr ⟨hW, hp2, hp3⟩
      · exact Or.inl hW
    refine (measureReal_mono hsub).trans ?_
    rw [jointP_fst]
    refine (measureReal_union_le _ _).trans ?_
    have e3 : 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) / (εW * d) ^ 2 =
        4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n := by
      rw [mul_pow, hd2, hc₀]
      field_simp
    rw [e3] at h3
    linarith
  -- the spread
  have t3 : (jointP k n).real {p : Joint k n | sdn p.1.1 p.1.2.1 p.1.2.2 < d} ≤
      2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n := by
    have h := spreadLean151 hn hθ1
    have hsub : {p : Joint k n | sdn p.1.1 p.1.2.1 p.1.2.2 < d} ⊆
        {p : Joint k n | p.1 ∈ {t : Trip n | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c₀}} := by
      intro p hp
      simp only [mem_ofPred_eq] at hp ⊢
      have h0 : 0 ≤ sdn p.1.1 p.1.2.1 p.1.2.2 := Real.sqrt_nonneg _
      rw [← hd2]
      exact pow_lt_pow_left₀ hp h0 (by norm_num)
    refine (measureReal_mono hsub).trans ?_
    rw [jointP_fst]
    exact h
  have hu : (1 : ℝ) ≤ (jointP k n).real {p | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} +
      (jointP k n).real {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|} := by
    have e : {p : Joint k n | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          sdn p.1.1 p.1.2.1 p.1.2.2 / 2} ∪
        {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
          |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|} = univ := by
      ext p
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      rw [show (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 =
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2 by ring]
      exact le_or_gt _ _
    have h1 := measureReal_union_le (μ := jointP k n)
      {p : Joint k n | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2}
      {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|}
    rw [e] at h1
    simpa using h1
  have h2p := h2.prob
  linarith

/-- `condLean151` for the estimator `gSampH bh k`. -/
theorem condLeanSamp151 (hn : 4096 ≤ n) {bh : CMap n} (hbh : Measurable bh) {E : Set (Fix k n)}
    {cV p₂ : ℝ} (h2 : H2 n k bh univ E cV p₂) (hcV : 0 < cV) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n + p₂ +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} :=
  condLean151 hn hbh h2 hcV hεW0 hεW hθ0 hθ1
    (fun p : Joint k n => gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2) fun _ _ => rfl

/-- `condLean151` for the straight-line program `fullProg150 k n J` of Part 150 (centre
`bTW J`), if `τ̃₀ > 0` on `E`. -/
theorem condLeanProg151 (hn : 4096 ≤ n) {J : ℕ} {E : Set (Fix k n)}
    {cV p₂ : ℝ} (h2 : H2 n k (bTW J) univ E cV p₂) (hτ : ∀ ω ∈ E, 0 < tauWA ω.1.1)
    (hcV : 0 < cV) {εW θ : ℝ} (hεW0 : 0 < εW) (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n + p₂ +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hgE : ∀ p : Joint k n, restJ p ∈ E →
      (fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () =
        gSampH (bTW J) k p.1.1 p.1.2.1 p.1.2.2 p.2 := by
    intro p hp
    have hτ' : 0 < tauWA p.1.1 := hτ (restJ p) hp
    exact fullProg150_gSampH (k := k) (J := J) p.1.1 p.1.2.1 p.1.2.2 p.2 hτ'
  exact condLean151 hn (measurable_bTW J) h2 hcV hεW0 hεW hθ0 hθ1
    (fun p : Joint k n => (fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) ()) hgE

end BstLean.Part151
