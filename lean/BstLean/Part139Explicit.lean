import BstLean.Part139Sample

/-!
# Part 139: the cheap estimate against the explicit scale `√(S·(1 − Q))`

Role: `delegations/statements/p139-spec.md`, "a statement … with `sd` replaced by the explicit
scale `√(S·y)` (`S = 4/n`) is also a result". Here `y = 1 − Q`, `Q = κ^{∘6}(0)`; by `spread_L2`
the squared realized spread `sd²` is within `S·√(v_n)` of `S·(1 − Q)` in `L²`.

These statements need no lower bound of the realized spread, so they have no Chebyshev term.

* `scale139 n = √((4/n)·(1 − Q))`: the explicit scale.
* **`standInExplicit139`**: for `n ≥ 4096`, `ε > 0`:
  `Pr(|g₀ − B| ≤ ε·scale) ≥ 1 − (0.002 + 9/(ε²·n))`.
* **`standInExplicit139_half`**: `≥ 99/100` at `ε = 1/2` for every `n ≥ 4500`.
* **`standInExplicit139_rate`**: `≥ 99/100` at `ε = 34/√n` for every `n ≥ 4096`.
* **`sampleExplicit139`**: the mean of `k` points of the cheap stand-in:
  `Pr(|ĝ_k − B| ≤ ε·scale) ≥ 1 − (0.002 + 9/(ε²·n) + 4.5/(ε²·k))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136 BstLean.Part138

/-- **The explicit scale of the spread**: `√(S·(1 − Q))`, `S = 4/n`, `Q = κ^{∘6}(0)`. -/
noncomputable def scale139 (n : ℕ) : ℝ := √(4 / (n : ℝ) * (1 - kappa^[6] 0))

/-- The assembly of two events: if the good event fails with probability at most `p₁` and the
squared error is at least `s` on the good event with probability at most `p₂`, then
`|d| ≤ √s` with probability at least `1 − (p₁ + p₂)`. -/
lemma ok_of_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Set Ω} {d : Ω → ℝ} {s p₁ p₂ : ℝ}
    (h1 : μ.real Gᶜ ≤ p₁) (h2 : μ.real {ω | ω ∈ G ∧ s ≤ d ω ^ 2} ≤ p₂) :
    1 - (p₁ + p₂) ≤ μ.real {ω | |d ω| ≤ √s} := by
  set OK : Set Ω := {ω | |d ω| ≤ √s} with hOK
  have hcov : OKᶜ ⊆ Gᶜ ∪ {ω | ω ∈ G ∧ s ≤ d ω ^ 2} := by
    intro ω hω
    by_cases hg : ω ∈ G
    swap
    · exact Or.inl hg
    by_cases he' : s ≤ d ω ^ 2
    · exact Or.inr ⟨hg, he'⟩
    have he := not_le.mp he'
    exfalso
    apply hω
    change |d ω| ≤ √s
    exact Real.abs_le_sqrt he.le
  have hle : μ.real OKᶜ ≤ p₁ + p₂ := by
    calc μ.real OKᶜ ≤ μ.real (Gᶜ ∪ {ω | ω ∈ G ∧ s ≤ d ω ^ 2}) :=
          measureReal_mono hcov (measure_ne_top _ _)
      _ ≤ μ.real Gᶜ + μ.real {ω | ω ∈ G ∧ s ≤ d ω ^ 2} := measureReal_union_le _ _
      _ ≤ _ := add_le_add h1 h2
  have hcompl : μ.real OK + μ.real OKᶜ ≥ 1 := by
    have a1 := measureReal_union_le (μ := μ) OK OKᶜ
    rw [Set.union_compl_self, probReal_univ] at a1
    exact a1
  linarith

/-- `ε·scale = √(ε²·S·(1 − Q))` for `ε ≥ 0`. -/
lemma eps_scale {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    ε * scale139 n = √(ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0))) := by
  unfold scale139
  rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]

/-- The arithmetic of the error term: `(2·(0.99/n) + 8·EH + c)·S/(ε²·S·y) ≤ 9/(ε²n) + 4.5c/ε²`. -/
lemma explicit_arith {n : ℕ} (hn : 4096 ≤ n) {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 ≤ c) :
    (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20) + c) * (4 / (n : ℝ)) /
        (ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0))) ≤
      9 / (ε ^ 2 * (n : ℝ)) + 9 / 2 * c / ε ^ 2 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have hEH := EH_le hn
  have hEH0 := (EH_pos hn (by norm_num : (0 : ℝ) < 1 / 20)).le
  have hnm := n_div_mW_scale hn
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hEH' : EH n (1 / 20) ≤ 470 / 262144 * t := by
    have e : 470 * (n : ℝ) / (mW n : ℝ) = 470 * ((n : ℝ) / (mW n : ℝ)) := by ring
    rw [e] at hEH
    have e2 : (1 : ℝ) / 262144 / (n : ℝ) = 1 / 262144 * t := by rw [ht]; ring
    rw [e2] at hnm
    linarith
  have e99 : 99 / 100 / (n : ℝ) = 99 / 100 * t := by rw [ht]; ring
  have e1 : (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20) + c) * (4 / (n : ℝ)) /
        (ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0))) =
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20) + c) / (1 - kappa^[6] 0) / ε ^ 2 := by
    field_simp
  have e2 : 9 / (ε ^ 2 * (n : ℝ)) + 9 / 2 * c / ε ^ 2 = (9 * t + 9 / 2 * c) / ε ^ 2 := by
    rw [ht]; field_simp
  rw [e1, e2]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [div_le_iff₀ hy0, e99]
  nlinarith

/-- **The cheap estimate against the explicit scale.** For every `n ≥ 4096` and `ε > 0`:
`Pr_{W,A,F}(|g₀ − B| ≤ ε·√(S(1 − Q))) ≥ 1 − (0.002 + 9/(ε²·n))`. -/
theorem standInExplicit139 {n : ℕ} (hn : 4096 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    1 - (2 / 1000 + 9 / (ε ^ 2 * (n : ℝ))) ≤
      (mlpTriple 2 n).real
        {t | |gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have hs0 : (0 : ℝ) < ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by positivity
  have h1 : (mlpTriple 2 n).real
      {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∈ goodW n}ᶜ ≤ 2 / 1000 := bad_prob hn
  have h2 : (mlpTriple 2 n).real
      {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
          t.1 ∈ goodW n} ∧
        ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) ≤
          (gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) ^ 2} ≤
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20)) * (4 / (n : ℝ)) /
        (ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0))) := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (errTail139 hn (ζ := 1 / 20) (by norm_num) (by norm_num) hs0)
    rintro t ⟨hg, he⟩
    change _ ≤ errG n t
    unfold errG
    rw [Set.indicator_of_mem (show t.1 ∈ goodW n from hg)]
    exact he
  have h := ok_of_two (mlpTriple 2 n)
    (d := fun t => gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2) h1 h2
  rw [eps_scale hε.le]
  have ha := explicit_arith hn hε (c := 0) le_rfl
  simp only [add_zero, mul_zero, zero_div] at ha
  exact le_trans (by linarith) h

/-- **Tolerance `1/2` of the explicit scale, level `99/100`, in the frontier interval.** For
every `n ≥ 4500`: `Pr_{W,A,F}(|g₀ − B| ≤ (1/2)·√(S(1 − Q))) ≥ 99/100`. -/
theorem standInExplicit139_half {n : ℕ} (hn : 4500 ≤ n) :
    99 / 100 ≤ (mlpTriple 2 n).real
      {t | |gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ 1 / 2 * scale139 n} := by
  have h := standInExplicit139 (n := n) (by omega) (ε := 1 / 2) (by norm_num)
  have hx : (4500 : ℝ) ≤ n := by exact_mod_cast hn
  have : 9 / ((1 / 2 : ℝ) ^ 2 * (n : ℝ)) ≤ 8 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Tolerance `34/√n` of the explicit scale, level `99/100`, every `n ≥ 4096`.**
`Pr_{W,A,F}(|g₀ − B| ≤ (34/√n)·√(S(1 − Q))) ≥ 99/100`. -/
theorem standInExplicit139_rate {n : ℕ} (hn : 4096 ≤ n) :
    99 / 100 ≤ (mlpTriple 2 n).real
      {t | |gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ 34 / √(n : ℝ) * scale139 n} := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have h := standInExplicit139 hn (ε := 34 / √(n : ℝ)) (by positivity)
  have e : (34 / √(n : ℝ)) ^ 2 * (n : ℝ) = 1156 := by
    rw [div_pow, Real.sq_sqrt hx0.le]
    field_simp
    norm_num
  rw [e] at h
  norm_num at h ⊢
  linarith

/-- **The sample estimate against the explicit scale.** For `n ≥ 4096`, `k ≥ 1`, `ε > 0`:
`Pr(|ĝ_k − B| ≤ ε·√(S(1 − Q))) ≥ 1 − (0.002 + 9/(ε²·n) + 4.5/(ε²·k))`, the probability over
`(W, A, F)` and the `k` Gaussian vectors. -/
theorem sampleExplicit139 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    1 - (2 / 1000 + 9 / (ε ^ 2 * (n : ℝ)) + 9 / 2 / (ε ^ 2 * (k : ℝ))) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |gSample k p.1.1 p.1.2.1 p.1.2.2 p.2 - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          ε * scale139 n} := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have hs0 : (0 : ℝ) < ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by positivity
  have h1 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodW n}ᶜ ≤ 2 / 1000 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodW n}).trans_le (bad_prob hn)
  have h2 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodW n} ∧
        ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) ≤
          (gSample k p.1.1 p.1.2.1 p.1.2.2 p.2 - Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (ε ^ 2 * (4 / (n : ℝ) * (1 - kappa^[6] 0))) := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (errSampleTail139 hn (ζ := 1 / 20) (by norm_num) (by norm_num) hk hs0)
    rintro p ⟨hg, he⟩
    change _ ≤ errS k n p
    unfold errS
    rw [Set.indicator_of_mem (show p.1.1 ∈ goodW n from hg)]
    exact he
  have h := ok_of_two ((mlpTriple 2 n).prod (gamK k n))
    (d := fun p => gSample k p.1.1 p.1.2.1 p.1.2.2 p.2 - Bn p.1.1 p.1.2.1 p.1.2.2) h1 h2
  rw [eps_scale hε.le]
  have ha := explicit_arith hn hε (c := (k : ℝ)⁻¹) (by positivity)
  have e : 9 / 2 * (k : ℝ)⁻¹ / ε ^ 2 = 9 / 2 / (ε ^ 2 * (k : ℝ)) := by
    field_simp
  rw [e] at ha
  exact le_trans (by linarith) h

end BstLean.Part139

open BstLean.Part139 in
#print axioms standInExplicit139
open BstLean.Part139 in
#print axioms standInExplicit139_half
open BstLean.Part139 in
#print axioms standInExplicit139_rate
open BstLean.Part139 in
#print axioms sampleExplicit139
