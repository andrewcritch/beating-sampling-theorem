import BstLean.Part141All

/-!
# Part 142, item 1 (`alloc142`) and the assembly of the headline in formula form

Role: `delegations/statements/p142-spec.md`, items 1 and 4. The program is `arithProg141 k n` of
Part 141, UNCHANGED; `gProgA` is its output, `okProgA k n` the event `|gProgA − B| ≤ sd/2`.

* **`progCore142`**: for the program of Part 141, with FREE `θ`, `ζ`, `η`, `η′`, a bound `p₁` of
  the bad hidden event and a bound `pS` of `Pr(sd² < θ·S·(1 − Q))` as hypotheses:
  `Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (p₁ + 68·10⁶/(qA n)² + 4·(XA n ζ η η′ + 1/k)/(θ(1 − Q)) + pS)`.
* **`progRate142`**: the same with `ζ = η = 1/20`, `η′ = 1/100` and `p₁ = 0.002 + 70/n`:
  `≥ 1 − (0.002 + (70.0002 + 8.2/(θ·0.222757))/n + (4/(θ·0.222757))/k + pS)`.
* **`alloc142`** (item 1): re-allocation of `θ`, `ζ`, `η`, `η′` in the formula of Part 141 gives
  no real gain: `Pr(ok) ≥ 1 − (0.002 + 2030.6/n + 180/k)` (the allocation of Part 141; the
  constant `2031` of Part 141 is this number, rounded up).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141

/-- **The headline of Part 141 in formula form, for the program output.** For `n ≥ 4096`,
`k ≥ 1`, `0 < θ < 1`, `0 < ζ < 1`, `η, η′ > 0`: if the bad hidden event has probability at most
`p₁` and `Pr(sd² < θ·(4/n)(1 − Q)) ≤ pS` (`Q = κ^{∘6}(0)`), then
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (p₁ + 68·10⁶/(qA n)² + 4(XA n ζ η η′ + 1/k)/(θ(1 − Q)) + pS)`. -/
theorem progCore142 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η')
    {p₁ pS : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    (hS : (mlpTriple 2 n).real
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤ pS) :
    1 - (p₁ + 68000000 / (qA n : ℝ) ^ 2 +
        4 * (XA n ζ η η' + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) + pS) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set s : ℝ := θ * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  set μ := (mlpTriple 2 n).prod (gamK k n) with hμ
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWA n ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPtA_null hn k]
    rfl
  have h1' : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}ᶜ ≤ p₁ + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWA n}).trans_le
      (badA_prob_gen hn h1)
  have h2 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        s ≤ (gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (XA n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
    have hT := errSampleTailA hn hζ0 hζ1 hη hη' hk hs0
    have hsub : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        s ≤ (gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ⊆
        {p | s ≤ errSA k n p} ∪ Z := by
      rintro p ⟨hg, he⟩
      by_cases hz : ∃ i, normSq (preA p.1.1 (p.2 i)) = 0
      · exact Or.inr ⟨hg, hz⟩
      · left
        push Not at hz
        change _ ≤ errSA k n p
        unfold errSA
        rw [Set.indicator_of_mem (show p.1.1 ∈ goodWA n from hg),
          ← gProgA_eq k p.1.1 p.1.2.1 p.1.2.2 p.2 hz]
        exact he
    calc _ ≤ μ.real ({p | s ≤ errSA k n p} ∪ Z) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real {p | s ≤ errSA k n p} + μ.real Z := measureReal_union_le _ _
      _ ≤ _ := by rw [hZ0, add_zero]; exact hT
  have h3 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 < 4 * s} ≤ pS := by
    have e : (4 : ℝ) * s = θ * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by rw [hs]; ring
    rw [e]
    exact (prod_fst_real (mlpTriple 2 n) (gamK k n)
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))}).trans_le hS
  have h := ok_of_three μ
    (d := fun p => gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (fun p => sdn_nonneg' _ _ _) h1' h2 h3
  have e : (XA n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s =
      4 * (XA n ζ η η' + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) := by
    rw [hs]
    field_simp
  rw [e] at h
  exact h

/-- **The rate of the program for a free `θ` and a bound `pS` of the spread event**, with the
bad hidden event of Part 140 (`0.002 + 70/n`) and `ζ = η = 1/20`, `η′ = 1/100`: for `n ≥ 4096`,
`k ≥ 1`, `0 < θ < 1`:
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + (70.0002 + 8.2/(θ·0.222757))/n +
  (4/(θ·0.222757))/k + pS)`. -/
theorem progRate142 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    {pS : ℝ}
    (hS : (mlpTriple 2 n).real
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤ pS) :
    1 - (2 / 1000 + (700002 / 10000 + 82 / 10 / (θ * (222757 / 1000000))) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ) + pS) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn1 : 1 ≤ n := by omega
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ 2 / 1000 + 70 / (n : ℝ) := by
    have := goodHat_prob hn
    rw [measureReal_compl (goodHat_meas hn1), probReal_univ]
    linarith
  have h := progCore142 hn hk hθ0 (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
    (by norm_num) (η' := 1 / 100) (by norm_num) h1 hS
  refine le_trans ?_ h
  have hX := XA_le hn
  have hX0 := XA_nonneg hn (1 / 20) (η := 1 / 20) (by norm_num) (η' := 1 / 100) (by norm_num)
  have t4 := qTerm_le hn
  have hk1 : (0 : ℝ) < (k : ℝ)⁻¹ := by positivity
  -- the Markov term
  have tM : 4 * (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) ≤
      82 / 10 / (θ * (222757 / 1000000)) / (n : ℝ) + 4 / (θ * (222757 / 1000000)) / (k : ℝ) := by
    have hden : θ * (222757 / 1000000) ≤ θ * (1 - kappa^[6] 0) :=
      mul_le_mul_of_nonneg_left hy hθ0.le
    have hnum : 0 ≤ 4 * (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) := by positivity
    calc 4 * (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0))
        ≤ 4 * (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hden
      _ ≤ 4 * (2050 / 1000 * (1 / (n : ℝ)) + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
          field_simp
          ring
  have e1 : (700002 / 10000 + 82 / 10 / (θ * (222757 / 1000000))) / (n : ℝ) =
      70 / (n : ℝ) + 1 / 5000 * (1 / (n : ℝ)) + 82 / 10 / (θ * (222757 / 1000000)) / (n : ℝ) := by
    field_simp
    ring
  rw [e1]
  linarith

/-- **`alloc142` (item 1): the constant from re-allocation alone.** For `n ≥ 4096`, `k ≥ 1`:
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 2030.6/n + 180/k)`. This is the allocation of Part 141
(`θ = 1/10`, `ζ = η = 1/20`, `η′ = 1/100`); the formula of Part 141 has its minimum over `θ`
near `θ = 0.1015`, with the value `2030.4` (arithmetic outside Lean). So re-allocation gives no
gain. -/
theorem alloc142 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 20306 / 10 / (n : ℝ) + 180 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progRate142 hn hk (θ := 1 / 10) (by norm_num) (spreadLow139 hn (by norm_num))
  refine le_trans ?_ h
  have t2 := chebA_le hn
  have e1 : (700002 / 10000 + 82 / 10 / (1 / 10 * (222757 / 1000000 : ℝ))) / (n : ℝ) ≤
      4382 / 10 * (1 / (n : ℝ)) := by
    rw [div_le_iff₀ hx0]
    have : 4382 / 10 * (1 / (n : ℝ)) * (n : ℝ) = 4382 / 10 := by field_simp
    rw [this]
    norm_num
  have e2 : 4 / (1 / 10 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 180 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : 20306 / 10 / (n : ℝ) = 20306 / 10 * (1 / (n : ℝ)) := by ring
  rw [e3]
  linarith

end BstLean.Part142

open BstLean.Part142 in
#print axioms progCore142
open BstLean.Part142 in
#print axioms progRate142
open BstLean.Part142 in
#print axioms alloc142
