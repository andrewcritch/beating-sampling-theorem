import BstLean.Part141Sample
import BstLean.Part141Cost

/-!
# Part 141, item 4 (`arithProg141`, `arithCost141`): the fully ARITHMETIC one-pass program
succeeds

Role: `delegations/statements/p141-spec.md`, item 4. Paper sources: `onW8c-cx.md` §§2–3, §7,
`onW17c-cx.md` §7, `MM-best-result.md` Theorem 3(a).

* **`arithProg141 k n`**: ONE straight-line program in the model `RProg` of Part 130 (operations
  `+ − × ÷ √ relu`, each costs one; rational constants; reading an input is free). Its inputs
  are the entries of `W = (M₁, M₂, M₃)`, `k` Gaussian vectors, and the entries of `A` and `F`.
  It has NO oracle and NO real constant: the constants are the rational numbers `cA n`, `c1A n`,
  the rational atoms `zA n` and the rational weights `pA n` (they depend on `n` only).
* `gProgA k W A F γ`: its output; `gProgA_eq`: it is the sample mean `gSampleA` if no point is
  zero before the normalization; `zeroPtA_null`.
* **`arithProgSucceeds141`**: `Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 2031/n + 180/k)`, every
  `n ≥ 4096`, `k ≥ 1`.
* **`arithCost141_focus`**: the operation count is at most
  `2m² + m(6n + 4·LA n + 4) + LA n + 12 + k(5n + 2 + cost of A + cost of F)`, `m = mW n`,
  `LA n = 2·RA n·hA n + 1` atoms; `RA_le`: `RA n ≤ 19 + ⌈log₂ n⌉`; `RA_frontier`,
  `hA_frontier`, `LA_frontier`: `LA n ≤ 1689667` for `n ≤ 16384`;
  **`arithCost141_frontier`**: for `1 ≤ n ≤ 16384` the count is at most
  `2m² + m(6n + 6758672) + 1689679 + k(…)`; **`arithCost141_ratio`**: at most `2.000002·m²` plus
  the `k` evaluations, for `4096 ≤ n ≤ 16384`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-- **The arithmetic one-pass program**: `arithProg` of `Part141Cost` at the widths of the Focus
(`N = 2n` inputs of `W`, hidden widths `mW n`, `mA n`, `mF n`) with the rational constants of
`Part141Tau`: `LA n` atoms `zA n` with weights `pA n`, and the constants `cA n`, `c1A n`. -/
noncomputable def arithProg141 (k n : ℕ) :
    RProg (ArIn k (2 * n) n (mW n) (mA n) (mF n)) Unit :=
  arithProg k (2 * n) n (mW n) (mA n) (mF n) (LA n) (cA n) (c1A n) (pA n) (zA n)

/-- **The output of the arithmetic program** on `(W, A, F)` and the `k` Gaussian vectors `γ`. -/
noncomputable def gProgA (k : ℕ) {n : ℕ} (W : MlpParam (2 * n) (mW n) n)
    (A : MlpParam n (mA n) n) (F : MlpParam n (mF n) 1) (γ : Fin k → Fin n → ℝ) : ℝ :=
  (arithProg141 k n).eval (arVal W γ A F) ()

section link

variable {n : ℕ}

/-- The program computes the sample mean of `Part141Sample` if no point is zero before the
normalization. -/
theorem gProgA_eq (k : ℕ) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n (mF n) 1) (γ : Fin k → Fin n → ℝ)
    (h : ∀ i, normSq (preA W (γ i)) ≠ 0) :
    gProgA k W A F γ = gSampleA k W A F γ := by
  unfold gProgA arithProg141
  rw [arithProg_eval_sphPt (cA n) (c1A n) (pA n) (zA n) W γ A F (fun i => h i)]
  rfl

/-- For `τ̃₀ ≠ 0`, almost no `k`-tuple of Gaussian vectors has a zero point before the
normalization. -/
theorem preA_null (hn : 1 ≤ n) (k : ℕ) (W : MlpParam (2 * n) (mW n) n)
    (hτ : tauWA W ≠ 0) :
    gamK k n {γ | ∃ i, normSq (preA W (γ i)) = 0} = 0 := by
  have inst : NullSingletonClass (stdGauss (Fin n)) := stdGauss_nullSingleton (n := n) hn
  set c := cenA W with hc
  set τ := tauWA W with hτd
  set g₀ : Fin n → ℝ := (-τ⁻¹) • c with hg₀
  have hsub : {γ : Fin k → Fin n → ℝ | ∃ i, normSq (preA W (γ i)) = 0} ⊆
      ⋃ i : Fin k, {γ | γ i = g₀} := by
    rintro γ ⟨i, hi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have h0 : preA W (γ i) = 0 := eq_zero_of_normSq hi
    have h1 : c + τ • γ i = 0 := h0
    change γ i = g₀
    have h2 : τ • γ i = -c := by
      have := eq_neg_of_add_eq_zero_right h1
      exact this
    rw [hg₀]
    funext j
    have h3 := congrFun h2 j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h3 ⊢
    field_simp
    linarith
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => ?_
  unfold gamK
  exact Measure.pi_hyperplane (μ := fun _ : Fin k => stdGauss (Fin n)) i g₀

end link

/-! ## The program succeeds -/

/-- The success event of the arithmetic program: `|gProgA − B| ≤ sd/2`. -/
def okProgA (k n : ℕ) : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
    MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) :=
  {p | |gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
    sdn p.1.1 p.1.2.1 p.1.2.2 / 2}

/-- The event "`W` is good and a point is zero before the normalization" has probability `0`. -/
lemma zeroPtA_null {n : ℕ} (hn : 4096 ≤ n) (k : ℕ) :
    ((mlpTriple 2 n).prod (gamK k n))
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} = 0 := by
  have hn1 : 1 ≤ n := by omega
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWA n ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have mZ : MeasurableSet Z := by
    have m1 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} :=
      (measurable_fst.comp measurable_fst) (goodWA_meas hn1)
    have m2 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} := by
      have e : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
          ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} =
          ⋃ i : Fin k, {p | normSq (preA p.1.1 (p.2 i)) = 0} := by
        ext p; simp
      rw [e]
      refine MeasurableSet.iUnion fun i => ?_
      have hm : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => normSq (preA p.1.1 (p.2 i))) :=
        measurable_normSq.comp (measurable_preA.comp
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_pi_apply i).comp measurable_snd)))
      exact hm (measurableSet_singleton 0)
    exact m1.inter m2
  rw [Measure.measure_prod_null mZ]
  refine Filter.Eventually.of_forall fun t => ?_
  change gamK k n (Prod.mk t ⁻¹' Z) = 0
  by_cases hg : t.1 ∈ goodWA n
  · have hτ : tauWA t.1 ≠ 0 := (tauA_pos hn hg).ne'
    refine measure_mono_null ?_ (preA_null hn1 k t.1 hτ)
    rintro γ ⟨-, h⟩
    exact h
  · have e : Prod.mk t ⁻¹' Z = ∅ := by
      ext γ
      simp only [Set.mem_preimage, hZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h
      exact absurd h hg
    rw [e]
    simp

/-- **`arithProgSucceeds141`: the fully arithmetic one-pass program succeeds.** For every
`n ≥ 4096` and `k ≥ 1`, with `gProgA` the output of the straight-line program `arithProg141 k n`
(operations `+ − × ÷ √ relu` and rational constants only) on the entries of `(W, A, F)` and `k`
independent standard Gaussian vectors:
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 2031/n + 180/k)`, the probability over `(W, A, F)` and
the `k` Gaussian vectors. -/
theorem arithProgSucceeds141 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 2031 / (n : ℝ) + 180 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hs0 : (0 : ℝ) < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 := by
    have : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
    positivity
  set μ := (mlpTriple 2 n).prod (gamK k n) with hμ
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWA n ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPtA_null hn k]
    rfl
  have h1 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}ᶜ ≤
      2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWA n}).trans_le (badA_prob hn)
  have h2 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) := by
    have hT := errSampleTailA hn (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
      (by norm_num) (η' := 1 / 100) (by norm_num) hk hs0
    have hsub : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ⊆
        {p | 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤ errSA k n p} ∪ Z := by
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
    calc _ ≤ μ.real ({p | 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤ errSA k n p} ∪ Z) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real {p | 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤ errSA k n p} +
          μ.real Z := measureReal_union_le _ _
      _ ≤ _ := by rw [hZ0, add_zero]; exact hT
  have h3 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 <
          4 * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4)} ≤
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 := by
    have e : (4 : ℝ) * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by ring
    rw [e]
    exact (prod_fst_real (mlpTriple 2 n) (gamK k n)
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0))}).trans_le
      (spreadLow139 hn (by norm_num))
  have h := ok_of_three μ
    (d := fun p => gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (fun p => sdn_nonneg' _ _ _) h1 h2 h3
  have ha := rateA_arith hn hk
  exact le_trans (by linarith) h

/-! ## The operation count -/

/-- **`arithCost141_focus`.** The operation count of the arithmetic one-pass program is at most
`2m² + m(6n + 4·LA n + 4) + LA n + 12 + k·(5n + 2 + mlpCost n mA n + mlpCost n mF 1)`,
`m = mW n`, with `LA n = 2·RA n·hA n + 1` atoms. The leading term is `2m²`: one pass over
`M₂`. -/
theorem arithCost141_focus (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (arithProg141 k n).cost ≤
      2 * mW n ^ 2 + mW n * (6 * n + 4 * LA n + 4) + LA n + 12 +
        k * (5 * n + 2 + mlpCost n (mA n) n + mlpCost n (mF n) 1) :=
  arithCost141 k n (mW n) (mA n) (mF n) (LA n) hn (cA n) (c1A n) (pA n) (zA n)

/-- `RA n ≤ 19 + ⌈log₂ n⌉`. -/
lemma RA_le (n : ℕ) : RA n ≤ 19 + Nat.clog 2 n := by
  unfold RA qA
  refine Nat.clog_le_of_le_pow ?_
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) n
  rw [pow_add]
  nlinarith

/-- `RA n ≤ 33` for `n ≤ 16384`. -/
lemma RA_frontier {n : ℕ} (hn : n ≤ 16384) : RA n ≤ 33 := by
  unfold RA qA
  refine Nat.clog_le_of_le_pow ?_
  norm_num
  omega

/-- `hA n ≤ 25601` for `n ≤ 16384`. -/
lemma hA_frontier {n : ℕ} (hn : n ≤ 16384) : hA n ≤ 25601 := by
  unfold hA qA
  have h1 : Nat.sqrt (4 * (10000 * n)) ≤ Nat.sqrt (25600 ^ 2) := Nat.sqrt_le_sqrt (by omega)
  rw [Nat.sqrt_eq'] at h1
  omega

/-- The number of atoms in the frontier interval: `LA n ≤ 1689667` for `n ≤ 16384`. -/
lemma LA_frontier {n : ℕ} (hn : n ≤ 16384) : LA n ≤ 1689667 := by
  have h := RA_frontier hn
  have h2 := hA_frontier hn
  have e : LA n = 2 * RA n * hA n + 1 := rfl
  rw [e]
  have : 2 * RA n * hA n ≤ 2 * 33 * 25601 := Nat.mul_le_mul (by omega) h2
  omega

/-- **`arithCost141_frontier`.** For `1 ≤ n ≤ 16384` (this contains the frontier interval): the
operation count of the arithmetic one-pass program is at most
`2m² + m·(6n + 6758672) + 1689679 + k·(5n + 2 + mlpCost n mA n + mlpCost n mF 1)`,
`m = mW n`. -/
theorem arithCost141_frontier (k : ℕ) {n : ℕ} (hn : 1 ≤ n) (h16 : n ≤ 16384) :
    (arithProg141 k n).cost ≤
      2 * mW n ^ 2 + mW n * (6 * n + 6758672) + 1689679 +
        k * (5 * n + 2 + mlpCost n (mA n) n + mlpCost n (mF n) 1) := by
  have h := arithCost141_focus k hn
  have hL := LA_frontier h16
  have h1 : mW n * (6 * n + 4 * LA n + 4) ≤ mW n * (6 * n + 6758672) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **`arithCost141_ratio`.** In the frontier interval (`4096 ≤ n ≤ 16384`): the operation count
of the arithmetic one-pass program is at most `2.000002·m²` plus the `k` evaluations of `F∘A`
(`10⁶·cost ≤ 2000002·m² + 10⁶·k·(5n + 2 + mlpCost n mA n + mlpCost n mF 1)`), `m = mW n`. -/
theorem arithCost141_ratio (k : ℕ) {n : ℕ} (hn : 4096 ≤ n) (h16 : n ≤ 16384) :
    1000000 * (arithProg141 k n).cost ≤
      2000002 * mW n ^ 2 +
        1000000 * (k * (5 * n + 2 + mlpCost n (mA n) n + mlpCost n (mF n) 1)) := by
  have h := arithCost141_frontier k (n := n) (by omega) h16
  have hm := mW_ge hn
  have h1 : 4398046511104 * mW n ≤ mW n * mW n := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left (mW n) hm
  have h2 : mW n * (6 * n + 6758672) ≤ mW n * 6856976 := Nat.mul_le_mul_left _ (by omega)
  have e2 : mW n ^ 2 = mW n * mW n := pow_two (mW n)
  rw [e2] at h ⊢
  omega

/-- The number of entries of `W = (M₁, M₂, M₃)` (the inputs `Sum.inl _` of the program):
`m·2n + m² + n·m`. The program uses each of them (each entry of `M₁` in one multiplication, the
square; each entry of `M₂`, `M₃` in one multiplication); reads are free in the model `RProg`. -/
theorem worldEntries141 (n m : ℕ) :
    Fintype.card (MlpW (2 * n) m n) = m * (2 * n) + m * m + n * m := by
  simp [MlpW, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-! ## The explicit scale -/

/-- `XA n (1/20) (1/20) (1/100) ≤ 2.05/n`. -/
lemma XA_le {n : ℕ} (hn : 4096 ≤ n) :
    XA n (1 / 20) (1 / 20) (1 / 100) ≤ 2050 / 1000 * (1 / (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hEH' := EHH_scale hn
  have hEH0 := EHH_nonneg hn (1 / 20)
  have hp := pertA_eq (n := n) (by omega)
  have ht0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  unfold XA
  have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * (1 / (n : ℝ)) := by ring
  rw [e183, hp]
  have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
  have e101 : (1 : ℝ) + 1 / (1 / 100) = 101 := by norm_num
  rw [e84, e101]
  linarith

/-- **The arithmetic program at the explicit scale**, with the probability `p₁` of the bad
hidden event as a hypothesis: for `n ≥ 4096`, `k ≥ 1`, `ε > 0`:
`Pr(|gProgA − B| ≤ ε·scale139 n) ≥ 1 − (p₁ + 9.3/(ε²n) + 4.5/(ε²k))`. -/
theorem arithProgExplicit141_core {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) {p₁ : ℝ} (h1 : (mlpTriple 2 n).real {t | t.1 ∉ goodWA n} ≤ p₁) :
    1 - (p₁ + 93 / 10 / (ε ^ 2 * (n : ℝ)) + 9 / 2 / (ε ^ 2 * (k : ℝ))) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          ε * scale139 n} := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set S : ℝ := 4 / (n : ℝ) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set s : ℝ := ε ^ 2 * (S * (1 - kappa^[6] 0)) with hs
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
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}ᶜ ≤ p₁ :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWA n}).trans_le h1
  have hT := errSampleTailA hn (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
    (by norm_num) (η' := 1 / 100) (by norm_num) hk hs0
  have h2 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        s ≤ (gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
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
  have h := ok_of_two μ
    (G := {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n})
    (d := fun p => gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    h1' h2
  rw [eps_scale hε.le]
  refine le_trans ?_ h
  have hX := XA_le hn
  have hterm : (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s ≤
      93 / 10 / (ε ^ 2 * (n : ℝ)) + 9 / 2 / (ε ^ 2 * (k : ℝ)) := by
    have e : (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s =
        (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) / (ε ^ 2 * (1 - kappa^[6] 0)) := by
      rw [hs, hS]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : (93 / 10 / (ε ^ 2 * (n : ℝ)) + 9 / 2 / (ε ^ 2 * (k : ℝ))) *
        (ε ^ 2 * (1 - kappa^[6] 0)) =
        (93 / 10 * (1 / (n : ℝ)) + 9 / 2 * (1 / (k : ℝ))) * (1 - kappa^[6] 0) := by
      field_simp
    rw [e2, inv_eq_one_div]
    have ha : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have hb : (0 : ℝ) < 1 / (k : ℝ) := by positivity
    nlinarith
  linarith

/-- **Level `99/100` for the arithmetic program at the explicit scale, inside the frontier
interval.** For every `n ≥ 10000` and every `k ≥ 100·n`:
`Pr(|gProgA − B| ≤ (1/2)·scale139 n) ≥ 99/100`, with `scale139 n = √((4/n)(1 − κ^{∘6}(0)))`
(NOT the realized spread `sd`), the probability over `(W, A, F)` and the `k` Gaussian vectors. -/
theorem arithProgExplicit141_99 {n : ℕ} (hn : 10000 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (gamK k n)).real
      {p | |gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        1 / 2 * scale139 n} := by
  have hx : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hkR : (100 : ℝ) * (n : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by nlinarith
  have h := arithProgExplicit141_core (n := n) (by omega) (k := k) (by omega) (ε := 1 / 2)
    (by norm_num) (badA_prob_gen (by omega) (goodHat_prob_sharp (n := n) (by omega)))
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
  have t6 : 9 / 2 / ((1 / 2 : ℝ) ^ 2 * (k : ℝ)) ≤ 18 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end BstLean.Part141

open BstLean.Part141 in
#print axioms gProgA_eq
open BstLean.Part141 in
#print axioms arithProgSucceeds141
open BstLean.Part141 in
#print axioms arithCost141_focus
open BstLean.Part141 in
#print axioms arithCost141_frontier
open BstLean.Part141 in
#print axioms arithCost141_ratio
open BstLean.Part141 in
#print axioms worldEntries141
open BstLean.Part141 in
#print axioms arithProgExplicit141_core
open BstLean.Part141 in
#print axioms arithProgExplicit141_99
