import BstLean.Part156Num
import BstLean.Part156Samp

/-!
# Part 156 (item 5, assembly): the CONDITIONAL classifier theorem at `n = 16 384`

This file joins the master inequality (`Part156Master`), the sampling step (`Part156Samp`) and
the numeric ledger (`Part156Num`).

* `master_sampling`: the master inequality with the hit fraction `R` equal to the mean of `k`
  variables that are, for each retained value in the good event, independent with values in
  `{0, 1}` and mean `q̃`. The sampling charge is `2 exp (-k d_s²)`.
* `classifier_conditional_16384`: at the ledger constants and `k = 10¹²`:
  IF the retained-data events with the stated charges exist and (GP-W), (GP-A), (REPL) and the
  replacement root hold on them, THEN the failure probability is below `0.008195686`.
* `classifier_conditional_ge_16384`: the same failure bound for every real `n ≥ 16 384`, with the
  same constants and charges.
* `classifier_conditional_16384_success`: THEN the success probability is at least `99/100`.

THESE THEOREMS ARE CONDITIONAL. They are NOT a Lean proof of the classifier theorem. The spaces
`Ω_C`, `Ω_W`, `Ω_A`, `Ω_S`, the functions `p`, `P`, `q̃`, `X`, the events `H`, `E₁` and the radius
`Hbar` are abstract. No ReLU network occurs in these files. The hypotheses (GP-W), (GP-A),
(REPL), `hQq` and the three charges are ASSUMED; the paper derives them from the Gaussian
structure of the networks, and no part of that derivation is in Lean.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open MeasureTheory ProbabilityTheory Real Set

variable {ΩC ΩW ΩA ΩS : Type*} [MeasurableSpace ΩC] [MeasurableSpace ΩW] [MeasurableSpace ΩA]
  [MeasurableSpace ΩS]

/-- The hit fraction of `k` draws. -/
noncomputable def hitFrac {k : ℕ} (X : Fin k → ΩC × ΩS → ℝ) : ΩC × ΩS → ℝ :=
  fun x => (∑ i, X i x) / k

/-- **The master inequality with the sampling step, conditional on its hypotheses.**
As `master_markov`, with `R = hitFrac X` and, for each retained value `c` in the good event,
`σ ↦ X i (c, σ)` independent with values in `{0, 1}` and mean `q̃ c`. -/
theorem master_sampling (μC : Measure ΩC) (μW : Measure ΩW) (μA : Measure ΩA) (μS : Measure ΩS)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS]
    {p : ΩC × (ΩW × ΩA) → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩC → ΩA → ℝ} (hPm : ∀ c, Measurable (P c)) (hP0 : ∀ c x, 0 ≤ P c x)
    (hP1 : ∀ c x, P c x ≤ 1)
    {k : ℕ} {X : Fin k → ΩC × ΩS → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX01 : ∀ i x, X i x = 0 ∨ X i x = 1)
    {qt : ΩC → ℝ} {H E₁ : Set ΩC} (hH : MeasurableSet H) (hE₁ : MeasurableSet E₁)
    {Hbar : ΩC → ℝ} (hHm : Measurable Hbar)
    {n cW cf hW hA ds a τp τm δhid δextra vW : ℝ}
    (hn : 0 < n) (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 < hW) (hhA : 0 ≤ hA) (hds : 0 < ds)
    (ha : 1 < a) (hτp : 0 < τp) (hτm : τm < 0)
    (hside1 : (hA + ds) + hW < √(1 / 100 / a)) (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW cW cf τp ≤ 0) (hEm : Eminus a (hA + ds) hW cW cf τm ≤ 0)
    (hhid : μC.real Hᶜ ≤ δhid)
    (hHint : IntegrableOn (fun c => Hbar c ^ 2) H μC)
    (hvW : ∫ c in H, Hbar c ^ 2 ∂μC ≤ vW)
    (hextra : μC.real (H ∩ E₁ᶜ) ≤ δextra)
    (GPW : ∀ c ∈ H ∩ {c | Hbar c ≤ hW} ∩ E₁, ∀ (ωA : ΩA) (s : ℝ),
      ∫ ωW, exp (s * p (c, (ωW, ωA))) ∂μW ≤
        exp (Tfun (cW / n) s * ∫ ωW, p (c, (ωW, ωA)) ∂μW))
    (GPA : ∀ c ∈ H ∩ {c | Hbar c ≤ hW} ∩ E₁, ∀ u : ℝ,
      ∫ ωA, exp (u * P c ωA) ∂μA ≤ exp (Tfun (cf / n) u * ∫ ωA, P c ωA ∂μA))
    (REPL : ∀ c ∈ H ∩ {c | Hbar c ≤ hW} ∩ E₁, ∀ ωA : ΩA,
      |√(∫ ωW, p (c, (ωW, ωA)) ∂μW) - √(P c ωA)| ≤ hW)
    (hQq : ∀ c ∈ H ∩ {c | Hbar c ≤ hW} ∩ E₁, |√(∫ ωA, P c ωA ∂μA) - √(qt c)| ≤ hA)
    (hXind : ∀ c ∈ H ∩ {c | Hbar c ≤ hW} ∩ E₁, iIndepFun (fun i σ => X i (c, σ)) μS)
    (hXmean : ∀ c ∈ H ∩ {c | Hbar c ≤ hW} ∩ E₁, ∀ i, ∫ σ, X i (c, σ) ∂μS = qt c) :
    (μC.prod ((μW.prod μA).prod μS)).real (failSet a p (hitFrac X)) ≤
      δhid + vW / hW ^ 2 + δextra + Bplus n a (hA + ds) hW cW cf τp +
        Bminus n a (hA + ds) hW cW cf τm + 2 * exp (-k * ds ^ 2) := by
  have hRm : Measurable (hitFrac X) := by
    unfold hitFrac
    exact (Finset.measurable_sum _ (fun i _ => hXm i)).div_const _
  have hR0 : ∀ x, 0 ≤ hitFrac X x := by
    intro x
    unfold hitFrac
    refine div_nonneg (Finset.sum_nonneg (fun i _ => ?_)) (Nat.cast_nonneg _)
    rcases hX01 i x with h | h <;> simp [h]
  refine master_markov μC μW μA μS hpm hp0 hp1 hPm hP0 hP1 hRm hR0 hH hE₁ hHm hn hcW hcf hhW
    hhA hds.le ha hτp hτm (by positivity) hside1 hside2 hEp hEm hhid hHint hvW hextra GPW GPA
    REPL hQq ?_
  intro c hc
  exact sampling_root (μ := μS) (X := fun i σ => X i (c, σ)) (hXind c hc)
    (fun i => (hXm i).comp measurable_prodMk_left) (fun i σ => hX01 i _) (hXmean c hc) hds

/-- Decrease in dimension of the upper tail: if `E_+ ≤ 0` and `n ≥ 16384` then
`B_+(n) ≤ B_+(16384)`. -/
lemma Bplus_anti {n a h hW cW cf τ : ℝ} (hn : 16384 ≤ n) (hE : Eplus a h hW cW cf τ ≤ 0) :
    Bplus n a h hW cW cf τ ≤ Bplus 16384 a h hW cW cf τ := by
  unfold Bplus
  exact exp_le_exp.2 (by nlinarith)

/-- Decrease in dimension of the lower tail: if `E_- ≤ 0` and `n ≥ 16384` then
`B_-(n) ≤ B_-(16384)`. -/
lemma Bminus_anti {n a h hW cW cf τ : ℝ} (hn : 16384 ≤ n) (hE : Eminus a h hW cW cf τ ≤ 0) :
    Bminus n a h hW cW cf τ ≤ Bminus 16384 a h hW cW cf τ := by
  unfold Bminus
  exact exp_le_exp.2 (by nlinarith)

/-- **The conditional classifier theorem at `n = 16 384` (failure bound).**
IF, on abstract probability spaces, there are a retained hidden/frame event `H` with
`μ_C (Hᶜ) ≤ 0.001900001`, a retained radius `Hbar` with `E[1_H Hbar²] ≤ 0.000741853·(0.004)²`,
a retained-data event `E₁` with `μ_C (H ∩ E₁ᶜ) ≤ 0.001104285235085`, and on
`H ∩ {Hbar ≤ 0.0024160420} ∩ E₁` the hypotheses (GP-W) with `L_W = 1.377/16384`, (GP-A) with
`L_A = 1.743/16384`, (REPL) with `h_W = 0.0024160420`, the replacement root
`|√Q - √q̃| ≤ 0.006583 + 10⁻²⁰`, and `10¹²` independent `{0, 1}`-valued draws of mean `q̃`,
THEN the output `U = min 1 (max (1/100) (2.2524763228 R))` fails `p ≤ U ≤ max (10 p) (1/100)` with
probability less than `0.008195686`. -/
theorem classifier_conditional_16384 (μC : Measure ΩC) (μW : Measure ΩW) (μA : Measure ΩA)
    (μS : Measure ΩS)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS]
    {p : ΩC × (ΩW × ΩA) → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩC → ΩA → ℝ} (hPm : ∀ c, Measurable (P c)) (hP0 : ∀ c x, 0 ≤ P c x)
    (hP1 : ∀ c x, P c x ≤ 1)
    {X : Fin (10 ^ 12) → ΩC × ΩS → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX01 : ∀ i x, X i x = 0 ∨ X i x = 1)
    {qt : ΩC → ℝ} {H E₁ : Set ΩC} (hH : MeasurableSet H) (hE₁ : MeasurableSet E₁)
    {Hbar : ΩC → ℝ} (hHm : Measurable Hbar)
    (hhid : μC.real Hᶜ ≤ δhidL)
    (hHint : IntegrableOn (fun c => Hbar c ^ 2) H μC)
    (hvW : ∫ c in H, Hbar c ^ 2 ∂μC ≤ vWL)
    (hextra : μC.real (H ∩ E₁ᶜ) ≤ δextraL)
    (GPW : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ (ωA : ΩA) (s : ℝ),
      ∫ ωW, exp (s * p (c, (ωW, ωA))) ∂μW ≤
        exp (Tfun (cWL / 16384) s * ∫ ωW, p (c, (ωW, ωA)) ∂μW))
    (GPA : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ u : ℝ,
      ∫ ωA, exp (u * P c ωA) ∂μA ≤ exp (Tfun (cfL / 16384) u * ∫ ωA, P c ωA ∂μA))
    (REPL : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ ωA : ΩA,
      |√(∫ ωW, p (c, (ωW, ωA)) ∂μW) - √(P c ωA)| ≤ hWL)
    (hQq : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, |√(∫ ωA, P c ωA ∂μA) - √(qt c)| ≤ hAL)
    (hXind : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, iIndepFun (fun i σ => X i (c, σ)) μS)
    (hXmean : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ i, ∫ σ, X i (c, σ) ∂μS = qt c) :
    (μC.prod ((μW.prod μA).prod μS)).real (failSet aL p (hitFrac X)) < 8195686 / 10 ^ 9 := by
  have h := master_sampling μC μW μA μS hpm hp0 hp1 hPm hP0 hP1 hXm hX01 hH hE₁ hHm
    (n := 16384) (cW := cWL) (cf := cfL) (hW := hWL) (hA := hAL) (ds := dsL) (a := aL)
    (τp := τpL) (τm := τmL) (δhid := δhidL) (δextra := δextraL) (vW := vWL)
    (by norm_num) (by unfold cWL; norm_num) (by unfold cfL; norm_num) (by unfold hWL; norm_num)
    (by unfold hAL; norm_num) (by unfold dsL; norm_num) (by unfold aL; norm_num)
    (by unfold τpL; norm_num) (by unfold τmL; norm_num) side1_ledger side2_ledger
    Eplus_ledger_neg.le Eminus_ledger_neg.le hhid hHint hvW hextra GPW GPA REPL hQq hXind hXmean
  have hk : 2 * exp (-((10 ^ 12 : ℕ) : ℝ) * dsL ^ 2) = 2 * exp (-100) := by
    unfold dsL; norm_num
  rw [hk] at h
  have h2 := ledger_total
  linarith

/-- **The conditional classifier theorem for a real `n ≥ 16 384` (failure bound), with the same
constants and charges.** The two endpoint tails decrease in `n` (`Bplus_anti`, `Bminus_anti`).
IF, on abstract probability spaces, there are a retained hidden/frame event `H` with
`μ_C (Hᶜ) ≤ 0.001900001`, a retained radius `Hbar` with `E[1_H Hbar²] ≤ 0.000741853·(0.004)²`,
a retained-data event `E₁` with `μ_C (H ∩ E₁ᶜ) ≤ 0.001104285235085`, and on
`H ∩ {Hbar ≤ 0.0024160420} ∩ E₁` the hypotheses (GP-W) with `L_W = 1.377/n`, (GP-A) with
`L_A = 1.743/n`, (REPL) with `h_W = 0.0024160420`, the replacement root
`|√Q - √q̃| ≤ 0.006583 + 10⁻²⁰`, and `10¹²` independent `{0, 1}`-valued draws of mean `q̃`,
THEN the output `U = min 1 (max (1/100) (2.2524763228 R))` fails `p ≤ U ≤ max (10 p) (1/100)` with
probability less than `0.008195686`. -/
theorem classifier_conditional_ge_16384 {n : ℝ} (hn16 : 16384 ≤ n) (μC : Measure ΩC) (μW : Measure ΩW) (μA : Measure ΩA)
    (μS : Measure ΩS)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS]
    {p : ΩC × (ΩW × ΩA) → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩC → ΩA → ℝ} (hPm : ∀ c, Measurable (P c)) (hP0 : ∀ c x, 0 ≤ P c x)
    (hP1 : ∀ c x, P c x ≤ 1)
    {X : Fin (10 ^ 12) → ΩC × ΩS → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX01 : ∀ i x, X i x = 0 ∨ X i x = 1)
    {qt : ΩC → ℝ} {H E₁ : Set ΩC} (hH : MeasurableSet H) (hE₁ : MeasurableSet E₁)
    {Hbar : ΩC → ℝ} (hHm : Measurable Hbar)
    (hhid : μC.real Hᶜ ≤ δhidL)
    (hHint : IntegrableOn (fun c => Hbar c ^ 2) H μC)
    (hvW : ∫ c in H, Hbar c ^ 2 ∂μC ≤ vWL)
    (hextra : μC.real (H ∩ E₁ᶜ) ≤ δextraL)
    (GPW : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ (ωA : ΩA) (s : ℝ),
      ∫ ωW, exp (s * p (c, (ωW, ωA))) ∂μW ≤
        exp (Tfun (cWL / n) s * ∫ ωW, p (c, (ωW, ωA)) ∂μW))
    (GPA : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ u : ℝ,
      ∫ ωA, exp (u * P c ωA) ∂μA ≤ exp (Tfun (cfL / n) u * ∫ ωA, P c ωA ∂μA))
    (REPL : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ ωA : ΩA,
      |√(∫ ωW, p (c, (ωW, ωA)) ∂μW) - √(P c ωA)| ≤ hWL)
    (hQq : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, |√(∫ ωA, P c ωA ∂μA) - √(qt c)| ≤ hAL)
    (hXind : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, iIndepFun (fun i σ => X i (c, σ)) μS)
    (hXmean : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ i, ∫ σ, X i (c, σ) ∂μS = qt c) :
    (μC.prod ((μW.prod μA).prod μS)).real (failSet aL p (hitFrac X)) < 8195686 / 10 ^ 9 := by
  have h := master_sampling μC μW μA μS hpm hp0 hp1 hPm hP0 hP1 hXm hX01 hH hE₁ hHm
    (n := n) (cW := cWL) (cf := cfL) (hW := hWL) (hA := hAL) (ds := dsL) (a := aL)
    (τp := τpL) (τm := τmL) (δhid := δhidL) (δextra := δextraL) (vW := vWL)
    (by linarith) (by unfold cWL; norm_num) (by unfold cfL; norm_num) (by unfold hWL; norm_num)
    (by unfold hAL; norm_num) (by unfold dsL; norm_num) (by unfold aL; norm_num)
    (by unfold τpL; norm_num) (by unfold τmL; norm_num) side1_ledger side2_ledger
    Eplus_ledger_neg.le Eminus_ledger_neg.le hhid hHint hvW hextra GPW GPA REPL hQq hXind hXmean
  have hk : 2 * exp (-((10 ^ 12 : ℕ) : ℝ) * dsL ^ 2) = 2 * exp (-100) := by
    unfold dsL; norm_num
  rw [hk] at h
  have h2 := ledger_total
  have h3 := Bplus_anti hn16 Eplus_ledger_neg.le
  have h4 := Bminus_anti hn16 Eminus_ledger_neg.le
  linarith

/-- **The conditional classifier theorem at `n = 16 384` (success form).** Under the hypotheses
of `classifier_conditional_16384`, the output succeeds with probability at least `99/100`. -/
theorem classifier_conditional_16384_success (μC : Measure ΩC) (μW : Measure ΩW)
    (μA : Measure ΩA) (μS : Measure ΩS)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS]
    {p : ΩC × (ΩW × ΩA) → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩC → ΩA → ℝ} (hPm : ∀ c, Measurable (P c)) (hP0 : ∀ c x, 0 ≤ P c x)
    (hP1 : ∀ c x, P c x ≤ 1)
    {X : Fin (10 ^ 12) → ΩC × ΩS → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX01 : ∀ i x, X i x = 0 ∨ X i x = 1)
    {qt : ΩC → ℝ} {H E₁ : Set ΩC} (hH : MeasurableSet H) (hE₁ : MeasurableSet E₁)
    {Hbar : ΩC → ℝ} (hHm : Measurable Hbar)
    (hhid : μC.real Hᶜ ≤ δhidL)
    (hHint : IntegrableOn (fun c => Hbar c ^ 2) H μC)
    (hvW : ∫ c in H, Hbar c ^ 2 ∂μC ≤ vWL)
    (hextra : μC.real (H ∩ E₁ᶜ) ≤ δextraL)
    (GPW : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ (ωA : ΩA) (s : ℝ),
      ∫ ωW, exp (s * p (c, (ωW, ωA))) ∂μW ≤
        exp (Tfun (cWL / 16384) s * ∫ ωW, p (c, (ωW, ωA)) ∂μW))
    (GPA : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ u : ℝ,
      ∫ ωA, exp (u * P c ωA) ∂μA ≤ exp (Tfun (cfL / 16384) u * ∫ ωA, P c ωA ∂μA))
    (REPL : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ ωA : ΩA,
      |√(∫ ωW, p (c, (ωW, ωA)) ∂μW) - √(P c ωA)| ≤ hWL)
    (hQq : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, |√(∫ ωA, P c ωA ∂μA) - √(qt c)| ≤ hAL)
    (hXind : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, iIndepFun (fun i σ => X i (c, σ)) μS)
    (hXmean : ∀ c ∈ H ∩ {c | Hbar c ≤ hWL} ∩ E₁, ∀ i, ∫ σ, X i (c, σ) ∂μS = qt c) :
    99 / 100 ≤ (μC.prod ((μW.prod μA).prod μS)).real
      {x | success (p (x.1, x.2.1)) (outRule aL (hitFrac X (x.1, x.2.2)))} := by
  have h := classifier_conditional_16384 μC μW μA μS hpm hp0 hp1 hPm hP0 hP1 hXm hX01 hH hE₁
    hHm hhid hHint hvW hextra GPW GPA REPL hQq hXind hXmean
  have hRm : Measurable (hitFrac X) := by
    unfold hitFrac
    exact (Finset.measurable_sum _ (fun i _ => hXm i)).div_const _
  have hF := measurableSet_failSet (ΩW := ΩW) (ΩA := ΩA) aL hpm hRm
  have hc : {x : ΩC × ((ΩW × ΩA) × ΩS) |
      success (p (x.1, x.2.1)) (outRule aL (hitFrac X (x.1, x.2.2)))} =
      (failSet aL p (hitFrac X))ᶜ := by
    ext x
    simp [failSet]
  rw [hc, measureReal_compl hF, probReal_univ]
  linarith

end BstLean.Part156
