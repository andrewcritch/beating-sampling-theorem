import BstLean.Part156End

/-!
# Part 156 (item 5, abstract part): the master inequality, CONDITIONAL on its hypotheses

The space is a product `Ω_C × ((Ω_W × Ω_A) × Ω_S)` of four probability spaces:

* `Ω_C`: the retained data (in the paper: the first two matrices of each network, the centres,
  the tables, `F`, `t`);
* `Ω_W`, `Ω_A`: the residual Gaussian matrices of `W` and of `A` (the theorems here use no
  property of the Gaussian distribution; they use only the ASSUMED bounds (GP-W), (GP-A));
* `Ω_S`: the random draws of the program.

`p (c, (ω_W, ω_A))` is the target, `R (c, σ)` is the hit fraction, `U = outRule a R` is the output.

* `fibre_fail`: for one retained value, from (GP-W), (GP-A), (REPL), the replacement
  `|√Q - √q̃| ≤ h_A` and a sampling tail `μ_S {|√R - √q̃| > d_s} ≤ δ_s`:
  the failure probability is at most `B_+ + B_- + δ_s`.
* `master`: with a measurable retained-data event `E` of probability at least `1 - δ_ret` on
  which these hypotheses hold: the failure probability is at most `δ_ret + B_+ + B_- + δ_s`.
* `master_markov`: the form of the paper, with the charges
  `δ_hidden + v_W/h_W² + δ_extra + B_+ + B_- + δ_s`.

Every hypothesis named (GP-W), (GP-A), (REPL), `hQq`, `hsamp` is ASSUMED. These files do not
prove them for the networks of the classifier question.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open MeasureTheory ProbabilityTheory Real Set

section fibre

variable {ΩW ΩA ΩS : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩA] [MeasurableSpace ΩS]

lemma real_prod_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite ν] [IsProbabilityMeasure ν] (s : Set α) :
    (μ.prod ν).real (s ×ˢ (univ : Set β)) = μ.real s := by
  simp [Measure.real, Measure.prod_prod]

lemma real_prod_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite ν] [IsProbabilityMeasure μ] (s : Set β) :
    (μ.prod ν).real ((univ : Set α) ×ˢ s) = ν.real s := by
  simp [Measure.real, Measure.prod_prod]

/-- **The failure bound for one retained value, conditional on (GP-W), (GP-A), (REPL), the
replacement of `Q` by `q̃`, and a sampling tail.** `h = h_A + d_s`. -/
theorem fibre_fail (μW : Measure ΩW) (μA : Measure ΩA) (μS : Measure ΩS)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    {p : ΩW × ΩA → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩA → ℝ} (hPm : Measurable P) (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {R : ΩS → ℝ} (hR0 : ∀ σ, 0 ≤ R σ)
    {n cW cf hW hA ds a τp τm qt δs : ℝ}
    (hn : 0 < n) (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 ≤ hW) (hhA : 0 ≤ hA) (hds : 0 ≤ ds)
    (ha : 1 < a) (hτp : 0 < τp) (hτm : τm < 0)
    (hside1 : (hA + ds) + hW < √(1 / 100 / a)) (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW cW cf τp ≤ 0) (hEm : Eminus a (hA + ds) hW cW cf τm ≤ 0)
    (GPW : ∀ (ωA : ΩA) (s : ℝ),
      ∫ ωW, exp (s * p (ωW, ωA)) ∂μW ≤ exp (Tfun (cW / n) s * ∫ ωW, p (ωW, ωA) ∂μW))
    (GPA : ∀ u : ℝ, ∫ ωA, exp (u * P ωA) ∂μA ≤ exp (Tfun (cf / n) u * ∫ ωA, P ωA ∂μA))
    (REPL : ∀ ωA : ΩA, |√(∫ ωW, p (ωW, ωA) ∂μW) - √(P ωA)| ≤ hW)
    (hQq : |√(∫ ωA, P ωA ∂μA) - √qt| ≤ hA)
    (hsamp : μS.real {σ | ds < |√(R σ) - √qt|} ≤ δs) :
    ((μW.prod μA).prod μS).real {x | ¬ success (p x.1) (outRule a (R x.2))} ≤
      Bplus n a (hA + ds) hW cW cf τp + Bminus n a (hA + ds) hW cW cf τm + δs := by
  set Q := ∫ ωA, P ωA ∂μA with hQdef
  set h := hA + ds with hh
  have hh0 : 0 ≤ h := add_nonneg hhA hds
  have ha0 : 0 < a := lt_trans one_pos ha
  have hQ0 : 0 ≤ Q := integral_nonneg hP0
  have hCPR : CPR (μW.prod μA) p (cW / n) (cf / n) hW Q :=
    cpr_of_stages μW μA hpm hp0 hp1 hPm hP0 hP1 (div_pos hcW hn) hhW GPW GPA REPL
  have hA1 := tail_plus (μW.prod μA) hpm hp0 hp1 hn hcW hcf hhW hQ0 ha0 hh0 hτp hEp hCPR
  have hB1 : (μW.prod μA).real {ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} ≤
      Bminus n a h hW cW cf τm := by
    by_cases hz : 1 / 1000 < zminus a h Q
    · have := tail_minus (μW.prod μA) hpm hp0 hp1 hn hcW hcf hhW hQ0 ha0 hh0 hτm hside1 hside2
        hEm hCPR hz
      refine le_trans (measureReal_mono (fun ω hω => ?_)) this
      exact hω.1
    · have : {ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} = (∅ : Set (ΩW × ΩA)) := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun _ => hz
      rw [this, measureReal_empty]
      exact (exp_pos _).le
  have hincl : {x : (ΩW × ΩA) × ΩS | ¬ success (p x.1) (outRule a (R x.2))} ⊆
      ({ω | zplus a h Q < p ω} ×ˢ (univ : Set ΩS)) ∪
        ({ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} ×ˢ (univ : Set ΩS)) ∪
        ((univ : Set (ΩW × ΩA)) ×ˢ {σ | ds < |√(R σ) - √qt|}) := by
    rintro ⟨ω, σ⟩ hx
    by_cases hs : ds < |√(R σ) - √qt|
    · right
      exact ⟨mem_univ _, hs⟩
    · left
      have hRQ : |√(R σ) - √Q| ≤ h := by
        have h1 : |√(R σ) - √Q| ≤ |√(R σ) - √qt| + |√qt - √Q| := abs_sub_le _ _ _
        have h2 : |√qt - √Q| ≤ hA := by rw [abs_sub_comm]; exact hQq
        have h3 := not_lt.1 hs
        linarith
      rcases not_success (hp1 ω) (hR0 σ) ha0 hRQ hx with h1 | h1
      · left
        exact ⟨h1.2, mem_univ _⟩
      · right
        exact ⟨⟨h1.2.1, h1.2.2⟩, mem_univ _⟩
  calc ((μW.prod μA).prod μS).real {x | ¬ success (p x.1) (outRule a (R x.2))}
      ≤ ((μW.prod μA).prod μS).real
          (({ω | zplus a h Q < p ω} ×ˢ (univ : Set ΩS)) ∪
          ({ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} ×ˢ (univ : Set ΩS)) ∪
          ((univ : Set (ΩW × ΩA)) ×ˢ {σ | ds < |√(R σ) - √qt|})) := measureReal_mono hincl
    _ ≤ ((μW.prod μA).prod μS).real ({ω | zplus a h Q < p ω} ×ˢ (univ : Set ΩS)) +
          ((μW.prod μA).prod μS).real
            ({ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} ×ˢ (univ : Set ΩS)) +
          ((μW.prod μA).prod μS).real
            ((univ : Set (ΩW × ΩA)) ×ˢ {σ | ds < |√(R σ) - √qt|}) :=
        (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
    _ ≤ Bplus n a h hW cW cf τp + Bminus n a h hW cW cf τm + δs := by
        rw [real_prod_left, real_prod_left, real_prod_right]
        linarith

end fibre

section master

variable {ΩC ΩW ΩA ΩS : Type*} [MeasurableSpace ΩC] [MeasurableSpace ΩW] [MeasurableSpace ΩA]
  [MeasurableSpace ΩS]

/-- The failure set of the program in the product space. -/
def failSet (a : ℝ) (p : ΩC × (ΩW × ΩA) → ℝ) (R : ΩC × ΩS → ℝ) :
    Set (ΩC × ((ΩW × ΩA) × ΩS)) :=
  {x | ¬ success (p (x.1, x.2.1)) (outRule a (R (x.1, x.2.2)))}

lemma measurableSet_failSet (a : ℝ) {p : ΩC × (ΩW × ΩA) → ℝ} (hpm : Measurable p)
    {R : ΩC × ΩS → ℝ} (hRm : Measurable R) :
    MeasurableSet (failSet a p R) := by
  have hp' : Measurable fun x : ΩC × ((ΩW × ΩA) × ΩS) => p (x.1, x.2.1) :=
    hpm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hR' : Measurable fun x : ΩC × ((ΩW × ΩA) × ΩS) => R (x.1, x.2.2) :=
    hRm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hU : Measurable fun x : ΩC × ((ΩW × ΩA) × ΩS) => outRule a (R (x.1, x.2.2)) := by
    unfold outRule
    exact measurable_const.min (measurable_const.max (hR'.const_mul a))
  have h1 : MeasurableSet {x : ΩC × ((ΩW × ΩA) × ΩS) |
      p (x.1, x.2.1) ≤ outRule a (R (x.1, x.2.2))} := measurableSet_le hp' hU
  have h2 : MeasurableSet {x : ΩC × ((ΩW × ΩA) × ΩS) |
      outRule a (R (x.1, x.2.2)) ≤ max (10 * p (x.1, x.2.1)) (1 / 100)} :=
    measurableSet_le hU ((hp'.const_mul 10).max measurable_const)
  exact (h1.inter h2).compl

/-- **The master inequality (abstract form), conditional on its hypotheses.**
`E` is a measurable retained-data event with `μ_C (Eᶜ) ≤ δ_ret`. For every retained value in `E`,
ASSUME (GP-W), (GP-A), (REPL) with `L_W = c_W/n`, `L_A = c_frame/n`, the replacement
`|√Q - √q̃| ≤ h_A`, and the sampling tail `μ_S {|√R - √q̃| > d_s} ≤ δ_s`. Then the probability
that the output `U = outRule a R` fails `p ≤ U ≤ max (10 p) (1/100)` is at most
`δ_ret + B_+ + B_- + δ_s`. -/
theorem master (μC : Measure ΩC) (μW : Measure ΩW) (μA : Measure ΩA) (μS : Measure ΩS)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS]
    {p : ΩC × (ΩW × ΩA) → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩC → ΩA → ℝ} (hPm : ∀ c, Measurable (P c)) (hP0 : ∀ c x, 0 ≤ P c x)
    (hP1 : ∀ c x, P c x ≤ 1)
    {R : ΩC × ΩS → ℝ} (hRm : Measurable R) (hR0 : ∀ x, 0 ≤ R x)
    {qt : ΩC → ℝ} {E : Set ΩC} (hE : MeasurableSet E)
    {n cW cf hW hA ds a τp τm δs δret : ℝ}
    (hn : 0 < n) (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 ≤ hW) (hhA : 0 ≤ hA) (hds : 0 ≤ ds)
    (ha : 1 < a) (hτp : 0 < τp) (hτm : τm < 0) (hδs : 0 ≤ δs)
    (hside1 : (hA + ds) + hW < √(1 / 100 / a)) (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW cW cf τp ≤ 0) (hEm : Eminus a (hA + ds) hW cW cf τm ≤ 0)
    (hret : μC.real Eᶜ ≤ δret)
    (GPW : ∀ c ∈ E, ∀ (ωA : ΩA) (s : ℝ),
      ∫ ωW, exp (s * p (c, (ωW, ωA))) ∂μW ≤
        exp (Tfun (cW / n) s * ∫ ωW, p (c, (ωW, ωA)) ∂μW))
    (GPA : ∀ c ∈ E, ∀ u : ℝ,
      ∫ ωA, exp (u * P c ωA) ∂μA ≤ exp (Tfun (cf / n) u * ∫ ωA, P c ωA ∂μA))
    (REPL : ∀ c ∈ E, ∀ ωA : ΩA, |√(∫ ωW, p (c, (ωW, ωA)) ∂μW) - √(P c ωA)| ≤ hW)
    (hQq : ∀ c ∈ E, |√(∫ ωA, P c ωA ∂μA) - √(qt c)| ≤ hA)
    (hsamp : ∀ c ∈ E, μS.real {σ | ds < |√(R (c, σ)) - √(qt c)|} ≤ δs) :
    (μC.prod ((μW.prod μA).prod μS)).real (failSet a p R) ≤
      δret + Bplus n a (hA + ds) hW cW cf τp + Bminus n a (hA + ds) hW cW cf τm + δs := by
  set B := Bplus n a (hA + ds) hW cW cf τp + Bminus n a (hA + ds) hW cW cf τm + δs with hB
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ Bplus n a (hA + ds) hW cW cf τp := (exp_pos _).le
    have h2 : 0 ≤ Bminus n a (hA + ds) hW cW cf τm := (exp_pos _).le
    linarith
  have hF := measurableSet_failSet (ΩW := ΩW) (ΩA := ΩA) a hpm hRm
  set ν := (μW.prod μA).prod μS with hν
  have hfib : ∀ c, ν (Prod.mk c ⁻¹' failSet a p R) ≤ Eᶜ.indicator 1 c + ENNReal.ofReal B := by
    intro c
    by_cases hc : c ∈ E
    · have hpc : Measurable fun ω : ΩW × ΩA => p (c, ω) := hpm.comp measurable_prodMk_left
      have h1 := fibre_fail μW μA μS (p := fun ω => p (c, ω)) (P := P c)
        (R := fun σ => R (c, σ)) hpc (fun x => hp0 _) (fun x => hp1 _) (hPm c) (hP0 c) (hP1 c)
        (fun σ => hR0 _) hn hcW hcf hhW hhA hds ha hτp hτm hside1 hside2 hEp hEm
        (GPW c hc) (GPA c hc) (REPL c hc) (hQq c hc) (hsamp c hc)
      have h2 : ν (Prod.mk c ⁻¹' failSet a p R) = ENNReal.ofReal (ν.real _) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
      rw [h2]
      exact le_add_left (ENNReal.ofReal_le_ofReal h1)
    · have h1 : Eᶜ.indicator (1 : ΩC → ENNReal) c = 1 := by
        rw [indicator_of_mem (by exact hc)]; rfl
      rw [h1]
      exact le_add_right prob_le_one
  have hmeas : (μC.prod ν) (failSet a p R) ≤ μC Eᶜ + ENNReal.ofReal B := by
    rw [Measure.prod_apply hF]
    calc ∫⁻ c, ν (Prod.mk c ⁻¹' failSet a p R) ∂μC
        ≤ ∫⁻ c, (Eᶜ.indicator 1 c + ENNReal.ofReal B) ∂μC := lintegral_mono hfib
      _ = μC Eᶜ + ENNReal.ofReal B := by
          rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hE.compl,
            lintegral_const, measure_univ, mul_one]
  have hreal : (μC.prod ν).real (failSet a p R) ≤ μC.real Eᶜ + B := by
    have h1 : (μC.prod ν).real (failSet a p R) ≤ (μC Eᶜ + ENNReal.ofReal B).toReal :=
      ENNReal.toReal_mono (by finiteness) hmeas
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hB0] at h1
    exact h1
  rw [hB] at hreal
  linarith

/-- **The master inequality in the form of the paper, conditional on its hypotheses.**
`H` is the retained hidden/frame event of the World network, `μ_C (Hᶜ) ≤ δ_hidden`. `Hbar` is
the retained radius with `E[1_H Hbar²] ≤ v_W`. `E₁` is a retained-data event (the intersection of
the events `E_j` of the paper) with `μ_C (H ∩ E₁ᶜ) ≤ δ_extra`. The hypotheses (GP-W), (GP-A),
(REPL), the replacement and the sampling tail are ASSUMED on `H ∩ {Hbar ≤ h_W} ∩ E₁`. Then the
failure probability is at most `δ_hidden + v_W/h_W² + δ_extra + B_+ + B_- + δ_s`. -/
theorem master_markov (μC : Measure ΩC) (μW : Measure ΩW) (μA : Measure ΩA) (μS : Measure ΩS)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS]
    {p : ΩC × (ΩW × ΩA) → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩC → ΩA → ℝ} (hPm : ∀ c, Measurable (P c)) (hP0 : ∀ c x, 0 ≤ P c x)
    (hP1 : ∀ c x, P c x ≤ 1)
    {R : ΩC × ΩS → ℝ} (hRm : Measurable R) (hR0 : ∀ x, 0 ≤ R x)
    {qt : ΩC → ℝ} {H E₁ : Set ΩC} (hH : MeasurableSet H) (hE₁ : MeasurableSet E₁)
    {Hbar : ΩC → ℝ} (hHm : Measurable Hbar)
    {n cW cf hW hA ds a τp τm δs δhid δextra vW : ℝ}
    (hn : 0 < n) (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 < hW) (hhA : 0 ≤ hA) (hds : 0 ≤ ds)
    (ha : 1 < a) (hτp : 0 < τp) (hτm : τm < 0) (hδs : 0 ≤ δs)
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
    (hsamp : ∀ c ∈ H ∩ {c | Hbar c ≤ hW} ∩ E₁,
      μS.real {σ | ds < |√(R (c, σ)) - √(qt c)|} ≤ δs) :
    (μC.prod ((μW.prod μA).prod μS)).real (failSet a p R) ≤
      δhid + vW / hW ^ 2 + δextra + Bplus n a (hA + ds) hW cW cf τp +
        Bminus n a (hA + ds) hW cW cf τm + δs := by
  have hEmeas : MeasurableSet (H ∩ {c | Hbar c ≤ hW} ∩ E₁) :=
    (hH.inter (measurableSet_le hHm measurable_const)).inter hE₁
  -- Markov on `H`
  have hmarkov : μC.real (H ∩ {c | hW < Hbar c}) ≤ vW / hW ^ 2 := by
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μC.restrict H)
      (f := fun c => Hbar c ^ 2) (Filter.Eventually.of_forall (fun c => sq_nonneg _)) hHint
      (hW ^ 2)
    have h2 : μC.real (H ∩ {c | hW < Hbar c}) ≤
        (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} := by
      have h3 : (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} =
          μC.real ({c | hW ^ 2 ≤ Hbar c ^ 2} ∩ H) := by
        simp only [Measure.real]
        rw [Measure.restrict_apply]
        exact measurableSet_le measurable_const (hHm.pow_const 2)
      rw [h3]
      refine measureReal_mono (fun c hc => ⟨?_, hc.1⟩)
      exact pow_le_pow_left₀ hhW.le (le_of_lt hc.2) 2
    rw [le_div_iff₀ (by positivity)]
    calc μC.real (H ∩ {c | hW < Hbar c}) * hW ^ 2
        ≤ (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} * hW ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = hW ^ 2 * (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} := mul_comm _ _
      _ ≤ ∫ c in H, Hbar c ^ 2 ∂μC := h1
      _ ≤ vW := hvW
  have hret : μC.real (H ∩ {c | Hbar c ≤ hW} ∩ E₁)ᶜ ≤ δhid + vW / hW ^ 2 + δextra := by
    have hsub : (H ∩ {c | Hbar c ≤ hW} ∩ E₁)ᶜ ⊆
        Hᶜ ∪ (H ∩ {c | hW < Hbar c}) ∪ (H ∩ E₁ᶜ) := by
      intro c hc
      by_cases h1 : c ∈ H
      · by_cases h2 : Hbar c ≤ hW
        · right
          exact ⟨h1, fun h3 => hc ⟨⟨h1, h2⟩, h3⟩⟩
        · left; right
          exact ⟨h1, not_le.1 h2⟩
      · left; left
        exact h1
    calc μC.real (H ∩ {c | Hbar c ≤ hW} ∩ E₁)ᶜ
        ≤ μC.real (Hᶜ ∪ (H ∩ {c | hW < Hbar c}) ∪ (H ∩ E₁ᶜ)) := measureReal_mono hsub
      _ ≤ μC.real Hᶜ + μC.real (H ∩ {c | hW < Hbar c}) + μC.real (H ∩ E₁ᶜ) :=
          (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
      _ ≤ δhid + vW / hW ^ 2 + δextra := by linarith
  exact master μC μW μA μS hpm hp0 hp1 hPm hP0 hP1 hRm hR0 hEmeas hn hcW hcf hhW.le hhA hds ha
    hτp hτm hδs hside1 hside2 hEp hEm hret GPW GPA REPL hQq hsamp

end master

end BstLean.Part156
