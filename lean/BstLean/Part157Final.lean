import BstLean.Part157Prog

/-!
# Part 157, item 3: the conditional classifier theorem for the ACTUAL networks

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p157-spec.md`, item 3. Paper: `proofs/option-n/theorem7-00-main.tex`
(Theorem 7), with the parts `theorem7-02-world.tex`, `theorem7-03-composition.tex`,
`theorem7-09-assembly.tex`.

The headline `classifier_networks_conditional` is a statement about the three random ReLU MLPs of
`MM.md` (`mlpTriple 2 n`, Part 130) and the target `pTarget` (Part 157, item 1). It is
CONDITIONAL: the five named hypotheses below are NOT proved in Lean.

* `GPW_hyp`: the bound of the moment generating function over the residual matrix of `W₃`.
* `GPA_hyp`: the same over the residual matrix of `A₃`, for the stand-in probability.
* `REPL_W_hyp`: the World root replacement.
* `REPL_A_hyp`: the Agent root replacement.
* `EVENTS_hyp`: the retained-data events with the charges of the ledger.

What IS proved here: the product structure (the regression, `triple_disint`), every measurability
item, the independence and the mean of the program's draws, and the derivation of the conclusion
from the five hypotheses through `BstLean.Part156.classifier_conditional_ge_16384`.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156

variable {n : ℕ}

/-! ## The named hypotheses -/

/-- **(GP-W), the moment generating function bound over the residual of `W₃`.** For every
retained value `c` in `E`, every residual matrix `ω_A` of `A₃` and every real `s`:
`E_{ω_W} exp(s·p) ≤ exp(((e^{s L_W} − 1)/L_W)·E_{ω_W} p)`, where `p` is the target of the triple
with retained data `c` and residual matrices `(ω_W, ω_A)`, and `ω_W` is a Gaussian matrix with
entry variance `2/m_W`.

Paper statement that proves it: `theorem7-02-world.tex`, formula `t7:p02:World-MGF` (from
Lemma `t7:p02:GP`, Corollary `t7:p02:MGF`, Lemma `t7:p02:regression` and the World frame
Input `t7:p02:input-frame`, with `L_W = c_W/n`), then the second inequality of Lemma `t7:p03:gp`
(in Lean: `BstLean.Part156.gp_of_primitive`). -/
def GPW_hyp (D : Centres n) (t LW : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, ∀ (ωA : ResA n) (s : ℝ),
    ∫ ωW, exp (s * pRes D t c (ωW, ωA)) ∂resW n ≤
      exp (Tfun LW s * ∫ ωW, pRes D t c (ωW, ωA) ∂resW n)

/-- **(GP-A), the moment generating function bound over the residual of `A₃`.** For every
retained value `c` in `E` and every real `u`:
`E_{ω_A} exp(u·P) ≤ exp(((e^{u L_A} − 1)/L_A)·E_{ω_A} P)`, where `P = PStand D t c ω_A` is the
stand-in probability and `ω_A` is a Gaussian matrix with entry variance `2/m_A`.

Paper statement that proves it: `theorem7-03-composition.tex`, Lemma `t7:p03:gp` applied to the
Agent representation of Lemma `t7:p03:regression`, with the frame bound `L_A = c_frame/n` of
`theorem7-09-assembly.tex`, Lemma `t7:p09:frame-junction`, formula `t7:p09:frame` (Parts 04 to
06). -/
def GPA_hyp (D : Design n) (t LA : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, ∀ u : ℝ,
    ∫ ωA, exp (u * PStand D t c ωA) ∂resA n ≤
      exp (Tfun LA u * ∫ ωA, PStand D t c ωA ∂resA n)

/-- **(REPL-W), the World root replacement.** For every retained value `c` in `E` and every
residual matrix `ω_A`: `|√(E_{ω_W} p) − √P| ≤ h_W`, with `p` the target and
`P = PStand D t c ω_A` the stand-in probability.

Paper statement that proves it: `theorem7-02-world.tex`, Lemma `t7:p02:replacement`
(`|√q_W − √q'_W| ≤ h_W` on `K_W(h_W)`), with the identity `E_{G_W} p = q_W` (Fubini and
Lemma `t7:p02:regression`). -/
def REPL_W_hyp (D : Design n) (t hW : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, ∀ ωA : ResA n,
    |√(∫ ωW, pRes D.toCentres t c (ωW, ωA) ∂resW n) - √(PStand D t c ωA)| ≤ hW

/-- **(REPL-A), the Agent root replacement.** For every retained value `c` in `E`:
`|√Q − √q̃| ≤ h_A`, `Q = E_{ω_A} P` and `q̃ = qTilde D t c` the mean of one draw of the program.

Paper statement that proves it: `theorem7-09-assembly.tex`, Lemma `t7:p09:bias-junction`,
formula `t7:p09:root` (Parts 04 to 08: Propositions `t7:p07:LG`, `t7:p07:FL`, `t7:p08:upper`). -/
def REPL_A_hyp (D : Design n) (t hA : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, |√(∫ ωA, PStand D t c ωA ∂resA n) - √(qTilde D t c)| ≤ hA

/-- **(EVENTS), the retained-data events with their charges.** `H` (the hidden World event),
`E₁` (the intersection of the other retained-data events) are measurable sets of retained data,
`Hbar` (the World replacement radius) is a measurable function of the retained data, and under
the distribution `retDist D` of the retained data of the three random networks:
`Pr(Hᶜ) ≤ δ_hid`, `E[1_H Hbar²] ≤ v_W`, `Pr(H ∩ E₁ᶜ) ≤ δ_extra`.

Paper statements that prove it: `theorem7-02-world.tex`, Input `t7:p02:input-hidden` (charge
`a_E(n)`) and Lemma `t7:p02:moment` (`v_W(n)`); `theorem7-09-assembly.tex`, the ledger
`t7:p09:ledger` and formula `t7:p09:retained` (`δ_ret(n)`). -/
def EVENTS_hyp (D : Centres n) (H E₁ : Set (Ret n)) (Hbar : Ret n → ℝ) (δhid vW δextra : ℝ) :
    Prop :=
  MeasurableSet H ∧ MeasurableSet E₁ ∧ Measurable Hbar ∧
    (retDist D).real Hᶜ ≤ δhid ∧
    IntegrableOn (fun c => Hbar c ^ 2) H (retDist D) ∧
    ∫ c in H, Hbar c ^ 2 ∂retDist D ≤ vW ∧
    (retDist D).real (H ∩ E₁ᶜ) ≤ δextra

/-- The common retained-data event: `H ∩ {Hbar ≤ h_W} ∩ E₁`. -/
def goodSet (H E₁ : Set (Ret n)) (Hbar : Ret n → ℝ) (hW : ℝ) : Set (Ret n) :=
  H ∩ {c | Hbar c ≤ hW} ∩ E₁

/-! ## The output of the program and the failure event -/

/-- **The output of the program**: `U = min 1 (max (1/100) (a·R))`, `R` the fraction of hits in
the `k` draws; a function of the retained data `ret D θ` and of the draws `σ`. -/
noncomputable def progOut (D : Design n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) : ℝ :=
  outRule a (hitFrac (hits D t k) (ret D.toCentres θ, σ))

/-- The failure event of the program for the actual networks. -/
def failNet (D : Design n) (t a : ℝ) (k : ℕ) : Set (Net3 n × (Fin k → DrawSp n)) :=
  {x | ¬ successNet x.1 t (progOut D t a k x.1 x.2)}

lemma measurable_hitFrac (D : Design n) (t : ℝ) (k : ℕ) : Measurable (hitFrac (hits D t k)) := by
  unfold hitFrac
  exact (Finset.measurable_sum _ (fun i _ => measurable_hits D t k i)).div_const _

lemma measurableSet_failNet (D : Design n) (t a : ℝ) (k : ℕ) :
    MeasurableSet (failNet D t a k) := by
  have hp : Measurable (fun x : Net3 n × (Fin k → DrawSp n) => pTargetT x.1 t) :=
    (measurable_pTargetT t).comp measurable_fst
  have hU : Measurable (fun x : Net3 n × (Fin k → DrawSp n) => progOut D t a k x.1 x.2) :=
    measurable_outRule a ((measurable_hitFrac D t k).comp
      (((measurable_ret D.toCentres).comp measurable_fst).prodMk measurable_snd))
  exact (measurableSet_success hp hU).compl

/-! ## The transfer to the product space of Part 156 -/

/-- **The failure probability for the actual networks is the failure probability on the product
space** `noise × ((residual of W₃ × residual of A₃) × draws)`. -/
theorem failNet_eq (D : Design n) (t a : ℝ) (k : ℕ) :
    ((mlpTriple 2 n).prod (sampMeas k n)).real (failNet D t a k) =
      ((noiseC n).prod (((resW n).prod (resA n)).prod (sampMeas k n))).real
        (failSet a (fun x : Ret n × (ResW n × ResA n) =>
            pRes D.toCentres t (retVal D.toCentres x.1) x.2)
          (hitFrac (fun i (x : Ret n × (Fin k → DrawSp n)) =>
            hits D t k i (retVal D.toCentres x.1, x.2)))) := by
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  -- the set in the space (retained data × triple) × draws
  set S' : Set ((Ret n × Net3 n) × (Fin k → DrawSp n)) :=
    {y | ¬ success (pTargetT y.1.2 t) (outRule a (hitFrac (hits D t k) (y.1.1, y.2)))} with hS'
  have mS' : MeasurableSet S' := by
    have hp : Measurable (fun y : (Ret n × Net3 n) × (Fin k → DrawSp n) => pTargetT y.1.2 t) :=
      (measurable_pTargetT t).comp (measurable_snd.comp measurable_fst)
    have hU : Measurable (fun y : (Ret n × Net3 n) × (Fin k → DrawSp n) =>
        outRule a (hitFrac (hits D t k) (y.1.1, y.2))) :=
      measurable_outRule a ((measurable_hitFrac D t k).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    exact (measurableSet_success hp hU).compl
  have mL : Measurable (fun θ : Net3 n => (ret D.toCentres θ, θ)) :=
    (measurable_ret D.toCentres).prodMk measurable_id
  have mΦ : Measurable (fun x : Ret n × (ResW n × ResA n) =>
      (retVal D.toCentres x.1, rebuild D.toCentres (retVal D.toCentres x.1) x.2)) :=
    ((measurable_retVal D.toCentres).comp measurable_fst).prodMk
      ((measurable_rebuild D.toCentres).comp
        (((measurable_retVal D.toCentres).comp measurable_fst).prodMk measurable_snd))
  -- left side
  have e1 : failNet D t a k =
      (Prod.map (fun θ : Net3 n => (ret D.toCentres θ, θ)) (id : (Fin k → DrawSp n) → _)) ⁻¹' S' :=
    rfl
  have e2 : ((mlpTriple 2 n).prod (sampMeas k n)).map
        (Prod.map (fun θ : Net3 n => (ret D.toCentres θ, θ)) (id : (Fin k → DrawSp n) → _)) =
      (((noiseC n).prod ((resW n).prod (resA n))).prod (sampMeas k n)).map
        (Prod.map (fun x : Ret n × (ResW n × ResA n) =>
          (retVal D.toCentres x.1, rebuild D.toCentres (retVal D.toCentres x.1) x.2))
          (id : (Fin k → DrawSp n) → _)) := by
    rw [← Measure.map_prod_map _ _ mL measurable_id, ← Measure.map_prod_map _ _ mΦ measurable_id,
      triple_disint D.toCentres]
  have e3 : ((noiseC n).prod ((resW n).prod (resA n))).prod (sampMeas k n) =
      ((noiseC n).prod (((resW n).prod (resA n)).prod (sampMeas k n))).map
        (MeasurableEquiv.prodAssoc :
          (Ret n × (ResW n × ResA n)) × (Fin k → DrawSp n) ≃ᵐ _).symm := by
    rw [← Measure.prodAssoc_prod (μ := noiseC n) (ν := (resW n).prod (resA n))
      (τ := sampMeas k n), MeasurableEquiv.map_symm_map]
  rw [e1, ← map_measureReal_apply (mL.prodMap measurable_id) mS', e2,
    map_measureReal_apply (mΦ.prodMap measurable_id) mS', e3,
    map_measureReal_apply MeasurableEquiv.prodAssoc.symm.measurable
      ((mΦ.prodMap measurable_id) mS')]
  rfl

/-! ## The conditional theorem -/

/-- **The conditional classifier theorem for the actual networks, failure bound, every
`n ≥ 16 384`.** `W`, `A`, `F` are the three independent random ReLU MLPs of `MM.md` at `r = 2`
(`mlpTriple 2 n`), `p = pTarget W A F t`, and the program draws `10¹²` times (`sampMeas`),
with output `U = min 1 (max (1/100) (2.2524763228·R))`. `D` is any design (centres, `τ₀`,
mixture table), measurable in the retained data. IF there are retained-data events `H`, `E₁` and
a radius `Hbar` with the charges of the ledger (`EVENTS_hyp`), and on
`H ∩ {Hbar ≤ h_W} ∩ E₁` the hypotheses (GP-W) with `L_W = 1.377/n`, (GP-A) with
`L_A = 1.743/n`, (REPL-W) with `h_W = 0.0024160420` and (REPL-A) with
`h_A = 0.006583 + 10⁻²⁰` hold, THEN the program fails `p ≤ U ≤ max (10 p) (1/100)` with
probability less than `0.008195686`, jointly over the networks and the draws. -/
theorem classifier_networks_conditional_ge (hn : 16384 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhidL vWL δextraL)
    (hGPW : GPW_hyp D.toCentres t (cWL / n) (goodSet H E₁ Hbar hWL))
    (hGPA : GPA_hyp D t (cfL / n) (goodSet H E₁ Hbar hWL))
    (hRW : REPL_W_hyp D t hWL (goodSet H E₁ Hbar hWL))
    (hRA : REPL_A_hyp D t hAL (goodSet H E₁ Hbar hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real (failNet D t aL (10 ^ 12)) <
      8195686 / 10 ^ 9 := by
  obtain ⟨hH, hE₁, hHm, hhid, hHint, hvW, hextra⟩ := hEv
  have hn1 : 1 ≤ n := by omega
  have mr := measurable_retVal D.toCentres
  have hmap := noise_retVal D.toCentres
  have hn' : (16384 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have mpair : Measurable (fun x : Ret n × (ResW n × ResA n) => (retVal D.toCentres x.1, x.2)) :=
    (mr.comp measurable_fst).prodMk measurable_snd
  have hpm : Measurable (fun x : Ret n × (ResW n × ResA n) =>
      pRes D.toCentres t (retVal D.toCentres x.1) x.2) := by
    have h := (measurable_pRes D.toCentres t).comp mpair
    exact h
  have hp0 : ∀ x : Ret n × (ResW n × ResA n),
      0 ≤ pRes D.toCentres t (retVal D.toCentres x.1) x.2 := fun x => pRes_nonneg _ _ _ _
  have hp1 : ∀ x : Ret n × (ResW n × ResA n),
      pRes D.toCentres t (retVal D.toCentres x.1) x.2 ≤ 1 := fun x => pRes_le_one hn1 _ _ _ _
  have hPm : ∀ c : Ret n, Measurable (PStand D t (retVal D.toCentres c)) :=
    fun c => measurable_PStand D t _
  have hP0 : ∀ (c : Ret n) (x : ResA n), 0 ≤ PStand D t (retVal D.toCentres c) x :=
    fun c x => PStand_nonneg _ _ _ _
  have hP1 : ∀ (c : Ret n) (x : ResA n), PStand D t (retVal D.toCentres c) x ≤ 1 :=
    fun c x => PStand_le_one _ _ _ _
  have hXm : ∀ i : Fin (10 ^ 12), Measurable (fun x : Ret n × (Fin (10 ^ 12) → DrawSp n) =>
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2)) := by
    intro i
    have h1 : Measurable (fun x : Ret n × (Fin (10 ^ 12) → DrawSp n) =>
        (retVal D.toCentres x.1, x.2)) := (mr.comp measurable_fst).prodMk measurable_snd
    have h2 := (measurable_hits D t (10 ^ 12) i).comp h1
    exact h2
  have hX01 : ∀ (i : Fin (10 ^ 12)) (x : Ret n × (Fin (10 ^ 12) → DrawSp n)),
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2) = 0 ∨
        hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2) = 1 :=
    fun i x => hits_01 D t (10 ^ 12) i _
  have hH' : MeasurableSet (retVal D.toCentres ⁻¹' H) := mr hH
  have hE₁' : MeasurableSet (retVal D.toCentres ⁻¹' E₁) := mr hE₁
  have hHm' : Measurable (fun c => Hbar (retVal D.toCentres c)) := hHm.comp mr
  have hhid' : (noiseC n).real (retVal D.toCentres ⁻¹' H)ᶜ ≤ δhidL := by
    have e : (retVal D.toCentres ⁻¹' H)ᶜ = retVal D.toCentres ⁻¹' Hᶜ := rfl
    rw [e, ← map_measureReal_apply mr hH.compl, hmap]
    exact hhid
  have hHint' : IntegrableOn (fun c => Hbar (retVal D.toCentres c) ^ 2)
      (retVal D.toCentres ⁻¹' H) (noiseC n) := by
    have h1 : Integrable (fun c => Hbar c ^ 2) ((retDist D.toCentres).restrict H) := hHint
    rw [← hmap, Measure.restrict_map mr hH] at h1
    exact (integrable_map_measure ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable).1 h1
  have hvW' : ∫ c in retVal D.toCentres ⁻¹' H, Hbar (retVal D.toCentres c) ^ 2 ∂noiseC n ≤ vWL := by
    have h1 := setIntegral_map (μ := noiseC n) hH
      (f := fun c => Hbar c ^ 2) (g := retVal D.toCentres)
      ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable
    rw [hmap] at h1
    rw [← h1]
    exact hvW
  have hextra' : (noiseC n).real (retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ) ≤
      δextraL := by
    have e : retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ =
        retVal D.toCentres ⁻¹' (H ∩ E₁ᶜ) := rfl
    rw [e, ← map_measureReal_apply mr (hH.inter hE₁.compl), hmap]
    exact hextra
  have key := classifier_conditional_ge_16384 (n := (n : ℝ)) hn'
    (noiseC n) (resW n) (resA n) (sampMeas (10 ^ 12) n)
    (p := fun x : Ret n × (ResW n × ResA n) => pRes D.toCentres t (retVal D.toCentres x.1) x.2)
    hpm hp0 hp1
    (P := fun c => PStand D t (retVal D.toCentres c)) hPm hP0 hP1
    (X := fun i (x : Ret n × (Fin (10 ^ 12) → DrawSp n)) =>
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2)) hXm hX01
    (qt := fun c => qTilde D t (retVal D.toCentres c))
    (H := retVal D.toCentres ⁻¹' H) (E₁ := retVal D.toCentres ⁻¹' E₁) hH' hE₁'
    (Hbar := fun c => Hbar (retVal D.toCentres c)) hHm' hhid' hHint' hvW' hextra'
    (fun c hc ωA s => hGPW (retVal D.toCentres c) hc ωA s)
    (fun c hc u => hGPA (retVal D.toCentres c) hc u)
    (fun c hc ωA => hRW (retVal D.toCentres c) hc ωA)
    (fun c hc => hRA (retVal D.toCentres c) hc)
    (fun c _ => hits_indep D t (10 ^ 12) (retVal D.toCentres c))
    (fun c _ i => hits_mean D t (10 ^ 12) (retVal D.toCentres c) i)
  rw [failNet_eq]
  exact key

/-- **The conditional classifier theorem for the actual networks, success form, every
`n ≥ 16 384`**: under the five named hypotheses the program succeeds with probability at least
`99/100`. -/
theorem classifier_networks_conditional_ge_success (hn : 16384 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhidL vWL δextraL)
    (hGPW : GPW_hyp D.toCentres t (cWL / n) (goodSet H E₁ Hbar hWL))
    (hGPA : GPA_hyp D t (cfL / n) (goodSet H E₁ Hbar hWL))
    (hRW : REPL_W_hyp D t hWL (goodSet H E₁ Hbar hWL))
    (hRA : REPL_A_hyp D t hAL (goodSet H E₁ Hbar hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have h := classifier_networks_conditional_ge hn D t hEv hGPW hGPA hRW hRA
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  linarith

/-- **`classifier_networks_conditional`: the conditional classifier theorem for the actual
networks at `n = 16 384`.** For the three random ReLU MLPs of `MM.md` at `n = 16 384`, `r = 2`
(widths `m_W = ⌈n^{7/2}⌉`, `m_A = n²`, `m_F = ⌈n^{3/2}⌉`), every threshold `t` and every design `D`:
IF `EVENTS_hyp`, `GPW_hyp` (constant `c_W/n`, `c_W = 1.377`), `GPA_hyp` (constant `c_frame/n`,
`c_frame = 1.743`), `REPL_W_hyp` (`h_W = 0.0024160420`) and `REPL_A_hyp`
(`h_A = 0.006583 + 10⁻²⁰`) hold, THEN
`Pr(p ≤ U ≤ max (10 p) (1/100)) ≥ 99/100`, with `p = pTarget W A F t` and
`U = min 1 (max (1/100) (2.2524763228·R))`, `R` the fraction of hits in `10¹²` independent draws
of the sampling program. The probability is joint over the networks and the draws. -/
theorem classifier_networks_conditional (D : Design 16384) (t : ℝ)
    {H E₁ : Set (Ret 16384)} {Hbar : Ret 16384 → ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhidL vWL δextraL)
    (hGPW : GPW_hyp D.toCentres t (cWL / 16384) (goodSet H E₁ Hbar hWL))
    (hGPA : GPA_hyp D t (cfL / 16384) (goodSet H E₁ Hbar hWL))
    (hRW : REPL_W_hyp D t hWL (goodSet H E₁ Hbar hWL))
    (hRA : REPL_A_hyp D t hAL (goodSet H E₁ Hbar hWL)) :
    99 / 100 ≤ ((mlpTriple 2 16384).prod (sampMeas (10 ^ 12) 16384)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have e : ((16384 : ℕ) : ℝ) = 16384 := by norm_num
  exact classifier_networks_conditional_ge_success (n := 16384) le_rfl D t hEv
    (by rw [e]; exact hGPW) (by rw [e]; exact hGPA) hRW hRA

end BstLean.Part157

open BstLean.Part157 in
#print axioms failNet_eq
open BstLean.Part157 in
#print axioms classifier_networks_conditional_ge
open BstLean.Part157 in
#print axioms classifier_networks_conditional_ge_success
open BstLean.Part157 in
#print axioms classifier_networks_conditional
