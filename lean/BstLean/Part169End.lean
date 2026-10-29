import BstLean.Part169Pass

/-!
# Part 169 (file `End`): the end theorem with the paper's tables

No proof is left open; no `native_decide` or `axiom` is used.

* `dP c`: the split data of the end theorem (Part 162's `dPaper` with the constants of Part 166)
  for the design `paperDesignP n`.
* `BIASP c`: `BIAS_hyp` at `h_b = 0.004295` for the paper's program (the tables are the
  conditional passes `passF`, `passW`).
* **`classifier_paper_pass80k`**: `classifier_paper_LG80k` with `fT = passF`, `wT = passW`.
  The remaining hypotheses are `BIASP` on `goodD` and the charge of the caller's `E_A`.
* **`classifier_paper_bias80k`**: the same with `E_A = E_A' ∩ E_bias`: the caller supplies a
  measurable bias event `E_bias` with charge `δ_bias`, the charge of `E_A'`, and
  `δ_A' + δ_bias ≤ roomE`; `BIASP` is asked only on `goodD n D (E_A' ∩ E_bias)`. This is the
  form that p168 §6.3 asks for.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (BIAS_hyp)
open BstLean.Part162 (dPaper)
open BstLean.Part166 (goodD)

variable {n : ℕ}

/-- The split data of the end theorem for the paper's program. -/
noncomputable def dP (c : Ret n) : BstLean.Part161.SplitData n :=
  dPaper (paperDesignP n) c (22 * √(2 / (n : ℝ)) ^ 2)
    (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
    (1 / 10000) (by norm_num) (by norm_num)

/-- **The bias hypothesis for the paper's program**: `√(E_kept H²(Q̄_a, Q̃_a)) ≤ 0.004295`, with
`Q̃_a` built from the conditional passes `passF`, `passW`. -/
def BIASP (c : Ret n) : Prop := BIAS_hyp (paperDesignP n) c (dP c) (4295 / 10 ^ 6)

/-- **The classifier theorem for the paper's program with its tables** (every `n ≥ 80 000`). -/
theorem classifier_paper_pass80k (hn : 80000 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part167.roomE)
    (hB : ∀ c ∈ goodD n (paperDesignP n) EA, BIASP c) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part168.classifier_paper_LG80k hn passF passW measurable_passF measurable_passW t hEA
    hA hroom hB

/-- **The classifier theorem with a separate bias event** (every `n ≥ 80 000`). -/
theorem classifier_paper_bias80k (hn : 80000 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ BstLean.Part167.roomE)
    (hB : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), BIASP c) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  set X := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  have hsub : X ∩ (EA ∩ Eb)ᶜ ⊆ (X ∩ EAᶜ) ∪ Ebᶜ := by
    intro x hx
    rcases hx with ⟨hX, hn'⟩
    by_cases h : x ∈ EA
    · right; exact fun hb' => hn' ⟨h, hb'⟩
    · left; exact ⟨hX, h⟩
  have hle : (retDist (paperCentres n)).real (X ∩ (EA ∩ Eb)ᶜ) ≤ δA + δb :=
    (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hA hb))
  exact classifier_paper_pass80k hn t (hEA.inter hEb) hle hroom hB

end BstLean.Part169
