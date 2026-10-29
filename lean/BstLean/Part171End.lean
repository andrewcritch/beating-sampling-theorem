import BstLean.Part171Num

/-!
# Part 171 (file `End`): the end theorem with the bias moments proved

No proof is left open; no `native_decide` or `axiom` is used.

* **`biasMomF_stat`**, **`biasMomW_stat`**: `BiasMomF (O₁) Gb 0.004` and `BiasMomW (O₁) Gb 0.02`
  for every `Gb ⊆ StatEvN n` and every `n ≥ 80 000`.
* **`classifier_paper_stat80k`**: the classifier theorem (success probability `≥ 99/100` for the
  paper's program `paperDesignP`, every `n ≥ 80 000`). Remaining hypotheses: a measurable
  first-layer event family `Gb` inside the statistics event `StatEvN n`, with charge `≤ 0.0006`
  in the World window.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW)
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- **The statistics event at the thresholds**: at every node `g < J_s`,
`1/(5n) ≤ ς² ≤ 5/n`, `DstN ≤ 16/n³`, `hUN ≤ 16/n³`, `V2N ≤ 64/n⁴`, `piN ≤ 1/n⁴`. -/
def StatEvN (n : ℕ) : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ) :=
  StatEv n (SminN n) (SmaxN n) (DmN n) (DmN n) (VmN n) (PmN n)

lemma SminN_pos (hn : 1 ≤ n) : 0 < SminN n := by
  unfold SminN; have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  positivity

lemma O1n_nonneg (n : ℕ) : 0 ≤ O1n n := by unfold O1n; positivity

/-- **The location bias moments** on every `Gb ⊆ StatEvN n` (`B_f = 0.004`). -/
theorem biasMomF_stat (hn : 80000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEvN n) : BiasMomF (O1n n) Gb (4 / 1000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numF hn
  exact biasMomF_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hGb (by norm_num) (by norm_num)
    z1_pow z2_pow h0 h1 h2 h3

/-- **The energy bias moments** on every `Gb ⊆ StatEvN n` (`B_ω = 0.02`). -/
theorem biasMomW_stat (hn : 80000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEvN n) : BiasMomW (O1n n) Gb (2 / 100) := by
  obtain ⟨h0, h1, h2, h3⟩ := numW hn
  exact biasMomW_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hGb (by norm_num) (by norm_num)
    z1_pow z2_pow h0 h1 h2 h3

/-- **The classifier theorem with the bias moments proved** (every `n ≥ 80 000`). Remaining
hypotheses: a measurable first-layer event family `Gb ⊆ StatEvN n` with charge `≤ 0.0006` in the
World window. -/
theorem classifier_paper_stat80k (hn : 80000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb)
    (hsub : Gb ⊆ StatEvN n)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ 6 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part170.classifier_paper_bias_num80k hn t hGb hδG (biasMomF_stat hn hsub)
    (biasMomW_stat hn hsub)

end BstLean.Part171
