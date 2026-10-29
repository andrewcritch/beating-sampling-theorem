import BstLean.Part181Ledger

/-!
# Part 182 (file `Led21M`): the ledger for the Agent frame constant `2.09` (TI-lite, λ = 0.72) at `n ≥ 21 000`

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1505`, `τ_- = −0.397`; tails at `n = 21 000`: `B_+ + B_- ≤ 0.00119`
(≈ `0.001183`). So the charges may use `0.008809`. Used only by the CONDITIONAL junction at
`21 000` (`FREE21M_of_TI`, file `Comb21M`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_21M : Eplus aL (hAL + dsL) hWL cWL (209 / 100) (301 / 2000) ≤
    -(1794765483 / 5000000000000 : ℝ) := by
  have e : (301 / 2000 : ℝ) * cWL = 414477 / 2000000 := by unfold cWL; norm_num
  refine certP (eT := 1230275957609 / 1000000000000) (y := 14441737061 / 40000000000)
    (ehi := 1434825769023 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_21M : Eminus aL (hAL + dsL) hWL cWL (209 / 100) (-(397 / 1000)) ≤
    -(698834927 / 2000000000000 : ℝ) := by
  have e : (-(397 / 1000) : ℝ) * cWL = -(546669 / 1000000) := by unfold cWL; norm_num
  have e2 : (-(153364571007 / 250000000000) : ℝ) / 2 = -(153364571007 / 500000000000) := by
    norm_num
  refine certM (eLo := 289437417273 / 500000000000) (eHi := 578874834547 / 1000000000000)
    (y := -(153364571007 / 250000000000)) (u := 11497654449 / 15625000000)
    (ehi := 270737526433 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
    (by norm_num) (by norm_num) ?_
  · rw [e]
    refine le_exp_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · rw [e2]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma exp_two_mul_le21M {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_21M : exp (-(((21000 : ℕ) : ℝ) * (1794765483 / 5000000000000)) / 8) ≤
    ((9754671089 / 15625000000) ^ 2 : ℝ) := by
  have e : -(((21000 : ℕ) : ℝ) * (1794765483 / 5000000000000)) / 8 =
      2 * (-(37690075143 / 80000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le21M ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_21M : exp (-(((21000 : ℕ) : ℝ) * (698834927 / 2000000000000)) / 8) ≤
    ((158040368467 / 250000000000) ^ 2 : ℝ) := by
  have e : -(((21000 : ℕ) : ℝ) * (698834927 / 2000000000000)) / 8 =
      2 * (-(14675533467 / 32000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le21M ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.09`, every
`n ≥ 21 000`, with the charge budget `0.008809`**: IF the three charges have
`δ_hid + v_W/h_W² + δ_extra ≤ 0.008809`, and on the good set the World frame bound `1.377/n`, the
Agent frame bound `2.09/n` and the Agent replacement hold, THEN the program succeeds with
probability at least `99/100` (tails `≤ 0.00119`, `2e^{−100} ≤ 10⁻⁶`). -/
theorem classifier_frame_21M (hn : 21000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 8809 / 10 ^ 6)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (209 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((21000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 209 / 100)
    (by norm_num : (0 : ℝ) < 301 / 2000) (by norm_num : (-(397 / 1000) : ℝ) < 0) Ep_21M Em_21M
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_21M) (tail8 hnR (by norm_num) um_21M)
    D t hEv hFW hFA hRA
  have hB : ((9754671089 / 15625000000 : ℝ) ^ 2) ^ 8 +
      ((158040368467 / 250000000000 : ℝ) ^ 2) ^ 8 ≤ 119 / 10 ^ 5 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms classifier_frame_21M
