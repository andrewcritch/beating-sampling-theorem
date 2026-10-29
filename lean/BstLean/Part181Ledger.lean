import BstLean.Part160Ledger2Gen

/-!
# Part 181 (file `Ledger`): the ledger for the Agent frame constant `2.765` at `n ≥ 22 000`

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1265`, `τ_- = -0.32825`; `E_+ ≤ −0.0003013649`, `E_- ≤ −0.0002902185`;
tails at `n = 22 000`: `u_+⁸ + u_-⁸ ≤ 0.0030538` (≈ `0.0030071`). The charges may use
`0.0069452` (Part 160's entries: `0.0063` with tails `0.003699`).
-/

namespace BstLean.Part181

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_2765 : Eplus aL (hAL + dsL) hWL cWL (2765 / 1000) (253 / 2000) ≤ -(3013649 / 10000000000 : ℝ) := by
  have e : (253 / 2000 : ℝ) * cWL = 348381 / 2000000 := by unfold cWL; norm_num
  refine certP (eT := 1190282293001 / 1000000000000) (y := 19734589 / 50000000) (ehi := 1483926744527 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_2765 : Eminus aL (hAL + dsL) hWL cWL (2765 / 1000) (-(1313 / 4000)) ≤ -(580437 / 2000000000 : ℝ) := by
  have e : (-(1313 / 4000) : ℝ) * cWL = -(1808001 / 4000000) := by unfold cWL; norm_num
  have e2 : (-(35040597 / 50000000) : ℝ) / 2 = -(35040597 / 100000000) := by norm_num
  refine certM (eLo := 159088502659 / 250000000000) (eHi := 636354010637 / 1000000000000) (y := -(35040597 / 50000000)) (u := 352201032779 / 500000000000)
    (ehi := 496182269963 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
    (by norm_num) ?_
  · rw [e]
    refine le_exp_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · rw [e2]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma up_2765 : exp (-(((22000 : ℕ) : ℝ) * (3013649 / 10000000000)) / 8) ≤ (1091482929 / 2500000000 : ℝ) := by
  have e : -(((22000 : ℕ) : ℝ) * (3013649 / 10000000000)) / 8 = -(33150139 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_2765 : exp (-(((22000 : ℕ) : ℝ) * (580437 / 2000000000)) / 8) ≤ (1125457767 / 2500000000 : ℝ) := by
  have e : -(((22000 : ℕ) : ℝ) * (580437 / 2000000000)) / 8 = -(6384807 / 8000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.765`, every
`n ≥ 22 000`, with the charge budget `0.0069452`**: IF the three charges have
`δ_hid + v_W/h_W² + δ_extra ≤ 0.0069452`, and on the good set the World frame bound `1.377/n`, the
Agent frame bound `2.765/n` and the Agent replacement hold, THEN the program succeeds with
probability at least `99/100` (tails `≤ 0.0030538`, `2e^{−100} ≤ 10⁻⁶`). -/
theorem classifier_frame_2765 (hn : 22000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 69452 / 10 ^ 7)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (2765 / 1000 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 2765 / 1000)
    (by norm_num : (0 : ℝ) < 253 / 2000) (by norm_num : (-(1313 / 4000) : ℝ) < 0) Ep_2765 Em_2765
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_2765) (tail8 hnR (by norm_num) um_2765)
    D t hEv hFW hFA hRA
  have hB : (1091482929 / 2500000000 : ℝ) ^ 8 + (1125457767 / 2500000000 : ℝ) ^ 8 ≤ 30538 / 10 ^ 7 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part181

open BstLean.Part181 in
#print axioms classifier_frame_2765
