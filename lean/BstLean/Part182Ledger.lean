import BstLean.Part181Ledger

/-!
# Part 182 (file `Ledger`): the ledger for the Agent frame constant `1.82` at `n ≥ 22 000`

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1629`, `τ_- = −0.4322`; `E_+ ≤ −0.0003888762885`, `E_- ≤ −0.0003798397674`;
tails at `n = 22 000`: `B_+ + B_- ≤ 0.00043` (≈ `0.000427`). So the charges may use `0.009569`
(Part 181 at `c_f = 2.765`: `0.0069452`). This entry is used only by the CONDITIONAL frame of this
part (`frameA_TI_22000`, file `FrameTI`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_182 : Eplus aL (hAL + dsL) hWL cWL (182 / 100) (1629 / 10000) ≤
    -(777752577 / 2000000000000 : ℝ) := by
  have e : (1629 / 10000 : ℝ) * cWL = 2243133 / 10000000 := by unfold cWL; norm_num
  refine certP (eT := 625731520693 / 500000000000) (y := 2682255481 / 7812500000)
    (ehi := 352408008511 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_182 : Eminus aL (hAL + dsL) hWL cWL (182 / 100) (-(2161 / 5000)) ≤
    -(1899198837 / 5000000000000 : ℝ) := by
  have e : (-(2161 / 5000) : ℝ) * cWL = -(2975697 / 5000000) := by unfold cWL; norm_num
  have e2 : (-(568951508227 / 1000000000000) : ℝ) / 2 = -(568951508227 / 2000000000000) := by
    norm_num
  refine certM (eLo := 137871420851 / 250000000000) (eHi := 110297136681 / 200000000000)
    (y := -(568951508227 / 1000000000000)) (u := 752408598057 / 1000000000000)
    (ehi := 566118698431 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_182 : exp (-(((22000 : ℕ) : ℝ) * (777752577 / 2000000000000)) / 8) ≤
    ((585842148597 / 1000000000000) ^ 2 : ℝ) := by
  have e : -(((22000 : ℕ) : ℝ) * (777752577 / 2000000000000)) / 8 =
      2 * (-(8555278347 / 16000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_182 : exp (-(((22000 : ℕ) : ℝ) * (1899198837 / 5000000000000)) / 8) ≤
    ((118633354987 / 200000000000) ^ 2 : ℝ) := by
  have e : -(((22000 : ℕ) : ℝ) * (1899198837 / 5000000000000)) / 8 =
      2 * (-(20891187207 / 40000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `1.82`, every
`n ≥ 22 000`, with the charge budget `0.009569`**: IF the three charges have
`δ_hid + v_W/h_W² + δ_extra ≤ 0.009569`, and on the good set the World frame bound `1.377/n`, the
Agent frame bound `1.82/n` and the Agent replacement hold, THEN the program succeeds with
probability at least `99/100` (tails `≤ 0.00043`, `2e^{−100} ≤ 10⁻⁶`). -/
theorem classifier_frame_182 (hn : 22000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 9569 / 10 ^ 6)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (182 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 182 / 100)
    (by norm_num : (0 : ℝ) < 1629 / 10000) (by norm_num : (-(2161 / 5000) : ℝ) < 0) Ep_182 Em_182
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_182) (tail8 hnR (by norm_num) um_182)
    D t hEv hFW hFA hRA
  have hB : ((585842148597 / 1000000000000 : ℝ) ^ 2) ^ 8 +
      ((118633354987 / 200000000000 : ℝ) ^ 2) ^ 8 ≤ 43 / 10 ^ 5 := by norm_num
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
#print axioms classifier_frame_182
