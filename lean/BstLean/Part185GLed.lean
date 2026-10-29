import BstLean.Part181Ledger

/-!
# Part 185 (file `GLed`): the ledger for the Agent frame constant `2.059` (TI-lite, `λ = 0.645, conditional`) at
`n ≥ 17 000` (copy of Part 185 `FLed`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1518`, `τ_- = -0.4009`; tails at `n = 17 000`: `B_+ + B_- ≤ 0.00461`
(≈ `0.0046095`). So the charges may use `0.005389`.
-/

namespace BstLean.Part183.F17

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_17 : Eplus aL (hAL + dsL) hWL cWL (2059 / 1000) (759 / 5000) ≤
    -(1810730501 / 5000000000000 : ℝ) := by
  have e : (759 / 5000 : ℝ) * cWL = 1045143 / 5000000 := by unfold cWL; norm_num
  refine certP (eT := 616240123481 / 500000000000) (y := 35909302051 / 100000000000)
    (ehi := 716015001769 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_17 : Eminus aL (hAL + dsL) hWL cWL (2059 / 1000) (-(4009 / 10000)) ≤
    -(3526789839 / 10000000000000 : ℝ) := by
  have e : (-(4009 / 10000) : ℝ) * cWL = -(5520393 / 10000000) := by unfold cWL; norm_num
  have e2 : (-30440427123 / 50000000000 : ℝ) / 2 = -30440427123 / 100000000000 := by
    norm_num
  refine certM (eLo := 57577443551 / 100000000000) (eHi := 575774435511 / 1000000000000)
    (y := -30440427123 / 50000000000) (u := 737562630819 / 1000000000000)
    (ehi := 543998634381 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le17 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_17 : exp (-(((17000 : ℕ) : ℝ) * (1810730501 / 5000000000000)) / 8) ≤
    ((17015004857 / 25000000000) ^ 2 : ℝ) := by
  have e : -(((17000 : ℕ) : ℝ) * (1810730501 / 5000000000000)) / 8 =
      2 * (-(30782418517 / 80000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le17 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_17 : exp (-(((17000 : ℕ) : ℝ) * (3526789839 / 10000000000000)) / 8) ≤
    ((2148377407 / 3125000000) ^ 2 : ℝ) := by
  have e : -(((17000 : ℕ) : ℝ) * (3526789839 / 10000000000000)) / 8 =
      2 * (-(59955427263 / 160000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le17 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.059`, every
`n ≥ 17 000`, with the charge budget `0.005389`** (tails `≤ 0.00461`). -/
theorem classifier_frame_17 (hn : 17000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 5389 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (2059 / 1000 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((17000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 2059 / 1000)
    (by norm_num : (0 : ℝ) < 759 / 5000) (by norm_num : (-(4009 / 10000) : ℝ) < 0) Ep_17 Em_17
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_17) (tail8 hnR (by norm_num) um_17)
    D t hEv hFW hFA hRA
  have hB : ((17015004857 / 25000000000 : ℝ) ^ 2) ^ 8 +
      ((2148377407 / 3125000000 : ℝ) ^ 2) ^ 8 ≤ 461 / 100000 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183.F17

open BstLean.Part183.F17 in
#print axioms classifier_frame_17
