import BstLean.Part181Ledger

/-!
# Part 186 (file `GLedC`): the ledger for the Agent frame constant `2.036` (TI-lite, `two-level core, conditional`) at
`n ≥ 16 384` (copy of Part 185 `FLed`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1528`, `τ_- = -0.4038`; tails at `n = 16 384`: `B_+ + B_- ≤ 0.005519`
(≈ `0.0055189`). So the charges may use `0.00448`.
-/

namespace BstLean.Part183.F16384

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_16384c : Eplus aL (hAL + dsL) hWL cWL (2036 / 1000) (191 / 1250) ≤
    -(182276537 / 500000000000 : ℝ) := by
  have e : (191 / 1250 : ℝ) * cWL = 263007 / 1250000 := by unfold cWL; norm_num
  refine certP (eT := 1234178541269 / 1000000000000) (y := 35767569459 / 100000000000)
    (ehi := 1430001787957 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_16384c : Eminus aL (hAL + dsL) hWL cWL (2036 / 1000) (-(2019 / 5000)) ≤
    -(221959661 / 625000000000 : ℝ) := by
  have e : (-(2019 / 5000) : ℝ) * cWL = -(2780163 / 5000000) := by unfold cWL; norm_num
  have e2 : (-3782900951 / 6250000000 : ℝ) / 2 = -3782900951 / 12500000000 := by
    norm_num
  refine certM (eLo := 57347978013 / 100000000000) (eHi := 573479780131 / 1000000000000)
    (y := -3782900951 / 6250000000) (u := 738870894643 / 1000000000000)
    (ehi := 545930198951 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le16384c {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_16384c : exp (-(((16384 : ℕ) : ℝ) * (182276537 / 500000000000)) / 8) ≤
    ((688457047917 / 1000000000000) ^ 2 : ℝ) := by
  have e : -(((16384 : ℕ) : ℝ) * (182276537 / 500000000000)) / 8 =
      2 * (-(182276537 / 488281250)) := by norm_num
  rw [e]
  refine exp_two_mul_le16384c ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_16384c : exp (-(((16384 : ℕ) : ℝ) * (221959661 / 625000000000)) / 8) ≤
    ((34756419781 / 50000000000) ^ 2 : ℝ) := by
  have e : -(((16384 : ℕ) : ℝ) * (221959661 / 625000000000)) / 8 =
      2 * (-(443919322 / 1220703125)) := by norm_num
  rw [e]
  refine exp_two_mul_le16384c ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.036`, every
`n ≥ 16 384`, with the charge budget `0.00448`** (tails `≤ 0.005519`). -/
theorem classifier_frame_16384c (hn : 16384 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 14 / 3125)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (2036 / 1000 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((16384 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 2036 / 1000)
    (by norm_num : (0 : ℝ) < 191 / 1250) (by norm_num : (-(2019 / 5000) : ℝ) < 0) Ep_16384c Em_16384c
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_16384c) (tail8 hnR (by norm_num) um_16384c)
    D t hEv hFW hFA hRA
  have hB : ((688457047917 / 1000000000000 : ℝ) ^ 2) ^ 8 +
      ((34756419781 / 50000000000 : ℝ) ^ 2) ^ 8 ≤ 5519 / 1000000 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183.F16384

open BstLean.Part183.F16384 in
#print axioms classifier_frame_16384c
