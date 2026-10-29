import BstLean.Part181Ledger

/-!
# Part 183 (file `FLed`): the ledger for the Agent frame constant `2.135` (TI-lite, `λ = 0.73`) at
`n ≥ 20 000` (copy of Part 182 `Led21M`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1486`, `τ_- = -0.3918`; tails at `n = 20 000`: `B_+ + B_- ≤ 0.00185`
(≈ `0.001847`). So the charges may use `0.008149`.
-/

namespace BstLean.Part183

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_20 : Eplus aL (hAL + dsL) hWL cWL (2135 / 1000) (743 / 5000) ≤
    -(3544197053 / 10000000000000 : ℝ) := by
  have e : (743 / 5000 : ℝ) * cWL = 1023111 / 5000000 := by unfold cWL; norm_num
  refine certP (eT := 1227061393587 / 1000000000000) (y := 4545856797 / 12500000000)
    (ehi := 44956165721 / 31250000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_20 : Eminus aL (hAL + dsL) hWL cWL (2135 / 1000) (-(1959 / 5000)) ≤
    -(13468027 / 39062500000 : ℝ) := by
  have e : (-(1959 / 5000) : ℝ) * cWL = -(2697543 / 5000000) := by unfold cWL; norm_num
  have e2 : (-31023826871 / 50000000000 : ℝ) / 2 = -31023826871 / 100000000000 := by
    norm_num
  refine certM (eLo := 116606937047 / 200000000000) (eHi := 145758671309 / 250000000000)
    (y := -31023826871 / 50000000000) (u := 733272219583 / 1000000000000)
    (ehi := 537688148013 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le20 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_20 : exp (-(((20000 : ℕ) : ℝ) * (3544197053 / 10000000000000)) / 8) ≤
    ((642091391139 / 1000000000000) ^ 2 : ℝ) := by
  have e : -(((20000 : ℕ) : ℝ) * (3544197053 / 10000000000000)) / 8 =
      2 * (-(3544197053 / 8000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le20 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_20 : exp (-(((20000 : ℕ) : ℝ) * (13468027 / 39062500000)) / 8) ≤
    ((129974789217 / 200000000000) ^ 2 : ℝ) := by
  have e : -(((20000 : ℕ) : ℝ) * (13468027 / 39062500000)) / 8 =
      2 * (-(13468027 / 31250000)) := by norm_num
  rw [e]
  refine exp_two_mul_le20 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.135`, every
`n ≥ 20 000`, with the charge budget `0.008149`** (tails `≤ 0.00185`). -/
theorem classifier_frame_20 (hn : 20000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 8149 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (2135 / 1000 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((20000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 2135 / 1000)
    (by norm_num : (0 : ℝ) < 743 / 5000) (by norm_num : (-(1959 / 5000) : ℝ) < 0) Ep_20 Em_20
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_20) (tail8 hnR (by norm_num) um_20)
    D t hEv hFW hFA hRA
  have hB : ((642091391139 / 1000000000000 : ℝ) ^ 2) ^ 8 +
      ((129974789217 / 200000000000 : ℝ) ^ 2) ^ 8 ≤ 185 / 10 ^ 5 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183

open BstLean.Part183 in
#print axioms classifier_frame_20
