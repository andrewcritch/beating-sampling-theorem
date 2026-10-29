import BstLean.Part181Ledger

/-!
# Part 184 (file `FLed`): the ledger for the Agent frame constant `2.19` (TI-lite, `λ = 0.735`) at
`n ≥ 18 500` (copy of Part 182 `Led21M`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1463`, `τ_- = -0.3854`; tails at `n = 18 500`: `B_+ + B_- ≤ 0.0035`
(≈ `0.003449`). So the charges may use `0.006499`.
-/

namespace BstLean.Part183.F185

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_185 : Eplus aL (hAL + dsL) hWL cWL (219 / 100) (1463 / 10000) ≤
    -(872589909 / 2500000000000 : ℝ) := by
  have e : (1463 / 10000 : ℝ) * cWL = 2014551 / 10000000 := by unfold cWL; norm_num
  refine certP (eT := 1223181314989 / 1000000000000) (y := 36666250917 / 100000000000)
    (ehi := 721455433873 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_185 : Eminus aL (hAL + dsL) hWL cWL (219 / 100) (-(1927 / 5000)) ≤
    -(848171043 / 2500000000000 : ℝ) := by
  have e : (-(1927 / 5000) : ℝ) * cWL = -(2653479 / 5000000) := by unfold cWL; norm_num
  have e2 : (-31429154499 / 50000000000 : ℝ) / 2 = -31429154499 / 100000000000 := by
    norm_num
  refine certM (eLo := 58819556079 / 100000000000) (eHi := 588195560791 / 1000000000000)
    (y := -31429154499 / 50000000000) (u := 730306080041 / 1000000000000)
    (ehi := 106669394109 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le185 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_185 : exp (-(((18500 : ℕ) : ℝ) * (872589909 / 2500000000000)) / 8) ≤
    ((333964688893 / 500000000000) ^ 2 : ℝ) := by
  have e : -(((18500 : ℕ) : ℝ) * (872589909 / 2500000000000)) / 8 =
      2 * (-(32285826633 / 80000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le185 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_185 : exp (-(((18500 : ℕ) : ℝ) * (848171043 / 2500000000000)) / 8) ≤
    ((168878886567 / 250000000000) ^ 2 : ℝ) := by
  have e : -(((18500 : ℕ) : ℝ) * (848171043 / 2500000000000)) / 8 =
      2 * (-(31382328591 / 80000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le185 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.19`, every
`n ≥ 18 500`, with the charge budget `0.006499`** (tails `≤ 0.0035`). -/
theorem classifier_frame_185 (hn : 18500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 6499 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (219 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((18500 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 219 / 100)
    (by norm_num : (0 : ℝ) < 1463 / 10000) (by norm_num : (-(1927 / 5000) : ℝ) < 0) Ep_185 Em_185
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_185) (tail8 hnR (by norm_num) um_185)
    D t hEv hFW hFA hRA
  have hB : ((333964688893 / 500000000000 : ℝ) ^ 2) ^ 8 +
      ((168878886567 / 250000000000 : ℝ) ^ 2) ^ 8 ≤ 35 / 10 ^ 4 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183.F185

open BstLean.Part183.F185 in
#print axioms classifier_frame_185
