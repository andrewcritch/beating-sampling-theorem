import BstLean.Part181Ledger

/-!
# Part 186 (file `FLed`): the ledger for the Agent frame constant `2.082` (TI-lite, `λ = 0.647, conditional`) at
`n ≥ 16 500` (copy of Part 185 `FLed`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1508`, `τ_- = -0.3981`; tails at `n = 16 500`: `B_+ + B_- ≤ 0.005734`
(≈ `0.0057332`). So the charges may use `0.004265`.
-/

namespace BstLean.Part183.F165

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_165 : Eplus aL (hAL + dsL) hWL cWL (2082 / 1000) (377 / 2500) ≤
    -(3597715713 / 10000000000000 : ℝ) := by
  have e : (377 / 2500 : ℝ) * cWL = 519129 / 2500000 := by unfold cWL; norm_num
  refine certP (eT := 307696072399 / 250000000000) (y := 18022769567 / 50000000000)
    (ehi := 1433982289009 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_165 : Eminus aL (hAL + dsL) hWL cWL (2082 / 1000) (-(3981 / 10000)) ≤
    -(1751268989 / 5000000000000 : ℝ) := by
  have e : (-(3981 / 10000) : ℝ) * cWL = -(5481837 / 10000000) := by unfold cWL; norm_num
  have e2 : (-30619077161 / 50000000000 : ℝ) / 2 = -30619077161 / 100000000000 := by
    norm_num
  refine certM (eLo := 7224983457 / 12500000000) (eHi := 577998676561 / 1000000000000)
    (y := -30619077161 / 50000000000) (u := 147249230239 / 200000000000)
    (ehi := 10841167903 / 20000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le165 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_165 : exp (-(((16500 : ℕ) : ℝ) * (3597715713 / 10000000000000)) / 8) ≤
    ((345016991147 / 500000000000) ^ 2 : ℝ) := by
  have e : -(((16500 : ℕ) : ℝ) * (3597715713 / 10000000000000)) / 8 =
      2 * (-(118724618529 / 320000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le165 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_165 : exp (-(((16500 : ℕ) : ℝ) * (1751268989 / 5000000000000)) / 8) ≤
    ((696840153883 / 1000000000000) ^ 2 : ℝ) := by
  have e : -(((16500 : ℕ) : ℝ) * (1751268989 / 5000000000000)) / 8 =
      2 * (-(57791876637 / 160000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le165 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.082`, every
`n ≥ 16 500`, with the charge budget `0.004265`** (tails `≤ 0.005734`). -/
theorem classifier_frame_165 (hn : 16500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 853 / 200000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (2082 / 1000 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((16500 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 2082 / 1000)
    (by norm_num : (0 : ℝ) < 377 / 2500) (by norm_num : (-(3981 / 10000) : ℝ) < 0) Ep_165 Em_165
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_165) (tail8 hnR (by norm_num) um_165)
    D t hEv hFW hFA hRA
  have hB : ((345016991147 / 500000000000 : ℝ) ^ 2) ^ 8 +
      ((696840153883 / 1000000000000 : ℝ) ^ 2) ^ 8 ≤ 2867 / 500000 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183.F165

open BstLean.Part183.F165 in
#print axioms classifier_frame_165
