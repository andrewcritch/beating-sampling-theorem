import BstLean.Part181Ledger

/-!
# Part 184 (file `GLed`): the ledger for the Agent frame constant `2.211` (TI-lite, `λ = 0.735`) at
`n ≥ 17 500` (copy of Part 182 `Led21M`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1455`, `τ_- = -0.383`; tails at `n = 17 500`: `B_+ + B_- ≤ 0.005041`
(≈ `0.0050408`). So the charges may use `0.004958`.
-/

namespace BstLean.Part183.F175

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_175 : Eplus aL (hAL + dsL) hWL cWL (2211 / 1000) (291 / 2000) ≤
    -(34702437 / 100000000000 : ℝ) := by
  have e : (291 / 2000 : ℝ) * cWL = 400707 / 2000000 := by unfold cWL; norm_num
  refine certP (eT := 1221834600359 / 1000000000000) (y := 9198618257 / 25000000000)
    (ehi := 722381092583 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_175 : Eminus aL (hAL + dsL) hWL cWL (2211 / 1000) (-(383 / 1000)) ≤
    -(3372065307 / 10000000000000 : ℝ) := by
  have e : (-(383 / 1000) : ℝ) * cWL = -(527391 / 1000000) := by unfold cWL; norm_num
  have e2 : (-63161004783 / 100000000000 : ℝ) / 2 = -63161004783 / 200000000000 := by
    norm_num
  refine certM (eLo := 590142645069 / 1000000000000) (eHi := 59014264507 / 100000000000)
    (y := -63161004783 / 100000000000) (u := 5696887603 / 7812500000)
    (ehi := 531734992671 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le175 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_175 : exp (-(((17500 : ℕ) : ℝ) * (34702437 / 100000000000)) / 8) ≤
    ((85520475997 / 125000000000) ^ 2 : ℝ) := by
  have e : -(((17500 : ℕ) : ℝ) * (34702437 / 100000000000)) / 8 =
      2 * (-(242917059 / 640000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le175 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_175 : exp (-(((17500 : ℕ) : ℝ) * (3372065307 / 10000000000000)) / 8) ≤
    ((345775062571 / 500000000000) ^ 2 : ℝ) := by
  have e : -(((17500 : ℕ) : ℝ) * (3372065307 / 10000000000000)) / 8 =
      2 * (-(23604457149 / 64000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le175 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.19`, every
`n ≥ 17 500`, with the charge budget `0.006499`** (tails `≤ 0.0035`). -/
theorem classifier_frame_175 (hn : 17500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 4958 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (2211 / 1000 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((17500 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 2211 / 1000)
    (by norm_num : (0 : ℝ) < 291 / 2000) (by norm_num : (-(383 / 1000) : ℝ) < 0) Ep_175 Em_175
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_175) (tail8 hnR (by norm_num) um_175)
    D t hEv hFW hFA hRA
  have hB : ((85520475997 / 125000000000 : ℝ) ^ 2) ^ 8 +
      ((345775062571 / 500000000000 : ℝ) ^ 2) ^ 8 ≤ 5041 / 10 ^ 6 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183.F175

open BstLean.Part183.F175 in
#print axioms classifier_frame_175
