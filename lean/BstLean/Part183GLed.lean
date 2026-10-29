import BstLean.Part181Ledger

/-!
# Part 183 (file `GLed`): the ledger for the Agent frame constant `2.17` (TI-lite, `λ = 0.735`) at
`n ≥ 19 000` (copy of Part 182 `Led21M`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1471`, `τ_- = -0.3877`; tails at `n = 19 000`: `B_+ + B_- ≤ 0.0028`
(≈ `0.002798`). So the charges may use `0.007199`.
-/

namespace BstLean.Part183

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_19 : Eplus aL (hAL + dsL) hWL cWL (217 / 100) (1471 / 10000) ≤
    -(701948299 / 2000000000000 : ℝ) := by
  have e : (1471 / 10000 : ℝ) * cWL = 2025567 / 10000000 := by unfold cWL; norm_num
  refine certP (eT := 612264756989 / 500000000000) (y := 36550870891 / 100000000000)
    (ehi := 360311749221 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_19 : Eminus aL (hAL + dsL) hWL cWL (217 / 100) (-(3877 / 10000)) ≤
    -(3412540713 / 10000000000000 : ℝ) := by
  have e : (-(3877 / 10000) : ℝ) * cWL = -(5338629 / 10000000) := by unfold cWL; norm_num
  have e2 : (-31282784639 / 50000000000 : ℝ) / 2 = -31282784639 / 100000000000 := by
    norm_num
  refine certM (eLo := 9161494273 / 15625000000) (eHi := 586335633473 / 1000000000000)
    (y := -31282784639 / 50000000000) (u := 365687905359 / 500000000000)
    (ehi := 66863822063 / 125000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le19 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_19 : exp (-(((19000 : ℕ) : ℝ) * (701948299 / 2000000000000)) / 8) ≤
    ((65916473233 / 100000000000) ^ 2 : ℝ) := by
  have e : -(((19000 : ℕ) : ℝ) * (701948299 / 2000000000000)) / 8 =
      2 * (-(13337017681 / 32000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le19 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_19 : exp (-(((19000 : ℕ) : ℝ) * (3412540713 / 10000000000000)) / 8) ≤
    ((333408641319 / 500000000000) ^ 2 : ℝ) := by
  have e : -(((19000 : ℕ) : ℝ) * (3412540713 / 10000000000000)) / 8 =
      2 * (-(64838273547 / 160000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le19 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.17`, every
`n ≥ 19 000`, with the charge budget `0.007199`** (tails `≤ 0.0028`). -/
theorem classifier_frame_19 (hn : 19000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 7199 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (217 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((19000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 217 / 100)
    (by norm_num : (0 : ℝ) < 1471 / 10000) (by norm_num : (-(3877 / 10000) : ℝ) < 0) Ep_19 Em_19
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_19) (tail8 hnR (by norm_num) um_19)
    D t hEv hFW hFA hRA
  have hB : ((65916473233 / 100000000000 : ℝ) ^ 2) ^ 8 +
      ((333408641319 / 500000000000 : ℝ) ^ 2) ^ 8 ≤ 28 / 10 ^ 4 := by norm_num
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
#print axioms classifier_frame_19
