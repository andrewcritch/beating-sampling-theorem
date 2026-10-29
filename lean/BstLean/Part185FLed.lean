import BstLean.Part181Ledger

/-!
# Part 185 (file `FLed`): the ledger for the Agent frame constant `2.217` (TI-lite, `λ = 0.735`) at
`n ≥ 17 250` (copy of Part 184 `ILed`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1453`, `τ_- = -0.3823`; tails at `n = 17 250`: `B_+ + B_- ≤ 0.005546`
(≈ `0.0055454`). So the charges may use `0.004453`.
-/

namespace BstLean.Part183.F1725

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_1725 : Eplus aL (hAL + dsL) hWL cWL (2217 / 1000) (1453 / 10000) ≤
    -(692907893 / 2000000000000 : ℝ) := by
  have e : (1453 / 10000 : ℝ) * cWL = 2000781 / 10000000 := by unfold cWL; norm_num
  refine certP (eT := 1221498153441 / 1000000000000) (y := 18419183163 / 50000000000)
    (ehi := 1445396478133 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_1725 : Eminus aL (hAL + dsL) hWL cWL (2217 / 1000) (-(3823 / 10000)) ≤
    -(3366217067 / 10000000000000 : ℝ) := by
  have e : (-(3823 / 10000) : ℝ) * cWL = -(5264271 / 10000000) := by unfold cWL; norm_num
  have e2 : (-15811116009 / 25000000000 : ℝ) / 2 = -15811116009 / 50000000000 := by
    norm_num
  refine certM (eLo := 147677939451 / 250000000000) (eHi := 118142351561 / 200000000000)
    (y := -15811116009 / 25000000000) (u := 182224345889 / 250000000000)
    (ehi := 106258279151 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le1725 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_1725 : exp (-(((17250 : ℕ) : ℝ) * (692907893 / 2000000000000)) / 8) ≤
    ((172076691249 / 250000000000) ^ 2 : ℝ) := by
  have e : -(((17250 : ℕ) : ℝ) * (692907893 / 2000000000000)) / 8 =
      2 * (-(47810644617 / 128000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le1725 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_1725 : exp (-(((17250 : ℕ) : ℝ) * (3366217067 / 10000000000000)) / 8) ≤
    ((27825675583 / 40000000000) ^ 2 : ℝ) := by
  have e : -(((17250 : ℕ) : ℝ) * (3366217067 / 10000000000000)) / 8 =
      2 * (-(232268977623 / 640000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le1725 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.217`, every
`n ≥ 17 250`, with the charge budget `0.004453`** (tails `≤ 0.005546`). -/
theorem classifier_frame_1725 (hn : 17250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 4453 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (2217 / 1000 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((17250 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 2217 / 1000)
    (by norm_num : (0 : ℝ) < 1453 / 10000) (by norm_num : (-(3823 / 10000) : ℝ) < 0) Ep_1725 Em_1725
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_1725) (tail8 hnR (by norm_num) um_1725)
    D t hEv hFW hFA hRA
  have hB : ((172076691249 / 250000000000 : ℝ) ^ 2) ^ 8 +
      ((27825675583 / 40000000000 : ℝ) ^ 2) ^ 8 ≤ 2773 / 500000 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183.F1725

open BstLean.Part183.F1725 in
#print axioms classifier_frame_1725
