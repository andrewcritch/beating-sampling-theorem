import BstLean.Part181Ledger

/-!
# Part 184 (file `GLed`): the ledger for the Agent frame constant `2.20` (TI-lite, `λ = 0.735`) at
`n ≥ 18 000` (copy of Part 182 `Led21M`)

No proof is left open; no `native_decide` or `axiom` is used. The rational certificates were
chosen outside Lean (single-process python); Lean checks each inequality.

Exponents `τ_+ = 0.1459`, `τ_- = -0.3842`; tails at `n = 18 000`: `B_+ + B_- ≤ 0.00417`
(≈ `0.0041685`). So the charges may use `0.005829`.
-/

namespace BstLean.Part183.F18

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_18 : Eplus aL (hAL + dsL) hWL cWL (220 / 100) (1459 / 10000) ≤
    -(3480750769 / 10000000000000 : ℝ) := by
  have e : (1459 / 10000 : ℝ) * cWL = 2009043 / 10000000 := by unfold cWL; norm_num
  refine certP (eT := 152813471529 / 125000000000) (y := 36722515729 / 100000000000)
    (ehi := 1443722947269 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_18 : Eminus aL (hAL + dsL) hWL cWL (220 / 100) (-(1921 / 5000)) ≤
    -(845709107 / 2500000000000 : ℝ) := by
  have e : (-(1921 / 5000) : ℝ) * cWL = -(2645217 / 5000000) := by unfold cWL; norm_num
  have e2 : (-3149808771 / 5000000000 : ℝ) / 2 = -3149808771 / 10000000000 := by
    norm_num
  refine certM (eLo := 589168298589 / 1000000000000) (eHi := 58916829859 / 100000000000)
    (y := -3149808771 / 5000000000) (u := 729802830083 / 1000000000000)
    (ehi := 266306085399 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le18 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_18 : exp (-(((18000 : ℕ) : ℝ) * (3480750769 / 10000000000000)) / 8) ≤
    ((675984953373 / 1000000000000) ^ 2 : ℝ) := by
  have e : -(((18000 : ℕ) : ℝ) * (3480750769 / 10000000000000)) / 8 =
      2 * (-(31326756921 / 80000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le18 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_18 : exp (-(((18000 : ℕ) : ℝ) * (845709107 / 2500000000000)) / 8) ≤
    ((683472335671 / 1000000000000) ^ 2 : ℝ) := by
  have e : -(((18000 : ℕ) : ℝ) * (845709107 / 2500000000000)) / 8 =
      2 * (-(7611381963 / 20000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le18 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}

/-- **The conditional classifier theorem for the Agent frame constant `2.19`, every
`n ≥ 18 000`, with the charge budget `0.006499`** (tails `≤ 0.0035`). -/
theorem classifier_frame_18 (hn : 18000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 5829 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (220 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((18000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) (by norm_num : (0 : ℝ) < 220 / 100)
    (by norm_num : (0 : ℝ) < 1459 / 10000) (by norm_num : (-(1921 / 5000) : ℝ) < 0) Ep_18 Em_18
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_18) (tail8 hnR (by norm_num) um_18)
    D t hEv hFW hFA hRA
  have hB : ((675984953373 / 1000000000000 : ℝ) ^ 2) ^ 8 +
      ((683472335671 / 1000000000000 : ℝ) ^ 2) ^ 8 ≤ 417 / 10 ^ 5 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part183.F18

open BstLean.Part183.F18 in
#print axioms classifier_frame_18
