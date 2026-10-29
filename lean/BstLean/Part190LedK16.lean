import BstLean.Part188All
import BstLean.Part181Ledger
import BstLean.Part188R160Ledger2Gen



namespace BstLean.Part190.Frame16200
open BstLean.Part183 BstLean.Part183.F16250

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part160

lemma Ep_16200K16 : Eplus aL (hAL + dsL) hWL cWL (193 / 100) (311 / 2000) ≤
    -(188001277 / 500000000000 : ℝ) := by
  have e : (311 / 2000 : ℝ) * cWL = 428247 / 2000000 := by unfold cWL; norm_num
  refine certP (eT := 619387817069 / 500000000000) (y := 86427486699 / 250000000000)
    (ehi := 1412992713311 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_16200K16 : Eminus aL (hAL + dsL) hWL cWL (193 / 100) (-(823 / 2000)) ≤
    -(366834679 / 1000000000000 : ℝ) := by
  have e : (-(823 / 2000) : ℝ) * cWL = -(1133271 / 2000000) := by unfold cWL; norm_num
  have e2 : (-290944335229 / 500000000000 : ℝ) / 2 = -290944335229 / 1000000000000 := by
    norm_num
  refine certM (eLo := 113486270693 / 200000000000) (eHi := 283715676733 / 500000000000)
    (y := -290944335229 / 500000000000) (u := 373778644733 / 500000000000)
    (ehi := 279420950517 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_
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

lemma exp_two_mul_le16200K16 {a v : ℝ} (hv : exp a ≤ v) : exp (2 * a) ≤ v ^ 2 := by
  have e : exp (2 * a) = exp a ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (exp_pos _).le hv 2

lemma up_16200K16 : exp (-(((16200 : ℕ) : ℝ) * (188001277 / 500000000000)) / 8) ≤
    ((683381106559 / 1000000000000) ^ 2 : ℝ) := by
  have e : -(((16200 : ℕ) : ℝ) * (188001277 / 500000000000)) / 8 =
      2 * ((-15228103437 / 40000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le16200K16 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_16200K16 : exp (-(((16200 : ℕ) : ℝ) * (366834679 / 1000000000000)) / 8) ≤
    ((1347175989 / 1953125000) ^ 2 : ℝ) := by
  have e : -(((16200 : ℕ) : ℝ) * (366834679 / 1000000000000)) / 8 =
      2 * ((-29713608999 / 80000000000)) := by norm_num
  rw [e]
  refine exp_two_mul_le16200K16 ?_
  refine exp_le_taylor (b := 1) 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

variable {n : ℕ}


theorem classifier_frame_16200K16 (hn : 16200 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 5111 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (193 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : ((16200 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := BstLean.Part188.Base160_R.classifier_networks_frameconst2 (by omega : 16200 ≤ n) (by norm_num : (0 : ℝ) < 193 / 100)
    (by norm_num : (0 : ℝ) < 311 / 2000) (by norm_num : (-(823 / 2000) : ℝ) < 0) Ep_16200K16 Em_16200K16
    (by norm_num) (by norm_num) (tail8 hnR (by norm_num) up_16200K16) (tail8 hnR (by norm_num) um_16200K16)
    D t hEv hFW hFA hRA
  have hB : ((683381106559 / 1000000000000 : ℝ) ^ 2) ^ 8 +
      ((1347175989 / 1953125000 : ℝ) ^ 2) ^ 8 ≤ 611 / 125000 := by norm_num
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part190.Frame16200

open BstLean.Part190.Frame16200 in
#print axioms classifier_frame_16200K16
