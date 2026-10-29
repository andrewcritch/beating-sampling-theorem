import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2A`): ledger certificates, frame constants 7.75, 5, 6, 7, 8

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `7.75`: `τ_+ = 0.058756`, `τ_- = -0.138401`, `n₀ = 48000` -/

lemma Ep_775 : Eplus aL (hAL + dsL) hWL cWL (31 / 4) (14689 / 250000) ≤ -(1389987 / 10000000000 : ℝ) := by
  have e : (14689 / 250000 : ℝ) * cWL = 20226753 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 542135033887 / 500000000000) (y := 48993629 / 100000000) (ehi := 816106114201 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_775 : Eminus aL (hAL + dsL) hWL cWL (31 / 4) (-(138401 / 1000000)) ≤ -(1262409 / 10000000000 : ℝ) := by
  have e : (-(138401 / 1000000) : ℝ) * cWL = -(190578177 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(93729421 / 100000000) : ℝ) / 2 = -(93729421 / 200000000) := by norm_num
  refine certM (eLo := 826481143387 / 1000000000000) (eHi := 206620285847 / 250000000000) (y := -(93729421 / 100000000)) (u := 156462100741 / 250000000000)
    (ehi := 391686223493 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
    (by norm_num) ?_
  · rw [e]
    refine le_exp_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · rw [e2]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma up_775 : exp (-(((48000 : ℕ) : ℝ) * (1389987 / 10000000000)) / 8) ≤ (2171559803 / 5000000000 : ℝ) := by
  have e : -(((48000 : ℕ) : ℝ) * (1389987 / 10000000000)) / 8 = -(4169961 / 5000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_775 : exp (-(((48000 : ℕ) : ℝ) * (1262409 / 10000000000)) / 8) ≤ (93772531 / 200000000 : ℝ) := by
  have e : -(((48000 : ℕ) : ℝ) * (1262409 / 10000000000)) / 8 = -(3787227 / 5000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `7.75`, every
`n ≥ 48000`** (exponents `τ_+ = 0.058756`, `τ_- = -0.138401`; `E_+ ≤ −0.000138999`,
`E_- ≤ −0.000126241`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `7.75/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_775 {n : ℕ} (hn : 48000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (31 / 4 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 48000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_775 Em_775 (by norm_num) (by norm_num) up_775 um_775 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `5.0`: `τ_+ = 0.083238`, `τ_- = -0.204571`, `n₀ = 33500` -/

lemma Ep_5 : Eplus aL (hAL + dsL) hWL cWL (5) (41619 / 500000) ≤ -(197523 / 1000000000 : ℝ) := by
  have e : (41619 / 500000 : ℝ) * cWL = 57309363 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 280361444483 / 250000000000) (y := 45553001 / 100000000) (ehi := 157700899211 / 100000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_5 : Eminus aL (hAL + dsL) hWL cWL (5) (-(204571 / 1000000)) ≤ -(57513 / 312500000 : ℝ) := by
  have e : (-(204571 / 1000000) : ℝ) * cWL = -(281694267 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(85554213 / 100000000) : ℝ) / 2 = -(85554213 / 200000000) := by norm_num
  refine certM (eLo := 150900865229 / 200000000000) (eHi := 377252163073 / 500000000000) (y := -(85554213 / 100000000)) (u := 81495081791 / 125000000000)
    (ehi := 53131586849 / 125000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
    (by norm_num) ?_
  · rw [e]
    refine le_exp_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · rw [e2]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma up_5 : exp (-(((33500 : ℕ) : ℝ) * (197523 / 1000000000)) / 8) ≤ (4373036113 / 10000000000 : ℝ) := by
  have e : -(((33500 : ℕ) : ℝ) * (197523 / 1000000000)) / 8 = -(13234041 / 16000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_5 : exp (-(((33500 : ℕ) : ℝ) * (57513 / 312500000)) / 8) ≤ (2313505051 / 5000000000 : ℝ) := by
  have e : -(((33500 : ℕ) : ℝ) * (57513 / 312500000)) / 8 = -(3853371 / 5000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `5.0`, every
`n ≥ 33500`** (exponents `τ_+ = 0.083238`, `τ_- = -0.204571`; `E_+ ≤ −0.000197523`,
`E_- ≤ −0.000184042`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `5.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_5 {n : ℕ} (hn : 33500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (5 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 33500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_5 Em_5 (by norm_num) (by norm_num) up_5 um_5 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `6.0`: `τ_+ = 0.072267`, `τ_- = -0.174421`, `n₀ = 38500` -/

lemma Ep_6 : Eplus aL (hAL + dsL) hWL cWL (6) (72267 / 1000000) ≤ -(214081 / 1250000000 : ℝ) := by
  have e : (72267 / 1000000 : ℝ) * cWL = 99511659 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 552315674781 / 500000000000) (y := 11773827 / 25000000) (ehi := 1601519842601 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_6 : Eminus aL (hAL + dsL) hWL cWL (6) (-(174421 / 1000000)) ≤ -(789221 / 5000000000 : ℝ) := by
  have e : (-(174421 / 1000000) : ℝ) * cWL = -(240177717 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(22322403 / 25000000) : ℝ) / 2 = -(22322403 / 50000000) := by norm_num
  refine certM (eLo := 98311009543 / 125000000000) (eHi := 157297615269 / 200000000000) (y := -(22322403 / 25000000)) (u := 639896995573 / 1000000000000)
    (ehi := 25591760309 / 62500000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
    (by norm_num) ?_
  · rw [e]
    refine le_exp_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · rw [e2]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma up_6 : exp (-(((38500 : ℕ) : ℝ) * (214081 / 1250000000)) / 8) ≤ (1096451309 / 2500000000 : ℝ) := by
  have e : -(((38500 : ℕ) : ℝ) * (214081 / 1250000000)) / 8 = -(16484237 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_6 : exp (-(((38500 : ℕ) : ℝ) * (789221 / 5000000000)) / 8) ≤ (2339208677 / 5000000000 : ℝ) := by
  have e : -(((38500 : ℕ) : ℝ) * (789221 / 5000000000)) / 8 = -(60770017 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `6.0`, every
`n ≥ 38500`** (exponents `τ_+ = 0.072267`, `τ_- = -0.174421`; `E_+ ≤ −0.000171265`,
`E_- ≤ −0.000157844`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `6.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_6 {n : ℕ} (hn : 38500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (6 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 38500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_6 Em_6 (by norm_num) (by norm_num) up_6 um_6 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `7.0`: `τ_+ = 0.063869`, `τ_- = -0.151876`, `n₀ = 44000` -/

lemma Ep_7 : Eplus aL (hAL + dsL) hWL cWL (7) (63869 / 1000000) ≤ -(302399 / 2000000000 : ℝ) := by
  have e : (63869 / 1000000 : ℝ) * cWL = 87947613 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 218386183509 / 200000000000) (y := 48275213 / 100000000) (ehi := 405132043727 / 250000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_7 : Eminus aL (hAL + dsL) hWL cWL (7) (-(37969 / 250000)) ≤ -(690537 / 5000000000 : ℝ) := by
  have e : (-(37969 / 250000) : ℝ) * cWL = -(52283313 / 250000000) := by unfold cWL; norm_num
  have e2 : (-(18414381 / 20000000) : ℝ) / 2 = -(18414381 / 40000000) := by norm_num
  refine certM (eLo := 101410890351 / 125000000000) (eHi := 811287122809 / 1000000000000) (y := -(18414381 / 20000000)) (u := 631056724049 / 1000000000000)
    (ehi := 49779073621 / 125000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
    (by norm_num) ?_
  · rw [e]
    refine le_exp_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · rw [e2]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma up_7 : exp (-(((44000 : ℕ) : ℝ) * (302399 / 2000000000)) / 8) ≤ (2176766813 / 5000000000 : ℝ) := by
  have e : -(((44000 : ℕ) : ℝ) * (302399 / 2000000000)) / 8 = -(3326389 / 4000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_7 : exp (-(((44000 : ℕ) : ℝ) * (690537 / 5000000000)) / 8) ≤ (4678578821 / 10000000000 : ℝ) := by
  have e : -(((44000 : ℕ) : ℝ) * (690537 / 5000000000)) / 8 = -(7595907 / 10000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `7.0`, every
`n ≥ 44000`** (exponents `τ_+ = 0.063869`, `τ_- = -0.151876`; `E_+ ≤ −0.0001512`,
`E_- ≤ −0.000138107`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `7.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_7 {n : ℕ} (hn : 44000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (7 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 44000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_7 Em_7 (by norm_num) (by norm_num) up_7 um_7 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `8.0`: `τ_+ = 0.05723`, `τ_- = -0.134416`, `n₀ = 49500` -/

lemma Ep_8 : Eplus aL (hAL + dsL) hWL cWL (8) (5723 / 100000) ≤ -(338399 / 2500000000 : ℝ) := by
  have e : (5723 / 100000 : ℝ) * cWL = 7880571 / 100000000 := by unfold cWL; norm_num
  refine certP (eT := 540997040509 / 500000000000) (y := 6151019 / 12500000) (ehi := 817858728729 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_8 : Eminus aL (hAL + dsL) hWL cWL (8) (-(8401 / 62500)) ≤ -(153403 / 1250000000 : ℝ) := by
  have e : (-(8401 / 62500) : ℝ) * cWL = -(11568177 / 62500000) := by unfold cWL; norm_num
  have e2 : (-(94217209 / 100000000) : ℝ) / 2 = -(94217209 / 200000000) := by norm_num
  refine certM (eLo := 811551559 / 976562500) (eHi := 831028796417 / 1000000000000) (y := -(94217209 / 100000000)) (u := 124864771231 / 200000000000)
    (ehi := 77956055473 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
    (by norm_num) ?_
  · rw [e]
    refine le_exp_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · rw [e2]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma up_8 : exp (-(((49500 : ℕ) : ℝ) * (338399 / 2500000000)) / 8) ≤ (2163874549 / 5000000000 : ℝ) := by
  have e : -(((49500 : ℕ) : ℝ) * (338399 / 2500000000)) / 8 = -(33501501 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_8 : exp (-(((49500 : ℕ) : ℝ) * (153403 / 1250000000)) / 8) ≤ (4679729191 / 10000000000 : ℝ) := by
  have e : -(((49500 : ℕ) : ℝ) * (153403 / 1250000000)) / 8 = -(15186897 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `8.0`, every
`n ≥ 49500`** (exponents `τ_+ = 0.05723`, `τ_- = -0.134416`; `E_+ ≤ −0.00013536`,
`E_- ≤ −0.000122722`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `8.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_8 {n : ℕ} (hn : 49500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (8 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 49500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_8 Em_8 (by norm_num) (by norm_num) up_8 um_8 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_775
open BstLean.Part160 in
#print axioms classifier_frame_5
open BstLean.Part160 in
#print axioms classifier_frame_6
open BstLean.Part160 in
#print axioms classifier_frame_7
open BstLean.Part160 in
#print axioms classifier_frame_8
