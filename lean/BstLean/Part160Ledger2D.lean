import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2D`): ledger certificates, frame constants 5.65, 5.6, 5.7, 4.55, 4.6, 4.45

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `5.65`: `τ_+ = 0.075759`, `τ_- = -0.183933`, `n₀ = 36750` -/

lemma Ep_565 : Eplus aL (hAL + dsL) hWL cWL (565 / 100) (75759 / 1000000) ≤ -(359233 / 2000000000 : ℝ) := by
  have e : (75759 / 1000000 : ℝ) * cWL = 104320143 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 1109955742603 / 1000000000000) (y := 4660483 / 10000000) (ehi := 796841986213 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_565 : Eminus aL (hAL + dsL) hWL cWL (565 / 100) (-(183933 / 1000000)) ≤ -(1661339 / 10000000000 : ℝ) := by
  have e : (-(183933 / 1000000) : ℝ) * cWL = -(253275741 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(88111309 / 100000000) : ℝ) / 2 = -(88111309 / 200000000) := by norm_num
  refine certM (eLo := 776253807309 / 1000000000000) (eHi := 77625380731 / 100000000000) (y := -(88111309 / 100000000)) (u := 321839042779 / 500000000000)
    (ehi := 103580369457 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_565 : exp (-(((36750 : ℕ) : ℝ) * (359233 / 2000000000)) / 8) ≤ (4381853447 / 10000000000 : ℝ) := by
  have e : -(((36750 : ℕ) : ℝ) * (359233 / 2000000000)) / 8 = -(52807251 / 64000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_565 : exp (-(((36750 : ℕ) : ℝ) * (1661339 / 10000000000)) / 8) ≤ (4661827273 / 10000000000 : ℝ) := by
  have e : -(((36750 : ℕ) : ℝ) * (1661339 / 10000000000)) / 8 = -(244216833 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `5.65`, every
`n ≥ 36750`** (exponents `τ_+ = 0.075759`, `τ_- = -0.183933`; `E_+ ≤ −0.000179616`,
`E_- ≤ −0.000166134`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `5.65/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_565 {n : ℕ} (hn : 36750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (565 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 36750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_565 Em_565 (by norm_num) (by norm_num) up_565 um_565 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `5.6`: `τ_+ = 0.076285`, `τ_- = -0.185376`, `n₀ = 36500` -/

lemma Ep_560 : Eplus aL (hAL + dsL) hWL cWL (560 / 100) (15257 / 200000) ≤ -(180877 / 1000000000 : ℝ) := by
  have e : (15257 / 200000 : ℝ) * cWL = 21008889 / 200000000 := by unfold cWL; norm_num
  refine certP (eT := 555379988493 / 500000000000) (y := 46530257 / 100000000) (ehi := 1592495957501 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_560 : Eminus aL (hAL + dsL) hWL cWL (560 / 100) (-(5793 / 31250)) ≤ -(1673887 / 10000000000 : ℝ) := by
  have e : (-(5793 / 31250) : ℝ) * cWL = -(7976961 / 31250000) := by unfold cWL; norm_num
  have e2 : (-(87932997 / 100000000) : ℝ) / 2 = -(87932997 / 200000000) := by norm_num
  refine certM (eLo := 96839114231 / 125000000000) (eHi := 774712913849 / 1000000000000) (y := -(87932997 / 100000000)) (u := 644252219091 / 1000000000000)
    (ehi := 103765230451 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_560 : exp (-(((36500 : ℕ) : ℝ) * (180877 / 1000000000)) / 8) ≤ (1095312181 / 2500000000 : ℝ) := by
  have e : -(((36500 : ℕ) : ℝ) * (180877 / 1000000000)) / 8 = -(13204021 / 16000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_560 : exp (-(((36500 : ℕ) : ℝ) * (1673887 / 10000000000)) / 8) ≤ (2329670797 / 5000000000 : ℝ) := by
  have e : -(((36500 : ℕ) : ℝ) * (1673887 / 10000000000)) / 8 = -(122193751 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `5.6`, every
`n ≥ 36500`** (exponents `τ_+ = 0.076285`, `τ_- = -0.185376`; `E_+ ≤ −0.000180877`,
`E_- ≤ −0.000167389`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `5.6/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_560 {n : ℕ} (hn : 36500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (560 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 36500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_560 Em_560 (by norm_num) (by norm_num) up_560 um_560 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `5.7`: `τ_+ = 0.075239`, `τ_- = -0.182514`, `n₀ = 37000` -/

lemma Ep_570 : Eplus aL (hAL + dsL) hWL cWL (570 / 100) (75239 / 1000000) ≤ -(356747 / 2000000000 : ℝ) := by
  have e : (75239 / 1000000 : ℝ) * cWL = 103604103 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 110916125437 / 100000000000) (y := 23338769 / 50000000) (ehi := 797421564759 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_570 : Eminus aL (hAL + dsL) hWL cWL (570 / 100) (-(91257 / 500000)) ≤ -(103061 / 625000000 : ℝ) := by
  have e : (-(91257 / 500000) : ℝ) * cWL = -(125660889 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(706303 / 800000) : ℝ) / 2 = -(706303 / 1600000) := by norm_num
  refine certM (eLo := 15555441227 / 20000000000) (eHi := 777772061351 / 1000000000000) (y := -(706303 / 800000)) (u := 321555038999 / 500000000000)
    (ehi := 413590572423 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_570 : exp (-(((37000 : ℕ) : ℝ) * (356747 / 2000000000)) / 8) ≤ (4382448803 / 10000000000 : ℝ) := by
  have e : -(((37000 : ℕ) : ℝ) * (356747 / 2000000000)) / 8 = -(13199639 / 16000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_570 : exp (-(((37000 : ℕ) : ℝ) * (103061 / 625000000)) / 8) ≤ (4664280987 / 10000000000 : ℝ) := by
  have e : -(((37000 : ℕ) : ℝ) * (103061 / 625000000)) / 8 = -(3813257 / 5000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `5.7`, every
`n ≥ 37000`** (exponents `τ_+ = 0.075239`, `τ_- = -0.182514`; `E_+ ≤ −0.000178373`,
`E_- ≤ −0.000164898`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `5.7/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_570 {n : ℕ} (hn : 37000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (570 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 37000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_570 Em_570 (by norm_num) (by norm_num) up_570 um_570 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.55`: `τ_+ = 0.089358`, `τ_- = -0.221685`, `n₀ = 30750` -/

lemma Ep_455 : Eplus aL (hAL + dsL) hWL cWL (455 / 100) (44679 / 500000) ≤ -(530471 / 2500000000 : ℝ) := by
  have e : (44679 / 500000 : ℝ) * cWL = 61522983 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 141367050547 / 125000000000) (y := 44692677 / 100000000) (ehi := 390874950001 / 250000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_455 : Eminus aL (hAL + dsL) hWL cWL (455 / 100) (-(44337 / 200000)) ≤ -(397659 / 2000000000 : ℝ) := by
  have e : (-(44337 / 200000) : ℝ) * cWL = -(61052049 / 200000000) := by unfold cWL; norm_num
  have e2 : (-(20856801 / 25000000) : ℝ) / 2 = -(20856801 / 50000000) := by norm_num
  refine certM (eLo := 368465783339 / 500000000000) (eHi := 736931566679 / 1000000000000) (y := -(20856801 / 25000000)) (u := 131786257203 / 200000000000)
    (ehi := 43419043969 / 100000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_455 : exp (-(((30750 : ℕ) : ℝ) * (530471 / 2500000000)) / 8) ≤ (221187097 / 500000000 : ℝ) := by
  have e : -(((30750 : ℕ) : ℝ) * (530471 / 2500000000)) / 8 = -(65247933 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_455 : exp (-(((30750 : ℕ) : ℝ) * (397659 / 2000000000)) / 8) ≤ (1164206619 / 2500000000 : ℝ) := by
  have e : -(((30750 : ℕ) : ℝ) * (397659 / 2000000000)) / 8 = -(48912057 / 64000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.55`, every
`n ≥ 30750`** (exponents `τ_+ = 0.089358`, `τ_- = -0.221685`; `E_+ ≤ −0.000212188`,
`E_- ≤ −0.00019883`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.55/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_455 {n : ℕ} (hn : 30750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (455 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 30750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_455 Em_455 (by norm_num) (by norm_num) up_455 um_455 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.6`: `τ_+ = 0.088633`, `τ_- = -0.219648`, `n₀ = 31000` -/

lemma Ep_460 : Eplus aL (hAL + dsL) hWL cWL (460 / 100) (88633 / 1000000) ≤ -(32883 / 156250000 : ℝ) := by
  have e : (88633 / 1000000 : ℝ) * cWL = 122047641 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 564903962839 / 500000000000) (y := 11198597 / 25000000) (ehi := 156509086029 / 100000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_460 : Eminus aL (hAL + dsL) hWL cWL (460 / 100) (-(3432 / 15625)) ≤ -(985363 / 5000000000 : ℝ) := by
  have e : (-(3432 / 15625) : ℝ) * cWL = -(590733 / 1953125) := by unfold cWL; norm_num
  have e2 : (-(20920081 / 25000000) : ℝ) / 2 = -(20920081 / 50000000) := by norm_num
  refine certM (eLo := 184750380961 / 250000000000) (eHi := 147800304769 / 200000000000) (y := -(20920081 / 25000000)) (u := 658097870077 / 1000000000000)
    (ehi := 2165464033 / 5000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_460 : exp (-(((31000 : ℕ) : ℝ) * (32883 / 156250000)) / 8) ≤ (4424187709 / 10000000000 : ℝ) := by
  have e : -(((31000 : ℕ) : ℝ) * (32883 / 156250000)) / 8 = -(1019373 / 1250000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_460 : exp (-(((31000 : ℕ) : ℝ) * (985363 / 5000000000)) / 8) ≤ (4659596089 / 10000000000 : ℝ) := by
  have e : -(((31000 : ℕ) : ℝ) * (985363 / 5000000000)) / 8 = -(30546253 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.6`, every
`n ≥ 31000`** (exponents `τ_+ = 0.088633`, `τ_- = -0.219648`; `E_+ ≤ −0.000210451`,
`E_- ≤ −0.000197073`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.6/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_460 {n : ℕ} (hn : 31000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (460 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 31000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_460 Em_460 (by norm_num) (by norm_num) up_460 um_460 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.45`: `τ_+ = 0.090844`, `τ_- = -0.22587`, `n₀ = 30250` -/

lemma Ep_445 : Eplus aL (hAL + dsL) hWL cWL (445 / 100) (22711 / 250000) ≤ -(2157511 / 10000000000 : ℝ) := by
  have e : (22711 / 250000 : ℝ) * cWL = 31273047 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 283313230143 / 250000000000) (y := 22241871 / 50000000) (ehi := 39005912799 / 25000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_445 : Eminus aL (hAL + dsL) hWL cWL (445 / 100) (-(22587 / 100000)) ≤ -(126523 / 625000000 : ℝ) := by
  have e : (-(22587 / 100000) : ℝ) * cWL = -(31102299 / 100000000) := by unfold cWL; norm_num
  have e2 : (-(20726757 / 25000000) : ℝ) / 2 = -(20726757 / 50000000) := by norm_num
  refine certM (eLo := 73269703097 / 100000000000) (eHi := 183174257743 / 250000000000) (y := -(20726757 / 25000000)) (u := 82580914731 / 125000000000)
    (ehi := 21822743929 / 50000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_445 : exp (-(((30250 : ℕ) : ℝ) * (2157511 / 10000000000)) / 8) ≤ (4422814447 / 10000000000 : ℝ) := by
  have e : -(((30250 : ℕ) : ℝ) * (2157511 / 10000000000)) / 8 = -(261058831 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_445 : exp (-(((30250 : ℕ) : ℝ) * (126523 / 625000000)) / 8) ≤ (1162794991 / 2500000000 : ℝ) := by
  have e : -(((30250 : ℕ) : ℝ) * (126523 / 625000000)) / 8 = -(15309283 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.45`, every
`n ≥ 30250`** (exponents `τ_+ = 0.090844`, `τ_- = -0.22587`; `E_+ ≤ −0.000215751`,
`E_- ≤ −0.000202437`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.45/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_445 {n : ℕ} (hn : 30250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (445 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 30250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_445 Em_445 (by norm_num) (by norm_num) up_445 um_445 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_565
open BstLean.Part160 in
#print axioms classifier_frame_560
open BstLean.Part160 in
#print axioms classifier_frame_570
open BstLean.Part160 in
#print axioms classifier_frame_455
open BstLean.Part160 in
#print axioms classifier_frame_460
open BstLean.Part160 in
#print axioms classifier_frame_445
