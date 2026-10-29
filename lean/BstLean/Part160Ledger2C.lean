import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2C`): ledger certificates, frame constants 8.5, 9, 10.6, 18

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `8.5`: `τ_+ = 0.054405`, `τ_- = -0.127096`, `n₀ = 52000` -/

lemma Ep_85 : Eplus aL (hAL + dsL) hWL cWL (17 / 2) (10881 / 200000) ≤ -(643133 / 5000000000 : ℝ) := by
  have e : (10881 / 200000 : ℝ) * cWL = 14983137 / 200000000 := by unfold cWL; norm_num
  refine certP (eT := 538896636457 / 500000000000) (y := 49605009 / 100000000) (ehi := 32844436293 / 20000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_85 : Eminus aL (hAL + dsL) hWL cWL (17 / 2) (-(15887 / 125000)) ≤ -(290597 / 2500000000 : ℝ) := by
  have e : (-(15887 / 125000) : ℝ) * cWL = -(21876399 / 125000000) := by unfold cWL; norm_num
  have e2 : (-(9511811 / 10000000) : ℝ) / 2 = -(9511811 / 20000000) := by norm_num
  refine certM (eLo := 419723812809 / 500000000000) (eHi := 839447625619 / 1000000000000) (y := -(9511811 / 10000000)) (u := 124303582133 / 200000000000)
    (ehi := 193142256639 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_85 : exp (-(((52000 : ℕ) : ℝ) * (643133 / 5000000000)) / 8) ≤ (270880767 / 625000000 : ℝ) := by
  have e : -(((52000 : ℕ) : ℝ) * (643133 / 5000000000)) / 8 = -(8360729 / 10000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_85 : exp (-(((52000 : ℕ) : ℝ) * (290597 / 2500000000)) / 8) ≤ (2348755733 / 5000000000 : ℝ) := by
  have e : -(((52000 : ℕ) : ℝ) * (290597 / 2500000000)) / 8 = -(3777761 / 5000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `8.5`, every
`n ≥ 52000`** (exponents `τ_+ = 0.054405`, `τ_- = -0.127096`; `E_+ ≤ −0.000128627`,
`E_- ≤ −0.000116239`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `8.5/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_85 {n : ℕ} (hn : 52000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (17 / 2 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 52000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_85 Em_85 (by norm_num) (by norm_num) up_85 um_85 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `9.0`: `τ_+ = 0.051847`, `τ_- = -0.120521`, `n₀ = 54500` -/

lemma Ep_9 : Eplus aL (hAL + dsL) hWL cWL (9) (51847 / 1000000) ≤ -(1225337 / 10000000000 : ℝ) := by
  have e : (51847 / 1000000 : ℝ) * cWL = 71393319 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 214800713763 / 200000000000) (y := 12491073 / 25000000) (ehi := 206016581301 / 125000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_9 : Eminus aL (hAL + dsL) hWL cWL (9) (-(120521 / 1000000)) ≤ -(552009 / 5000000000 : ℝ) := by
  have e : (-(120521 / 1000000) : ℝ) * cWL = -(165957417 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(23981029 / 25000000) : ℝ) / 2 = -(23981029 / 50000000) := by norm_num
  refine certM (eLo := 847082304727 / 1000000000000) (eHi := 105885288091 / 125000000000) (y := -(23981029 / 25000000)) (u := 619018215147 / 1000000000000)
    (ehi := 95795887671 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_9 : exp (-(((54500 : ℕ) : ℝ) * (1225337 / 10000000000)) / 8) ≤ (4339782631 / 10000000000 : ℝ) := by
  have e : -(((54500 : ℕ) : ℝ) * (1225337 / 10000000000)) / 8 = -(133561733 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_9 : exp (-(((54500 : ℕ) : ℝ) * (552009 / 5000000000)) / 8) ≤ (4713698437 / 10000000000 : ℝ) := by
  have e : -(((54500 : ℕ) : ℝ) * (552009 / 5000000000)) / 8 = -(60168981 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `9.0`, every
`n ≥ 54500`** (exponents `τ_+ = 0.051847`, `τ_- = -0.120521`; `E_+ ≤ −0.000122534`,
`E_- ≤ −0.000110402`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `9.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_9 {n : ℕ} (hn : 54500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (9 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 54500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_9 Em_9 (by norm_num) (by norm_num) up_9 um_9 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `10.6`: `τ_+ = 0.045071`, `τ_- = -0.103376`, `n₀ = 63500` -/

lemma Ep_106 : Eplus aL (hAL + dsL) hWL cWL (53 / 5) (45071 / 1000000) ≤ -(532067 / 5000000000 : ℝ) := by
  have e : (45071 / 1000000 : ℝ) * cWL = 62062767 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 1064029128549 / 1000000000000) (y := 25457633 / 50000000) (ehi := 415970181191 / 250000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_106 : Eminus aL (hAL + dsL) hWL cWL (53 / 5) (-(6461 / 62500)) ≤ -(475507 / 5000000000 : ℝ) := by
  have e : (-(6461 / 62500) : ℝ) * cWL = -(8896797 / 62500000) := by unfold cWL; norm_num
  have e2 : (-(122533 / 125000) : ℝ) / 2 = -(122533 / 250000) := by norm_num
  refine certM (eLo := 433659362297 / 500000000000) (eHi := 173463744919 / 200000000000) (y := -(122533 / 125000)) (u := 306272766419 / 500000000000)
    (ehi := 1876060149 / 5000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_106 : exp (-(((63500 : ℕ) : ℝ) * (532067 / 5000000000)) / 8) ≤ (1074262489 / 2500000000 : ℝ) := by
  have e : -(((63500 : ℕ) : ℝ) * (532067 / 5000000000)) / 8 = -(67572509 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_106 : exp (-(((63500 : ℕ) : ℝ) * (475507 / 5000000000)) / 8) ≤ (4700729599 / 10000000000 : ℝ) := by
  have e : -(((63500 : ℕ) : ℝ) * (475507 / 5000000000)) / 8 = -(60389389 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `10.6`, every
`n ≥ 63500`** (exponents `τ_+ = 0.045071`, `τ_- = -0.103376`; `E_+ ≤ −0.000106413`,
`E_- ≤ −9.51014e-05`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `10.6/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_106 {n : ℕ} (hn : 63500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (53 / 5 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 63500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_106 Em_106 (by norm_num) (by norm_num) up_106 um_106 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `18.0`: `τ_+ = 0.028112`, `τ_- = -0.062236`, `n₀ = 103000` -/

lemma Ep_18 : Eplus aL (hAL + dsL) hWL cWL (18) (1757 / 62500) ≤ -(4137 / 62500000 : ℝ) := by
  have e : (1757 / 62500 : ℝ) * cWL = 2419389 / 62500000 := by unfold cWL; norm_num
  refine certP (eT := 103946922677 / 100000000000) (y := 53296131 / 100000000) (ehi := 425992707621 / 250000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_18 : Eminus aL (hAL + dsL) hWL cWL (18) (-(15559 / 250000)) ≤ -(578973 / 10000000000 : ℝ) := by
  have e : (-(15559 / 250000) : ℝ) * cWL = -(21424743 / 250000000) := by unfold cWL; norm_num
  have e2 : (-(51519219 / 50000000) : ℝ) / 2 = -(51519219 / 100000000) := by norm_num
  refine certM (eLo := 183574098871 / 200000000000) (eHi := 229467623589 / 250000000000) (y := -(51519219 / 50000000)) (u := 298692886007 / 500000000000)
    (ehi := 71373952121 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_18 : exp (-(((103000 : ℕ) : ℝ) * (4137 / 62500000)) / 8) ≤ (266541419 / 625000000 : ℝ) := by
  have e : -(((103000 : ℕ) : ℝ) * (4137 / 62500000)) / 8 = -(426111 / 500000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_18 : exp (-(((103000 : ℕ) : ℝ) * (578973 / 10000000000)) / 8) ≤ (4745312817 / 10000000000 : ℝ) := by
  have e : -(((103000 : ℕ) : ℝ) * (578973 / 10000000000)) / 8 = -(59634219 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `18.0`, every
`n ≥ 103000`** (exponents `τ_+ = 0.028112`, `τ_- = -0.062236`; `E_+ ≤ −6.6192e-05`,
`E_- ≤ −5.78973e-05`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `18.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_18 {n : ℕ} (hn : 103000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (18 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 103000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_18 Em_18 (by norm_num) (by norm_num) up_18 um_18 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_85
open BstLean.Part160 in
#print axioms classifier_frame_9
open BstLean.Part160 in
#print axioms classifier_frame_106
open BstLean.Part160 in
#print axioms classifier_frame_18
