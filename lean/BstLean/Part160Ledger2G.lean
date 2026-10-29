import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2G`): ledger certificates, frame constants 3.70 to 3.50

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `3.7`: `τ_+ = 0.103823`, `τ_- = -0.26279`, `n₀ = 26250` -/

lemma Ep_370 : Eplus aL (hAL + dsL) hWL cWL (370 / 100) (103823 / 1000000) ≤ -(617229 / 2500000000 : ℝ) := by
  have e : (103823 / 1000000 : ℝ) * cWL = 142964271 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 1153688580791 / 1000000000000) (y := 42658727 / 100000000) (ehi := 766010110257 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_370 : Eminus aL (hAL + dsL) hWL cWL (370 / 100) (-(26279 / 100000)) ≤ -(234171 / 1000000000 : ℝ) := by
  have e : (-(26279 / 100000) : ℝ) * cWL = -(36186183 / 100000000) := by unfold cWL; norm_num
  have e2 : (-(39149993 / 50000000) : ℝ) / 2 = -(39149993 / 100000000) := by norm_num
  refine certM (eLo := 696378579823 / 1000000000000) (eHi := 43523661239 / 62500000000) (y := -(39149993 / 50000000)) (u := 338021048909 / 500000000000)
    (ehi := 457032918023 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_370 : exp (-(((26250 : ℕ) : ℝ) * (617229 / 2500000000)) / 8) ≤ (1112019431 / 2500000000 : ℝ) := by
  have e : -(((26250 : ℕ) : ℝ) * (617229 / 2500000000)) / 8 = -(12961809 / 16000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_370 : exp (-(((26250 : ℕ) : ℝ) * (234171 / 1000000000)) / 8) ≤ (1159416821 / 2500000000 : ℝ) := by
  have e : -(((26250 : ℕ) : ℝ) * (234171 / 1000000000)) / 8 = -(4917591 / 6400000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.7`, every
`n ≥ 26250`** (exponents `τ_+ = 0.103823`, `τ_- = -0.26279`; `E_+ ≤ −0.000246892`,
`E_- ≤ −0.000234171`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.7/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_370 {n : ℕ} (hn : 26250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (370 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 26250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_370 Em_370 (by norm_num) (by norm_num) up_370 um_370 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.65`: `τ_+ = 0.104823`, `τ_- = -0.265661`, `n₀ = 26000` -/

lemma Ep_365 : Eplus aL (hAL + dsL) hWL cWL (365 / 100) (104823 / 1000000) ≤ -(1246473 / 5000000000 : ℝ) := by
  have e : (104823 / 1000000 : ℝ) * cWL = 144341271 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 14440978803 / 12500000000) (y := 10629387 / 25000000) (ehi := 1529858855743 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_365 : Eminus aL (hAL + dsL) hWL cWL (365 / 100) (-(265661 / 1000000)) ≤ -(2366327 / 10000000000 : ℝ) := by
  have e : (-(265661 / 1000000) : ℝ) * cWL = -(365815197 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(38970437 / 50000000) : ℝ) / 2 = -(38970437 / 100000000) := by norm_num
  refine certM (eLo := 13872619489 / 20000000000) (eHi := 173407743613 / 250000000000) (y := -(38970437 / 50000000)) (u := 169314265603 / 250000000000)
    (ehi := 458677128587 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_365 : exp (-(((26000 : ℕ) : ℝ) * (1246473 / 5000000000)) / 8) ≤ (44476579 / 100000000 : ℝ) := by
  have e : -(((26000 : ℕ) : ℝ) * (1246473 / 5000000000)) / 8 = -(16204149 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_365 : exp (-(((26000 : ℕ) : ℝ) * (2366327 / 10000000000)) / 8) ≤ (1158625579 / 2500000000 : ℝ) := by
  have e : -(((26000 : ℕ) : ℝ) * (2366327 / 10000000000)) / 8 = -(30762251 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.65`, every
`n ≥ 26000`** (exponents `τ_+ = 0.104823`, `τ_- = -0.265661`; `E_+ ≤ −0.000249295`,
`E_- ≤ −0.000236633`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.65/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_365 {n : ℕ} (hn : 26000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (365 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 26000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_365 Em_365 (by norm_num) (by norm_num) up_365 um_365 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.6`: `τ_+ = 0.105844`, `τ_- = -0.268592`, `n₀ = 25750` -/

lemma Ep_360 : Eplus aL (hAL + dsL) hWL cWL (360 / 100) (26461 / 250000) ≤ -(157341 / 625000000 : ℝ) := by
  have e : (26461 / 250000 : ℝ) * cWL = 36436797 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 578451835973 / 500000000000) (y := 42374069 / 100000000) (ehi := 1527665403503 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_360 : Eminus aL (hAL + dsL) hWL cWL (360 / 100) (-(16787 / 62500)) ≤ -(47829 / 200000000 : ℝ) := by
  have e : (-(16787 / 62500) : ℝ) * cWL = -(23115699 / 62500000) := by unfold cWL; norm_num
  have e2 : (-(38787107 / 50000000) : ℝ) / 2 = -(38787107 / 100000000) := by norm_num
  refine certM (eLo := 345418565303 / 500000000000) (eHi := 690837130607 / 1000000000000) (y := -(38787107 / 50000000)) (u := 678499816607 / 1000000000000)
    (ehi := 28772625071 / 62500000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_360 : exp (-(((25750 : ℕ) : ℝ) * (157341 / 625000000)) / 8) ≤ (2223609469 / 5000000000 : ℝ) := by
  have e : -(((25750 : ℕ) : ℝ) * (157341 / 625000000)) / 8 = -(16206123 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_360 : exp (-(((25750 : ℕ) : ℝ) * (47829 / 200000000)) / 8) ≤ (578912221 / 1250000000 : ℝ) := by
  have e : -(((25750 : ℕ) : ℝ) * (47829 / 200000000)) / 8 = -(4926387 / 6400000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.6`, every
`n ≥ 25750`** (exponents `τ_+ = 0.105844`, `τ_- = -0.268592`; `E_+ ≤ −0.000251746`,
`E_- ≤ −0.000239145`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.6/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_360 {n : ℕ} (hn : 25750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (360 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 25750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_360 Em_360 (by norm_num) (by norm_num) up_360 um_360 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.55`: `τ_+ = 0.106885`, `τ_- = -0.271583`, `n₀ = 25500` -/

lemma Ep_355 : Eplus aL (hAL + dsL) hWL cWL (355 / 100) (21377 / 200000) ≤ -(2542459 / 10000000000 : ℝ) := by
  have e : (21377 / 200000 : ℝ) * cWL = 29436129 / 200000000 := by unfold cWL; norm_num
  refine certP (eT := 1158563232783 / 1000000000000) (y := 2639219 / 6250000) (ehi := 305085604143 / 200000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_355 : Eminus aL (hAL + dsL) hWL cWL (355 / 100) (-(271583 / 1000000)) ≤ -(2417093 / 10000000000 : ℝ) := by
  have e : (-(271583 / 1000000) : ℝ) * cWL = -(373969791 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(77199361 / 100000000) : ℝ) / 2 = -(77199361 / 200000000) := by norm_num
  refine certM (eLo := 687997695237 / 1000000000000) (eHi := 343998847619 / 500000000000) (y := -(77199361 / 100000000)) (u := 679772697551 / 1000000000000)
    (ehi := 28880682521 / 62500000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_355 : exp (-(((25500 : ℕ) : ℝ) * (2542459 / 10000000000)) / 8) ≤ (4446762427 / 10000000000 : ℝ) := by
  have e : -(((25500 : ℕ) : ℝ) * (2542459 / 10000000000)) / 8 = -(129665409 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_355 : exp (-(((25500 : ℕ) : ℝ) * (2417093 / 10000000000)) / 8) ≤ (4628055027 / 10000000000 : ℝ) := by
  have e : -(((25500 : ℕ) : ℝ) * (2417093 / 10000000000)) / 8 = -(123271743 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.55`, every
`n ≥ 25500`** (exponents `τ_+ = 0.106885`, `τ_- = -0.271583`; `E_+ ≤ −0.000254246`,
`E_- ≤ −0.000241709`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.55/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_355 {n : ℕ} (hn : 25500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (355 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 25500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_355 Em_355 (by norm_num) (by norm_num) up_355 um_355 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.5`: `τ_+ = 0.107948`, `τ_- = -0.27464`, `n₀ = 25250` -/

lemma Ep_350 : Eplus aL (hAL + dsL) hWL cWL (350 / 100) (26987 / 250000) ≤ -(2567971 / 10000000000 : ℝ) := by
  have e : (26987 / 250000 : ℝ) * cWL = 37161099 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 1160260322629 / 1000000000000) (y := 21039171 / 50000000) (ehi := 1523154357913 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_350 : Eminus aL (hAL + dsL) hWL cWL (350 / 100) (-(3433 / 12500)) ≤ -(1221637 / 5000000000 : ℝ) := by
  have e : (-(3433 / 12500) : ℝ) * cWL = -(4727241 / 12500000) := by unfold cWL; norm_num
  have e2 : (-(76817061 / 100000000) : ℝ) / 2 = -(76817061 / 200000000) := by norm_num
  refine certM (eLo := 685107663553 / 1000000000000) (eHi := 342553831777 / 500000000000) (y := -(76817061 / 100000000)) (u := 340536662871 / 500000000000)
    (ehi := 231930437519 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_350 : exp (-(((25250 : ℕ) : ℝ) * (2567971 / 10000000000)) / 8) ≤ (1111571617 / 2500000000 : ℝ) := by
  have e : -(((25250 : ℕ) : ℝ) * (2567971 / 10000000000)) / 8 = -(259365071 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_350 : exp (-(((25250 : ℕ) : ℝ) * (1221637 / 5000000000)) / 8) ≤ (289048153 / 625000000 : ℝ) := by
  have e : -(((25250 : ℕ) : ℝ) * (1221637 / 5000000000)) / 8 = -(123385337 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.5`, every
`n ≥ 25250`** (exponents `τ_+ = 0.107948`, `τ_- = -0.27464`; `E_+ ≤ −0.000256797`,
`E_- ≤ −0.000244327`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.5/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_350 {n : ℕ} (hn : 25250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (350 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 25250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_350 Em_350 (by norm_num) (by norm_num) up_350 um_350 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_370
open BstLean.Part160 in
#print axioms classifier_frame_365
open BstLean.Part160 in
#print axioms classifier_frame_360
open BstLean.Part160 in
#print axioms classifier_frame_355
open BstLean.Part160 in
#print axioms classifier_frame_350
