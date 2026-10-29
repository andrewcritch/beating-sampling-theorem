import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2I`): ledger certificates, frame constants 3.20 to 3.00

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `3.2`: `τ_+ = 0.114804`, `τ_- = -0.294413`, `n₀ = 23750` -/

lemma Ep_320 : Eplus aL (hAL + dsL) hWL cWL (320 / 100) (28701 / 250000) ≤ -(546533 / 2000000000 : ℝ) := by
  have e : (28701 / 250000 : ℝ) * cWL = 39521277 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 585632937281 / 500000000000) (y := 10278397 / 25000000) (ehi := 1508530321733 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_320 : Eminus aL (hAL + dsL) hWL cWL (320 / 100) (-(294413 / 1000000)) ≤ -(2612593 / 10000000000 : ℝ) := by
  have e : (-(294413 / 1000000) : ℝ) * cWL = -(405406701 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(74337087 / 100000000) : ℝ) / 2 = -(74337087 / 200000000) := by norm_num
  refine certM (eLo := 5333644847 / 8000000000) (eHi := 166676401469 / 250000000000) (y := -(74337087 / 100000000)) (u := 86196390419 / 125000000000)
    (ehi := 475508334161 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_320 : exp (-(((23750 : ℕ) : ℝ) * (546533 / 2000000000)) / 8) ≤ (4338847 / 9765625 : ℝ) := by
  have e : -(((23750 : ℕ) : ℝ) * (546533 / 2000000000)) / 8 = -(10384127 / 12800000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_320 : exp (-(((23750 : ℕ) : ℝ) * (2612593 / 10000000000)) / 8) ≤ (1151053011 / 2500000000 : ℝ) := by
  have e : -(((23750 : ℕ) : ℝ) * (2612593 / 10000000000)) / 8 = -(49639267 / 64000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.2`, every
`n ≥ 23750`** (exponents `τ_+ = 0.114804`, `τ_- = -0.294413`; `E_+ ≤ −0.000273266`,
`E_- ≤ −0.000261259`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.2/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_320 {n : ℕ} (hn : 23750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (320 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 23750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_320 Em_320 (by norm_num) (by norm_num) up_320 um_320 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.15`: `τ_+ = 0.116034`, `τ_- = -0.297971`, `n₀ = 23500` -/

lemma Ep_315 : Eplus aL (hAL + dsL) hWL cWL (315 / 100) (58017 / 500000) ≤ -(110489 / 400000000 : ℝ) := by
  have e : (58017 / 500000 : ℝ) * cWL = 79889409 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 586625670107 / 500000000000) (y := 20470183 / 50000000) (ehi := 1505919477271 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_315 : Eminus aL (hAL + dsL) hWL cWL (315 / 100) (-(297971 / 1000000)) ≤ -(660757 / 2500000000 : ℝ) := by
  have e : (-(297971 / 1000000) : ℝ) * cWL = -(410306067 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(7389097 / 10000000) : ℝ) / 2 = -(7389097 / 20000000) := by norm_num
  refine certM (eLo := 20732723743 / 31250000000) (eHi := 663447159777 / 1000000000000) (y := -(7389097 / 10000000)) (u := 172777746779 / 250000000000)
    (ehi := 477634396513 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_315 : exp (-(((23500 : ℕ) : ℝ) * (110489 / 400000000)) / 8) ≤ (4442341043 / 10000000000 : ℝ) := by
  have e : -(((23500 : ℕ) : ℝ) * (110489 / 400000000)) / 8 = -(5192983 / 6400000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_315 : exp (-(((23500 : ℕ) : ℝ) * (660757 / 2500000000)) / 8) ≤ (1150160223 / 2500000000 : ℝ) := by
  have e : -(((23500 : ℕ) : ℝ) * (660757 / 2500000000)) / 8 = -(31055579 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.15`, every
`n ≥ 23500`** (exponents `τ_+ = 0.116034`, `τ_- = -0.297971`; `E_+ ≤ −0.000276223`,
`E_- ≤ −0.000264303`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.15/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_315 {n : ℕ} (hn : 23500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (315 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 23500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_315 Em_315 (by norm_num) (by norm_num) up_315 um_315 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.1`: `τ_+ = 0.117292`, `τ_- = -0.301607`, `n₀ = 23250` -/

lemma Ep_310 : Eplus aL (hAL + dsL) hWL cWL (310 / 100) (29323 / 250000) ≤ -(2792441 / 10000000000 : ℝ) := by
  have e : (29323 / 250000 : ℝ) * cWL = 40377771 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 1175285484951 / 1000000000000) (y := 4076357 / 10000000) (ehi := 751629711999 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_310 : Eminus aL (hAL + dsL) hWL cWL (310 / 100) (-(301607 / 1000000)) ≤ -(53483 / 200000000 : ℝ) := by
  have e : (-(301607 / 1000000) : ℝ) * cWL = -(415312839 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(73434021 / 100000000) : ℝ) / 2 = -(73434021 / 200000000) := by norm_num
  refine certM (eLo := 660133732821 / 1000000000000) (eHi := 330066866411 / 500000000000) (y := -(73434021 / 100000000)) (u := 692691804683 / 1000000000000)
    (ehi := 19192877451 / 40000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_310 : exp (-(((23250 : ℕ) : ℝ) * (2792441 / 10000000000)) / 8) ≤ (4441676643 / 10000000000 : ℝ) := by
  have e : -(((23250 : ℕ) : ℝ) * (2792441 / 10000000000)) / 8 = -(259697013 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_310 : exp (-(((23250 : ℕ) : ℝ) * (53483 / 200000000)) / 8) ≤ (4597029111 / 10000000000 : ℝ) := by
  have e : -(((23250 : ℕ) : ℝ) * (53483 / 200000000)) / 8 = -(4973919 / 6400000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.1`, every
`n ≥ 23250`** (exponents `τ_+ = 0.117292`, `τ_- = -0.301607`; `E_+ ≤ −0.000279244`,
`E_- ≤ −0.000267415`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.1/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_310 {n : ℕ} (hn : 23250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (310 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 23250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_310 Em_310 (by norm_num) (by norm_num) up_310 um_310 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.05`: `τ_+ = 0.118578`, `τ_- = -0.305327`, `n₀ = 23000` -/

lemma Ep_305 : Eplus aL (hAL + dsL) hWL cWL (305 / 100) (59289 / 500000) ≤ -(2823337 / 10000000000 : ℝ) := by
  have e : (59289 / 500000 : ℝ) * cWL = 81640953 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 1177368550169 / 1000000000000) (y := 10145677 / 25000000) (ehi := 750271528059 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_305 : Eminus aL (hAL + dsL) hWL cWL (305 / 100) (-(305327 / 1000000)) ≤ -(1352991 / 5000000000 : ℝ) := by
  have e : (-(305327 / 1000000) : ℝ) * cWL = -(420435279 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(7296661 / 10000000) : ℝ) / 2 = -(7296661 / 20000000) := by norm_num
  refine certM (eLo := 656760883367 / 1000000000000) (eHi := 656760883369 / 1000000000000) (y := -(7296661 / 10000000)) (u := 173578139171 / 250000000000)
    (ehi := 48206992637 / 100000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_305 : exp (-(((23000 : ℕ) : ℝ) * (2823337 / 10000000000)) / 8) ≤ (444098281 / 1000000000 : ℝ) := by
  have e : -(((23000 : ℕ) : ℝ) * (2823337 / 10000000000)) / 8 = -(64936751 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_305 : exp (-(((23000 : ℕ) : ℝ) * (1352991 / 5000000000)) / 8) ≤ (4593376011 / 10000000000 : ℝ) := by
  have e : -(((23000 : ℕ) : ℝ) * (1352991 / 5000000000)) / 8 = -(31118793 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.05`, every
`n ≥ 23000`** (exponents `τ_+ = 0.118578`, `τ_- = -0.305327`; `E_+ ≤ −0.000282334`,
`E_- ≤ −0.000270598`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.05/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_305 {n : ℕ} (hn : 23000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (305 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 23000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_305 Em_305 (by norm_num) (by norm_num) up_305 um_305 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.0`: `τ_+ = 0.119893`, `τ_- = -0.309131`, `n₀ = 22750` -/

lemma Ep_300 : Eplus aL (hAL + dsL) hWL cWL (300 / 100) (119893 / 1000000) ≤ -(356867 / 1250000000 : ℝ) := by
  have e : (119893 / 1000000 : ℝ) * cWL = 165092661 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 1179502407521 / 1000000000000) (y := 807953 / 2000000) (ehi := 74888437449 / 50000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_300 : Eminus aL (hAL + dsL) hWL cWL (300 / 100) (-(309131 / 1000000)) ≤ -(2738547 / 10000000000 : ℝ) := by
  have e : (-(309131 / 1000000) : ℝ) * cWL = -(425673387 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(72487889 / 100000000) : ℝ) / 2 = -(72487889 / 200000000) := by norm_num
  refine certM (eLo := 10208276457 / 15625000000) (eHi := 653329693249 / 1000000000000) (y := -(72487889 / 100000000)) (u := 347988228629 / 500000000000)
    (ehi := 242191614529 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_300 : exp (-(((22750 : ℕ) : ℝ) * (356867 / 1250000000)) / 8) ≤ (4440258823 / 10000000000 : ℝ) := by
  have e : -(((22750 : ℕ) : ℝ) * (356867 / 1250000000)) / 8 = -(32474897 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_300 : exp (-(((22750 : ℕ) : ℝ) * (2738547 / 10000000000)) / 8) ≤ (4589682227 / 10000000000 : ℝ) := by
  have e : -(((22750 : ℕ) : ℝ) * (2738547 / 10000000000)) / 8 = -(249207777 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.0`, every
`n ≥ 22750`** (exponents `τ_+ = 0.119893`, `τ_- = -0.309131`; `E_+ ≤ −0.000285494`,
`E_- ≤ −0.000273855`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_300 {n : ℕ} (hn : 22750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (300 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 22750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_300 Em_300 (by norm_num) (by norm_num) up_300 um_300 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_320
open BstLean.Part160 in
#print axioms classifier_frame_315
open BstLean.Part160 in
#print axioms classifier_frame_310
open BstLean.Part160 in
#print axioms classifier_frame_305
open BstLean.Part160 in
#print axioms classifier_frame_300
