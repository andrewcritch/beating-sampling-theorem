import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2F`): ledger certificates, frame constants 3.95 to 3.75

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `3.95`: `τ_+ = 0.099096`, `τ_- = -0.249275`, `n₀ = 27750` -/

lemma Ep_395 : Eplus aL (hAL + dsL) hWL cWL (395 / 100) (12387 / 125000) ≤ -(235547 / 1000000000 : ℝ) := by
  have e : (12387 / 125000 : ℝ) * cWL = 17056899 / 125000000 := by unfold cWL; norm_num
  refine certP (eT := 573101758769 / 500000000000) (y := 5415387 / 12500000) (ehi := 38555809339 / 25000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_395 : Eminus aL (hAL + dsL) hWL cWL (395 / 100) (-(9971 / 40000)) ≤ -(55643 / 250000000 : ℝ) := by
  have e : (-(9971 / 40000) : ℝ) * cWL = -(13730067 / 40000000) := by unfold cWL; norm_num
  have e2 : (-(39994579 / 50000000) : ℝ) / 2 = -(39994579 / 100000000) := by norm_num
  refine certM (eLo := 141891927167 / 200000000000) (eHi := 177364908959 / 250000000000) (y := -(39994579 / 50000000)) (u := 670356385071 / 1000000000000)
    (ehi := 224688841503 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_395 : exp (-(((27750 : ℕ) : ℝ) * (235547 / 1000000000)) / 8) ≤ (552164039 / 1250000000 : ℝ) := by
  have e : -(((27750 : ℕ) : ℝ) * (235547 / 1000000000)) / 8 = -(26145717 / 32000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_395 : exp (-(((27750 : ℕ) : ℝ) * (55643 / 250000000)) / 8) ≤ (4620664233 / 10000000000 : ℝ) := by
  have e : -(((27750 : ℕ) : ℝ) * (55643 / 250000000)) / 8 = -(6176373 / 8000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.95`, every
`n ≥ 27750`** (exponents `τ_+ = 0.099096`, `τ_- = -0.249275`; `E_+ ≤ −0.000235547`,
`E_- ≤ −0.000222572`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.95/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_395 {n : ℕ} (hn : 27750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (395 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 27750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_395 Em_395 (by norm_num) (by norm_num) up_395 um_395 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.9`: `τ_+ = 0.100006`, `τ_- = -0.25187`, `n₀ = 27500` -/

lemma Ep_390 : Eplus aL (hAL + dsL) hWL cWL (390 / 100) (50003 / 500000) ≤ -(594327 / 2500000000 : ℝ) := by
  have e : (50003 / 500000 : ℝ) * cWL = 68854131 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 143455086379 / 125000000000) (y := 1727807 / 4000000) (ehi := 308052159157 / 200000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_390 : Eminus aL (hAL + dsL) hWL cWL (390 / 100) (-(25187 / 100000)) ≤ -(140501 / 625000000 : ℝ) := by
  have e : (-(25187 / 100000) : ℝ) * cWL = -(34682499 / 100000000) := by unfold cWL; norm_num
  have e2 : (-(79664521 / 100000000) : ℝ) / 2 = -(79664521 / 200000000) := by norm_num
  refine certM (eLo := 706929037083 / 1000000000000) (eHi := 176732259271 / 250000000000) (y := -(79664521 / 100000000)) (u := 335722690541 / 500000000000)
    (ehi := 450838899777 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_390 : exp (-(((27500 : ℕ) : ℝ) * (594327 / 2500000000)) / 8) ≤ (4416667569 / 10000000000 : ℝ) := by
  have e : -(((27500 : ℕ) : ℝ) * (594327 / 2500000000)) / 8 = -(6537597 / 8000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_390 : exp (-(((27500 : ℕ) : ℝ) * (140501 / 625000000)) / 8) ≤ (28858687 / 62500000 : ℝ) := by
  have e : -(((27500 : ℕ) : ℝ) * (140501 / 625000000)) / 8 = -(1545511 / 2000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.9`, every
`n ≥ 27500`** (exponents `τ_+ = 0.100006`, `τ_- = -0.25187`; `E_+ ≤ −0.000237731`,
`E_- ≤ −0.000224802`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.9/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_390 {n : ℕ} (hn : 27500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (390 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 27500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_390 Em_390 (by norm_num) (by norm_num) up_390 um_390 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.85`: `τ_+ = 0.100933`, `τ_- = -0.254519`, `n₀ = 27250` -/

lemma Ep_385 : Eplus aL (hAL + dsL) hWL cWL (385 / 100) (100933 / 1000000) ≤ -(1199779 / 5000000000 : ℝ) := by
  have e : (100933 / 1000000 : ℝ) * cWL = 138984741 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 1149106565653 / 1000000000000) (y := 43064763 / 100000000) (ehi := 153825342009 / 100000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_385 : Eminus aL (hAL + dsL) hWL cWL (385 / 100) (-(254519 / 1000000)) ≤ -(2270751 / 10000000000 : ℝ) := by
  have e : (-(254519 / 1000000) : ℝ) * cWL = -(350472663 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(79333879 / 100000000) : ℝ) / 2 = -(79333879 / 200000000) := by norm_num
  refine certM (eLo := 704355088437 / 1000000000000) (eHi := 352177544219 / 500000000000) (y := -(79333879 / 100000000)) (u := 672556339371 / 1000000000000)
    (ehi := 452332029629 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_385 : exp (-(((27250 : ℕ) : ℝ) * (1199779 / 5000000000)) / 8) ≤ (4416005919 / 10000000000 : ℝ) := by
  have e : -(((27250 : ℕ) : ℝ) * (1199779 / 5000000000)) / 8 = -(130775911 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_385 : exp (-(((27250 : ℕ) : ℝ) * (2270751 / 10000000000)) / 8) ≤ (576758867 / 1250000000 : ℝ) := by
  have e : -(((27250 : ℕ) : ℝ) * (2270751 / 10000000000)) / 8 = -(247511859 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.85`, every
`n ≥ 27250`** (exponents `τ_+ = 0.100933`, `τ_- = -0.254519`; `E_+ ≤ −0.000239956`,
`E_- ≤ −0.000227075`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.85/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_385 {n : ℕ} (hn : 27250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (385 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 27250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_385 Em_385 (by norm_num) (by norm_num) up_385 um_385 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.8`: `τ_+ = 0.101878`, `τ_- = -0.257222`, `n₀ = 26750` -/

lemma Ep_380 : Eplus aL (hAL + dsL) hWL cWL (380 / 100) (50939 / 500000) ≤ -(484447 / 2000000000 : ℝ) := by
  have e : (50939 / 500000 : ℝ) * cWL = 70143003 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 287650707779 / 250000000000) (y := 42932017 / 100000000) (ehi := 768106402461 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_380 : Eminus aL (hAL + dsL) hWL cWL (380 / 100) (-(128611 / 500000)) ≤ -(143371 / 625000000 : ℝ) := by
  have e : (-(128611 / 500000) : ℝ) * cWL = -(177097347 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(15799327 / 20000000) : ℝ) / 2 = -(15799327 / 40000000) := by norm_num
  refine certM (eLo := 175434582453 / 250000000000) (eHi := 701738329813 / 1000000000000) (y := -(15799327 / 20000000)) (u := 673691374011 / 1000000000000)
    (ehi := 453860067417 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_380 : exp (-(((26750 : ℕ) : ℝ) * (484447 / 2000000000)) / 8) ≤ (889774119 / 2000000000 : ℝ) := by
  have e : -(((26750 : ℕ) : ℝ) * (484447 / 2000000000)) / 8 = -(51835829 / 64000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_380 : exp (-(((26750 : ℕ) : ℝ) * (143371 / 625000000)) / 8) ≤ (464388009 / 1000000000 : ℝ) := by
  have e : -(((26750 : ℕ) : ℝ) * (143371 / 625000000)) / 8 = -(15340697 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.8`, every
`n ≥ 26750`** (exponents `τ_+ = 0.101878`, `τ_- = -0.257222`; `E_+ ≤ −0.000242223`,
`E_- ≤ −0.000229394`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.8/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_380 {n : ℕ} (hn : 26750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (380 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 26750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_380 Em_380 (by norm_num) (by norm_num) up_380 um_380 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.75`: `τ_+ = 0.102841`, `τ_- = -0.259979`, `n₀ = 26500` -/

lemma Ep_375 : Eplus aL (hAL + dsL) hWL cWL (375 / 100) (102841 / 1000000) ≤ -(48907 / 200000000 : ℝ) := by
  have e : (102841 / 1000000 : ℝ) * cWL = 141612057 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 230425920243 / 200000000000) (y := 42796629 / 100000000) (ehi := 1534134364427 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_375 : Eminus aL (hAL + dsL) hWL cWL (375 / 100) (-(259979 / 1000000)) ≤ -(144849 / 625000000 : ℝ) := by
  have e : (-(259979 / 1000000) : ℝ) * cWL = -(357991083 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(78652199 / 100000000) : ℝ) / 2 = -(78652199 / 200000000) := by norm_num
  refine certM (eLo := 174769827167 / 250000000000) (eHi := 699079308669 / 1000000000000) (y := -(78652199 / 100000000)) (u := 84356573931 / 125000000000)
    (ehi := 91085204037 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_375 : exp (-(((26500 : ℕ) : ℝ) * (48907 / 200000000)) / 8) ≤ (4448481961 / 10000000000 : ℝ) := by
  have e : -(((26500 : ℕ) : ℝ) * (48907 / 200000000)) / 8 = -(2592071 / 3200000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_375 : exp (-(((26500 : ℕ) : ℝ) * (144849 / 625000000)) / 8) ≤ (4640793633 / 10000000000 : ℝ) := by
  have e : -(((26500 : ℕ) : ℝ) * (144849 / 625000000)) / 8 = -(7676997 / 10000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.75`, every
`n ≥ 26500`** (exponents `τ_+ = 0.102841`, `τ_- = -0.259979`; `E_+ ≤ −0.000244535`,
`E_- ≤ −0.000231758`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.75/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_375 {n : ℕ} (hn : 26500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (375 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 26500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_375 Em_375 (by norm_num) (by norm_num) up_375 um_375 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_395
open BstLean.Part160 in
#print axioms classifier_frame_390
open BstLean.Part160 in
#print axioms classifier_frame_385
open BstLean.Part160 in
#print axioms classifier_frame_380
open BstLean.Part160 in
#print axioms classifier_frame_375
