import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2B`): ledger certificates, frame constants 4.5, 5.5, 6.5, 4, 7.5

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `4.5`: `τ_+ = 0.090095`, `τ_- = -0.223761`, `n₀ = 30500` -/

lemma Ep_45 : Eplus aL (hAL + dsL) hWL cWL (9 / 2) (18019 / 200000) ≤ -(534887 / 2500000000 : ℝ) := by
  have e : (18019 / 200000 : ℝ) * cWL = 24812163 / 200000000 := by unfold cWL; norm_num
  refine certP (eT := 566042358319 / 500000000000) (y := 44589197 / 100000000) (ehi := 1561882727229 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_45 : Eminus aL (hAL + dsL) hWL cWL (9 / 2) (-(223761 / 1000000)) ≤ -(2006173 / 10000000000 : ℝ) := by
  have e : (-(223761 / 1000000) : ℝ) * cWL = -(308118897 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(16634043 / 20000000) : ℝ) / 2 = -(16634043 / 40000000) := by norm_num
  refine certM (eLo := 91853492997 / 125000000000) (eHi := 734827943977 / 1000000000000) (y := -(16634043 / 20000000)) (u := 131955704137 / 200000000000)
    (ehi := 217653848179 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_45 : exp (-(((30500 : ℕ) : ℝ) * (534887 / 2500000000)) / 8) ≤ (4423284051 / 10000000000 : ℝ) := by
  have e : -(((30500 : ℕ) : ℝ) * (534887 / 2500000000)) / 8 = -(32628107 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_45 : exp (-(((30500 : ℕ) : ℝ) * (2006173 / 10000000000)) / 8) ≤ (2327010639 / 5000000000 : ℝ) := by
  have e : -(((30500 : ℕ) : ℝ) * (2006173 / 10000000000)) / 8 = -(122376553 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.5`, every
`n ≥ 30500`** (exponents `τ_+ = 0.090095`, `τ_- = -0.223761`; `E_+ ≤ −0.000213955`,
`E_- ≤ −0.000200617`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.5/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_45 {n : ℕ} (hn : 30500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (9 / 2 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 30500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_45 Em_45 (by norm_num) (by norm_num) up_45 um_45 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `5.5`: `τ_+ = 0.077362`, `τ_- = -0.188331`, `n₀ = 36000` -/

lemma Ep_55 : Eplus aL (hAL + dsL) hWL cWL (11 / 2) (38681 / 500000) ≤ -(1834523 / 10000000000 : ℝ) := by
  have e : (38681 / 500000 : ℝ) * cWL = 53263737 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 1112408488337 / 1000000000000) (y := 11594883 / 25000000) (ehi := 1590097475979 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_55 : Eminus aL (hAL + dsL) hWL cWL (11 / 2) (-(188331 / 1000000)) ≤ -(1699551 / 10000000000 : ℝ) := by
  have e : (-(188331 / 1000000) : ℝ) * cWL = -(259331787 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(87568743 / 100000000) : ℝ) / 2 = -(87568743 / 200000000) := by norm_num
  refine certM (eLo := 30862679387 / 40000000000) (eHi := 192891746169 / 250000000000) (y := -(87568743 / 100000000)) (u := 645426645479 / 1000000000000)
    (ehi := 83315110939 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_55 : exp (-(((36000 : ℕ) : ℝ) * (1834523 / 10000000000)) / 8) ≤ (2190002231 / 5000000000 : ℝ) := by
  have e : -(((36000 : ℕ) : ℝ) * (1834523 / 10000000000)) / 8 = -(16510707 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_55 : exp (-(((36000 : ℕ) : ℝ) * (1699551 / 10000000000)) / 8) ≤ (1163569903 / 2500000000 : ℝ) := by
  have e : -(((36000 : ℕ) : ℝ) * (1699551 / 10000000000)) / 8 = -(15295959 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `5.5`, every
`n ≥ 36000`** (exponents `τ_+ = 0.077362`, `τ_- = -0.188331`; `E_+ ≤ −0.000183452`,
`E_- ≤ −0.000169955`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `5.5/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_55 {n : ℕ} (hn : 36000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (11 / 2 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 36000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_55 Em_55 (by norm_num) (by norm_num) up_55 um_55 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `6.5`: `τ_+ = 0.067807`, `τ_- = -0.162381`, `n₀ = 41500` -/

lemma Ep_65 : Eplus aL (hAL + dsL) hWL cWL (13 / 2) (67807 / 1000000) ≤ -(401511 / 2500000000 : ℝ) := by
  have e : (67807 / 1000000 : ℝ) * cWL = 93370239 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 4288547397 / 3906250000) (y := 9544413 / 20000000) (ehi := 80579450097 / 50000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_65 : Eminus aL (hAL + dsL) hWL cWL (13 / 2) (-(162381 / 1000000)) ≤ -(736627 / 5000000000 : ℝ) := by
  have e : (-(162381 / 1000000) : ℝ) * cWL = -(223598637 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(90773811 / 100000000) : ℝ) / 2 = -(90773811 / 200000000) := by norm_num
  refine certM (eLo := 799636014279 / 1000000000000) (eHi := 799636014281 / 1000000000000) (y := -(90773811 / 100000000)) (u := 1587914749 / 2500000000)
    (ehi := 80687144003 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_65 : exp (-(((41500 : ℕ) : ℝ) * (401511 / 2500000000)) / 8) ≤ (4346842711 / 10000000000 : ℝ) := by
  have e : -(((41500 : ℕ) : ℝ) * (401511 / 2500000000)) / 8 = -(33325413 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_65 : exp (-(((41500 : ℕ) : ℝ) * (736627 / 5000000000)) / 8) ≤ (4656828237 / 10000000000 : ℝ) := by
  have e : -(((41500 : ℕ) : ℝ) * (736627 / 5000000000)) / 8 = -(61140041 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `6.5`, every
`n ≥ 41500`** (exponents `τ_+ = 0.067807`, `τ_- = -0.162381`; `E_+ ≤ −0.000160604`,
`E_- ≤ −0.000147325`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `6.5/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_65 {n : ℕ} (hn : 41500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (13 / 2 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 41500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_65 Em_65 (by norm_num) (by norm_num) up_65 um_65 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.0`: `τ_+ = 0.098203`, `τ_- = -0.246726`, `n₀ = 28000` -/

lemma Ep_4 : Eplus aL (hAL + dsL) hWL cWL (4) (98203 / 1000000) ≤ -(583509 / 2500000000 : ℝ) := by
  have e : (98203 / 1000000 : ℝ) * cWL = 135225531 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 286198735497 / 250000000000) (y := 2715551 / 6250000) (ehi := 7720862437 / 5000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_4 : Eminus aL (hAL + dsL) hWL cWL (4) (-(123363 / 500000)) ≤ -(2203849 / 10000000000 : ℝ) := by
  have e : (-(123363 / 500000) : ℝ) * cWL = -(169870851 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(20076551 / 25000000) : ℝ) / 2 = -(20076551 / 50000000) := by norm_num
  refine certM (eLo := 711954195359 / 1000000000000) (eHi := 4449713721 / 6250000000) (y := -(20076551 / 25000000)) (u := 669294557861 / 1000000000000)
    (ehi := 447955205183 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_4 : exp (-(((28000 : ℕ) : ℝ) * (583509 / 2500000000)) / 8) ≤ (883587089 / 2000000000 : ℝ) := by
  have e : -(((28000 : ℕ) : ℝ) * (583509 / 2500000000)) / 8 = -(4084563 / 5000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_4 : exp (-(((28000 : ℕ) : ℝ) * (2203849 / 10000000000)) / 8) ≤ (4623897403 / 10000000000 : ℝ) := by
  have e : -(((28000 : ℕ) : ℝ) * (2203849 / 10000000000)) / 8 = -(15426943 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.0`, every
`n ≥ 28000`** (exponents `τ_+ = 0.098203`, `τ_- = -0.246726`; `E_+ ≤ −0.000233404`,
`E_- ≤ −0.000220385`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.0/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_4 {n : ℕ} (hn : 28000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (4 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 28000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_4 Em_4 (by norm_num) (by norm_num) up_4 um_4 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `7.5`: `τ_+ = 0.060366`, `τ_- = -0.142621`, `n₀ = 46500` -/

lemma Ep_75 : Eplus aL (hAL + dsL) hWL cWL (15 / 2) (30183 / 500000) ≤ -(714199 / 5000000000 : ℝ) := by
  have e : (30183 / 500000 : ℝ) * cWL = 41561991 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 1086676528527 / 1000000000000) (y := 24383573 / 50000000) (ehi := 814259864101 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_75 : Eminus aL (hAL + dsL) hWL cWL (15 / 2) (-(142621 / 1000000)) ≤ -(324913 / 2500000000 : ℝ) := by
  have e : (-(142621 / 1000000) : ℝ) * cWL = -(196389117 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(23302289 / 25000000) : ℝ) / 2 = -(23302289 / 50000000) := by norm_num
  refine certM (eLo := 410846218983 / 500000000000) (eHi := 821692437967 / 1000000000000) (y := -(23302289 / 25000000)) (u := 313739278711 / 500000000000)
    (ehi := 15749173601 / 40000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_75 : exp (-(((46500 : ℕ) : ℝ) * (714199 / 5000000000)) / 8) ≤ (4359375249 / 10000000000 : ℝ) := by
  have e : -(((46500 : ℕ) : ℝ) * (714199 / 5000000000)) / 8 = -(66420507 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_75 : exp (-(((46500 : ℕ) : ℝ) * (324913 / 2500000000)) / 8) ≤ (939623943 / 2000000000 : ℝ) := by
  have e : -(((46500 : ℕ) : ℝ) * (324913 / 2500000000)) / 8 = -(30216909 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `7.5`, every
`n ≥ 46500`** (exponents `τ_+ = 0.060366`, `τ_- = -0.142621`; `E_+ ≤ −0.00014284`,
`E_- ≤ −0.000129965`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `7.5/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_75 {n : ℕ} (hn : 46500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (15 / 2 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 46500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_75 Em_75 (by norm_num) (by norm_num) up_75 um_75 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_45
open BstLean.Part160 in
#print axioms classifier_frame_55
open BstLean.Part160 in
#print axioms classifier_frame_65
open BstLean.Part160 in
#print axioms classifier_frame_4
open BstLean.Part160 in
#print axioms classifier_frame_75
