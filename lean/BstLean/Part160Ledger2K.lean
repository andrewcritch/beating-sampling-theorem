import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2K`): ledger certificates, frame constants 2.70 to 2.50

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `2.7`: `τ_+ = 0.128457`, `τ_- = -0.333922`, `n₀ = 21000` -/

lemma Ep_270 : Eplus aL (hAL + dsL) hWL cWL (270 / 100) (128457 / 1000000) ≤ -(122431 / 400000000 : ℝ) := by
  have e : (128457 / 1000000 : ℝ) * cWL = 176885289 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 298373544591 / 250000000000) (y := 9797973 / 25000000) (ehi := 739908861459 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_270 : Eminus aL (hAL + dsL) hWL cWL (270 / 100) (-(166961 / 500000)) ≤ -(1475389 / 5000000000 : ℝ) := by
  have e : (-(166961 / 500000) : ℝ) * cWL = -(229905297 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(4335337 / 6250000) : ℝ) / 2 = -(4335337 / 12500000) := by norm_num
  refine certM (eLo := 631403225741 / 1000000000000) (eHi := 315701612871 / 500000000000) (y := -(4335337 / 6250000)) (u := 141385528887 / 200000000000)
    (ehi := 499746694467 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_270 : exp (-(((21000 : ℕ) : ℝ) * (122431 / 400000000)) / 8) ≤ (447779911 / 1000000000 : ℝ) := by
  have e : -(((21000 : ℕ) : ℝ) * (122431 / 400000000)) / 8 = -(2571051 / 3200000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_270 : exp (-(((21000 : ℕ) : ℝ) * (1475389 / 5000000000)) / 8) ≤ (921795349 / 2000000000 : ℝ) := by
  have e : -(((21000 : ℕ) : ℝ) * (1475389 / 5000000000)) / 8 = -(30983169 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.7`, every
`n ≥ 21000`** (exponents `τ_+ = 0.128457`, `τ_- = -0.333922`; `E_+ ≤ −0.000306077`,
`E_- ≤ −0.000295078`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.7/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_270 {n : ℕ} (hn : 21000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (270 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 21000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_270 Em_270 (by norm_num) (by norm_num) up_270 um_270 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.65`: `τ_+ = 0.130009`, `τ_- = -0.338407`, `n₀ = 20750` -/

lemma Ep_265 : Eplus aL (hAL + dsL) hWL cWL (265 / 100) (130009 / 1000000) ≤ -(3098063 / 10000000000 : ℝ) := by
  have e : (130009 / 1000000 : ℝ) * cWL = 179022393 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 1196047526961 / 1000000000000) (y := 7794743 / 20000000) (ehi := 1476592620499 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_265 : Eminus aL (hAL + dsL) hWL cWL (265 / 100) (-(338407 / 1000000)) ≤ -(149461 / 500000000 : ℝ) := by
  have e : (-(338407 / 1000000) : ℝ) * cWL = -(465986439 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(68798867 / 100000000) : ℝ) / 2 = -(68798867 / 200000000) := by norm_num
  refine certM (eLo := 627515793731 / 1000000000000) (eHi := 156878948433 / 250000000000) (y := -(68798867 / 100000000)) (u := 44308309009 / 62500000000)
    (ehi := 502585919293 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_265 : exp (-(((20750 : ℕ) : ℝ) * (3098063 / 10000000000)) / 8) ≤ (1119330391 / 2500000000 : ℝ) := by
  have e : -(((20750 : ℕ) : ℝ) * (3098063 / 10000000000)) / 8 = -(257139229 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_265 : exp (-(((20750 : ℕ) : ℝ) * (149461 / 500000000)) / 8) ≤ (575690329 / 1250000000 : ℝ) := by
  have e : -(((20750 : ℕ) : ℝ) * (149461 / 500000000)) / 8 = -(12405263 / 16000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.65`, every
`n ≥ 20750`** (exponents `τ_+ = 0.130009`, `τ_- = -0.338407`; `E_+ ≤ −0.000309806`,
`E_- ≤ −0.000298922`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.65/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_265 {n : ℕ} (hn : 20750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (265 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 20750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_265 Em_265 (by norm_num) (by norm_num) up_265 um_265 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.6`: `τ_+ = 0.131599`, `τ_- = -0.343006`, `n₀ = 20500` -/

lemma Ep_260 : Eplus aL (hAL + dsL) hWL cWL (260 / 100) (131599 / 1000000) ≤ -(3136289 / 10000000000 : ℝ) := by
  have e : (131599 / 1000000 : ℝ) * cWL = 181211823 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 7491681613 / 6250000000) (y := 19374841 / 50000000) (ehi := 294657653711 / 200000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_260 : Eminus aL (hAL + dsL) hWL cWL (260 / 100) (-(171503 / 500000)) ≤ -(1514311 / 5000000000 : ℝ) := by
  have e : (-(171503 / 500000) : ℝ) * cWL = -(236159631 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(1364373 / 2000000) : ℝ) / 2 = -(1364373 / 4000000) := by norm_num
  refine certM (eLo := 623554403909 / 1000000000000) (eHi := 62355440391 / 100000000000) (y := -(1364373 / 2000000)) (u := 142198521011 / 200000000000)
    (ehi := 505510484443 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_260 : exp (-(((20500 : ℕ) : ℝ) * (3136289 / 10000000000)) / 8) ≤ (1119202833 / 2500000000 : ℝ) := by
  have e : -(((20500 : ℕ) : ℝ) * (3136289 / 10000000000)) / 8 = -(128587849 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_260 : exp (-(((20500 : ℕ) : ℝ) * (1514311 / 5000000000)) / 8) ≤ (143813897 / 312500000 : ℝ) := by
  have e : -(((20500 : ℕ) : ℝ) * (1514311 / 5000000000)) / 8 = -(62086751 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.6`, every
`n ≥ 20500`** (exponents `τ_+ = 0.131599`, `τ_- = -0.343006`; `E_+ ≤ −0.000313629`,
`E_- ≤ −0.000302862`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.6/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_260 {n : ℕ} (hn : 20500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (260 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 20500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_260 Em_260 (by norm_num) (by norm_num) up_260 um_260 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.55`: `τ_+ = 0.13323`, `τ_- = -0.347716`, `n₀ = 20250` -/

lemma Ep_255 : Eplus aL (hAL + dsL) hWL cWL (255 / 100) (13323 / 100000) ≤ -(317549 / 1000000000 : ℝ) := by
  have e : (13323 / 100000 : ℝ) * cWL = 18345771 / 100000000 := by unfold cWL; norm_num
  refine certP (eT := 150170519831 / 125000000000) (y := 38520057 / 100000000) (ehi := 367477277887 / 250000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_255 : Eminus aL (hAL + dsL) hWL cWL (255 / 100) (-(86929 / 250000)) ≤ -(3069019 / 10000000000 : ℝ) := by
  have e : (-(86929 / 250000) : ℝ) * cWL = -(119701233 / 250000000) := by unfold cWL; norm_num
  have e2 : (-(67623209 / 100000000) : ℝ) / 2 = -(67623209 / 200000000) := by norm_num
  refine certM (eLo := 309761661041 / 500000000000) (eHi := 619523322083 / 1000000000000) (y := -(67623209 / 100000000)) (u := 356556264977 / 500000000000)
    (ehi := 254264740189 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_255 : exp (-(((20250 : ℕ) : ℝ) * (317549 / 1000000000)) / 8) ≤ (2238132933 / 5000000000 : ℝ) := by
  have e : -(((20250 : ℕ) : ℝ) * (317549 / 1000000000)) / 8 = -(25721469 / 32000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_255 : exp (-(((20250 : ℕ) : ℝ) * (3069019 / 10000000000)) / 8) ≤ (919708733 / 2000000000 : ℝ) := by
  have e : -(((20250 : ℕ) : ℝ) * (3069019 / 10000000000)) / 8 = -(248590539 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.55`, every
`n ≥ 20250`** (exponents `τ_+ = 0.13323`, `τ_- = -0.347716`; `E_+ ≤ −0.000317549`,
`E_- ≤ −0.000306902`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.55/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_255 {n : ℕ} (hn : 20250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (255 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 20250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_255 Em_255 (by norm_num) (by norm_num) up_255 um_255 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.5`: `τ_+ = 0.134903`, `τ_- = -0.352546`, `n₀ = 20000` -/

lemma Ep_250 : Eplus aL (hAL + dsL) hWL cWL (250 / 100) (134903 / 1000000) ≤ -(1607853 / 5000000000 : ℝ) := by
  have e : (134903 / 1000000 : ℝ) * cWL = 185761431 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 301033739209 / 250000000000) (y := 3828441 / 10000000) (ehi := 1466449392787 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_250 : Eminus aL (hAL + dsL) hWL cWL (250 / 100) (-(176273 / 500000)) ≤ -(622089 / 2000000000 : ℝ) := by
  have e : (-(176273 / 500000) : ℝ) * cWL = -(242727921 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(67012851 / 100000000) : ℝ) / 2 = -(67012851 / 200000000) := by norm_num
  refine certM (eLo := 615416600081 / 1000000000000) (eHi := 307708300041 / 500000000000) (y := -(67012851 / 100000000)) (u := 715292123781 / 1000000000000)
    (ehi := 63955352793 / 125000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_250 : exp (-(((20000 : ℕ) : ℝ) * (1607853 / 5000000000)) / 8) ≤ (1118920333 / 2500000000 : ℝ) := by
  have e : -(((20000 : ℕ) : ℝ) * (1607853 / 5000000000)) / 8 = -(1607853 / 2000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_250 : exp (-(((20000 : ℕ) : ℝ) * (622089 / 2000000000)) / 8) ≤ (287188961 / 625000000 : ℝ) := by
  have e : -(((20000 : ℕ) : ℝ) * (622089 / 2000000000)) / 8 = -(622089 / 800000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.5`, every
`n ≥ 20000`** (exponents `τ_+ = 0.134903`, `τ_- = -0.352546`; `E_+ ≤ −0.000321571`,
`E_- ≤ −0.000311045`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.5/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_250 {n : ℕ} (hn : 20000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (250 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 20000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_250 Em_250 (by norm_num) (by norm_num) up_250 um_250 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_270
open BstLean.Part160 in
#print axioms classifier_frame_265
open BstLean.Part160 in
#print axioms classifier_frame_260
open BstLean.Part160 in
#print axioms classifier_frame_255
open BstLean.Part160 in
#print axioms classifier_frame_250
