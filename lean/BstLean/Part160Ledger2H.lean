import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2H`): ledger certificates, frame constants 3.45 to 3.25

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `3.45`: `τ_+ = 0.109032`, `τ_- = -0.27776`, `n₀ = 25000` -/

lemma Ep_345 : Eplus aL (hAL + dsL) hWL cWL (345 / 100) (13629 / 125000) ≤ -(2594007 / 10000000000 : ℝ) := by
  have e : (13629 / 125000 : ℝ) * cWL = 18767133 / 125000000 := by unfold cWL; norm_num
  refine certP (eT := 1161993499291 / 1000000000000) (y := 41925789 / 100000000) (ehi := 760416255859 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_345 : Eminus aL (hAL + dsL) hWL cWL (345 / 100) (-(868 / 3125)) ≤ -(308751 / 1250000000 : ℝ) := by
  have e : (-(868 / 3125) : ℝ) * cWL = -(298809 / 781250) := by unfold cWL; norm_num
  have e2 : (-(76425929 / 100000000) : ℝ) / 2 = -(76425929 / 200000000) := by norm_num
  refine certM (eLo := 170542647577 / 250000000000) (eHi := 682170590309 / 1000000000000) (y := -(76425929 / 100000000)) (u := 68240657687 / 100000000000)
    (ehi := 116419684039 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_345 : exp (-(((25000 : ℕ) : ℝ) * (2594007 / 10000000000)) / 8) ≤ (4445791443 / 10000000000 : ℝ) := by
  have e : -(((25000 : ℕ) : ℝ) * (2594007 / 10000000000)) / 8 = -(2594007 / 3200000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_345 : exp (-(((25000 : ℕ) : ℝ) * (308751 / 1250000000)) / 8) ≤ (4621445769 / 10000000000 : ℝ) := by
  have e : -(((25000 : ℕ) : ℝ) * (308751 / 1250000000)) / 8 = -(308751 / 400000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.45`, every
`n ≥ 25000`** (exponents `τ_+ = 0.109032`, `τ_- = -0.27776`; `E_+ ≤ −0.000259401`,
`E_- ≤ −0.000247001`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.45/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_345 {n : ℕ} (hn : 25000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (345 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 25000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_345 Em_345 (by norm_num) (by norm_num) up_345 um_345 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.4`: `τ_+ = 0.110138`, `τ_- = -0.280949`, `n₀ = 24750` -/

lemma Ep_340 : Eplus aL (hAL + dsL) hWL cWL (340 / 100) (55069 / 500000) ≤ -(524117 / 2000000000 : ℝ) := by
  have e : (55069 / 500000 : ℝ) * cWL = 75830013 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 1163764519491 / 1000000000000) (y := 41769887 / 100000000) (ehi := 1518463350681 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_340 : Eminus aL (hAL + dsL) hWL cWL (340 / 100) (-(280949 / 1000000)) ≤ -(78041 / 312500000 : ℝ) := by
  have e : (-(280949 / 1000000) : ℝ) * cWL = -(386866773 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(19006659 / 25000000) : ℝ) / 2 = -(19006659 / 50000000) := by norm_num
  refine certM (eLo := 339590787111 / 500000000000) (eHi := 42448848389 / 62500000000) (y := -(19006659 / 25000000)) (u := 136754067723 / 200000000000)
    (ehi := 46754187597 / 100000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_340 : exp (-(((24750 : ℕ) : ℝ) * (524117 / 2000000000)) / 8) ≤ (2222637221 / 5000000000 : ℝ) := by
  have e : -(((24750 : ℕ) : ℝ) * (524117 / 2000000000)) / 8 = -(51887583 / 64000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_340 : exp (-(((24750 : ℕ) : ℝ) * (78041 / 312500000)) / 8) ≤ (4618080733 / 10000000000 : ℝ) := by
  have e : -(((24750 : ℕ) : ℝ) * (78041 / 312500000)) / 8 = -(7726059 / 10000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.4`, every
`n ≥ 24750`** (exponents `τ_+ = 0.110138`, `τ_- = -0.280949`; `E_+ ≤ −0.000262059`,
`E_- ≤ −0.000249731`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.4/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_340 {n : ℕ} (hn : 24750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (340 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 24750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_340 Em_340 (by norm_num) (by norm_num) up_340 um_340 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.35`: `τ_+ = 0.111268`, `τ_- = -0.284207`, `n₀ = 24500` -/

lemma Ep_335 : Eplus aL (hAL + dsL) hWL cWL (335 / 100) (27817 / 250000) ≤ -(2647721 / 10000000000 : ℝ) := by
  have e : (27817 / 250000 : ℝ) * cWL = 38304009 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 582788379143 / 500000000000) (y := 41611057 / 100000000) (ehi := 758026744819 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_335 : Eminus aL (hAL + dsL) hWL cWL (335 / 100) (-(284207 / 1000000)) ≤ -(2525203 / 10000000000 : ℝ) := by
  have e : (-(284207 / 1000000) : ℝ) * cWL = -(391353039 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(18904613 / 25000000) : ℝ) / 2 = -(18904613 / 50000000) := by norm_num
  refine certM (eLo := 676141409611 / 1000000000000) (eHi := 169035352403 / 250000000000) (y := -(18904613 / 25000000)) (u := 685167284217 / 1000000000000)
    (ehi := 234727103681 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_335 : exp (-(((24500 : ℕ) : ℝ) * (2647721 / 10000000000)) / 8) ≤ (4444736277 / 10000000000 : ℝ) := by
  have e : -(((24500 : ℕ) : ℝ) * (2647721 / 10000000000)) / 8 = -(129738329 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_335 : exp (-(((24500 : ℕ) : ℝ) * (2525203 / 10000000000)) / 8) ≤ (1153669017 / 2500000000 : ℝ) := by
  have e : -(((24500 : ℕ) : ℝ) * (2525203 / 10000000000)) / 8 = -(123734947 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.35`, every
`n ≥ 24500`** (exponents `τ_+ = 0.111268`, `τ_- = -0.284207`; `E_+ ≤ −0.000264772`,
`E_- ≤ −0.00025252`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.35/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_335 {n : ℕ} (hn : 24500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (335 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 24500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_335 Em_335 (by norm_num) (by norm_num) up_335 um_335 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.3`: `τ_+ = 0.112422`, `τ_- = -0.287534`, `n₀ = 24250` -/

lemma Ep_330 : Eplus aL (hAL + dsL) hWL cWL (330 / 100) (56211 / 500000) ≤ -(1337717 / 5000000000 : ℝ) := by
  have e : (56211 / 500000 : ℝ) * cWL = 77402547 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 58371519987 / 50000000000) (y := 20724441 / 50000000) (ehi := 18919960281 / 12500000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_330 : Eminus aL (hAL + dsL) hWL cWL (330 / 100) (-(143767 / 500000)) ≤ -(2553701 / 10000000000 : ℝ) := by
  have e : (-(143767 / 500000) : ℝ) * cWL = -(197967159 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(75200657 / 100000000) : ℝ) / 2 = -(75200657 / 200000000) := by norm_num
  refine certM (eLo := 336525450907 / 500000000000) (eHi := 134610180363 / 200000000000) (y := -(75200657 / 100000000)) (u := 343300038779 / 500000000000)
    (ehi := 471419666503 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_330 : exp (-(((24250 : ℕ) : ℝ) * (1337717 / 5000000000)) / 8) ≤ (4444174609 / 10000000000 : ℝ) := by
  have e : -(((24250 : ℕ) : ℝ) * (1337717 / 5000000000)) / 8 = -(129758549 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_330 : exp (-(((24250 : ℕ) : ℝ) * (2553701 / 10000000000)) / 8) ≤ (1152807321 / 2500000000 : ℝ) := by
  have e : -(((24250 : ℕ) : ℝ) * (2553701 / 10000000000)) / 8 = -(247708997 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.3`, every
`n ≥ 24250`** (exponents `τ_+ = 0.112422`, `τ_- = -0.287534`; `E_+ ≤ −0.000267543`,
`E_- ≤ −0.00025537`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.3/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_330 {n : ℕ} (hn : 24250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (330 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 24250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_330 Em_330 (by norm_num) (by norm_num) up_330 um_330 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `3.25`: `τ_+ = 0.1136`, `τ_- = -0.290936`, `n₀ = 24000` -/

lemma Ep_325 : Eplus aL (hAL + dsL) hWL cWL (325 / 100) (71 / 625) ≤ -(1351871 / 5000000000 : ℝ) := by
  have e : (71 / 625 : ℝ) * cWL = 97767 / 625000 := by unfold cWL; norm_num
  refine certP (eT := 233865126463 / 200000000000) (y := 41282941 / 100000000) (ehi := 188885903447 / 125000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_325 : Eminus aL (hAL + dsL) hWL cWL (325 / 100) (-(36367 / 125000)) ≤ -(103313 / 400000000 : ℝ) := by
  have e : (-(36367 / 125000) : ℝ) * cWL = -(50077359 / 125000000) := by unfold cWL; norm_num
  have e2 : (-(14954759 / 20000000) : ℝ) / 2 = -(14954759 / 40000000) := by norm_num
  refine certM (eLo := 167476333017 / 250000000000) (eHi := 669905332069 / 1000000000000) (y := -(14954759 / 20000000)) (u := 68806705991 / 100000000000)
    (ehi := 236718139467 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_325 : exp (-(((24000 : ℕ) : ℝ) * (1351871 / 5000000000)) / 8) ≤ (277724343 / 625000000 : ℝ) := by
  have e : -(((24000 : ℕ) : ℝ) * (1351871 / 5000000000)) / 8 = -(4055613 / 5000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_325 : exp (-(((24000 : ℕ) : ℝ) * (103313 / 400000000)) / 8) ≤ (4607740437 / 10000000000 : ℝ) := by
  have e : -(((24000 : ℕ) : ℝ) * (103313 / 400000000)) / 8 = -(309939 / 400000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `3.25`, every
`n ≥ 24000`** (exponents `τ_+ = 0.1136`, `τ_- = -0.290936`; `E_+ ≤ −0.000270374`,
`E_- ≤ −0.000258282`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `3.25/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_325 {n : ℕ} (hn : 24000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (325 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 24000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_325 Em_325 (by norm_num) (by norm_num) up_325 um_325 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_345
open BstLean.Part160 in
#print axioms classifier_frame_340
open BstLean.Part160 in
#print axioms classifier_frame_335
open BstLean.Part160 in
#print axioms classifier_frame_330
open BstLean.Part160 in
#print axioms classifier_frame_325
