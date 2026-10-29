import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2E`): ledger certificates, frame constants 4.4, 4.35, 4.3, 4.25, 4.2, 4.1

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `4.4`: `τ_+ = 0.091606`, `τ_- = -0.228018`, `n₀ = 30000` -/

lemma Ep_440 : Eplus aL (hAL + dsL) hWL cWL (440 / 100) (45803 / 500000) ≤ -(1087891 / 5000000000 : ℝ) := by
  have e : (45803 / 500000 : ℝ) * cWL = 63070731 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 567221318729 / 500000000000) (y := 2773539 / 6250000) (ehi := 779283056311 / 500000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_440 : Eminus aL (hAL + dsL) hWL cWL (440 / 100) (-(114009 / 500000)) ≤ -(255361 / 1250000000 : ℝ) := by
  have e : (-(114009 / 500000) : ℝ) * cWL = -(156990393 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(661113 / 800000) : ℝ) / 2 = -(661113 / 1600000) := by norm_num
  refine certM (eLo := 365266532243 / 500000000000) (eHi := 730533064487 / 1000000000000) (y := -(661113 / 800000)) (u := 165383214451 / 250000000000)
    (ehi := 87525144391 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_440 : exp (-(((30000 : ℕ) : ℝ) * (1087891 / 5000000000)) / 8) ≤ (1105582651 / 2500000000 : ℝ) := by
  have e : -(((30000 : ℕ) : ℝ) * (1087891 / 5000000000)) / 8 = -(3263673 / 4000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_440 : exp (-(((30000 : ℕ) : ℝ) * (255361 / 1250000000)) / 8) ≤ (581037809 / 1250000000 : ℝ) := by
  have e : -(((30000 : ℕ) : ℝ) * (255361 / 1250000000)) / 8 = -(766083 / 1000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.4`, every
`n ≥ 30000`** (exponents `τ_+ = 0.091606`, `τ_- = -0.228018`; `E_+ ≤ −0.000217578`,
`E_- ≤ −0.000204289`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.4/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_440 {n : ℕ} (hn : 30000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (440 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 30000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_440 Em_440 (by norm_num) (by norm_num) up_440 um_440 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.35`: `τ_+ = 0.092381`, `τ_- = -0.230208`, `n₀ = 29750` -/

lemma Ep_435 : Eplus aL (hAL + dsL) hWL cWL (435 / 100) (92381 / 1000000) ≤ -(2194367 / 10000000000 : ℝ) := by
  have e : (92381 / 1000000 : ℝ) * cWL = 127208637 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 70978370781 / 62500000000) (y := 5533453 / 12500000) (ehi := 1556868201089 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_435 : Eminus aL (hAL + dsL) hWL cWL (435 / 100) (-(3597 / 15625)) ≤ -(1030871 / 5000000000 : ℝ) := by
  have e : (-(3597 / 15625) : ℝ) * cWL = -(4953069 / 15625000) := by unfold cWL; norm_num
  have e2 : (-(41183487 / 50000000) : ℝ) / 2 = -(41183487 / 100000000) := by norm_num
  refine certM (eLo := 728333365467 / 1000000000000) (eHi := 182083341367 / 250000000000) (y := -(41183487 / 50000000)) (u := 662433654691 / 1000000000000)
    (ehi := 109704586717 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_435 : exp (-(((29750 : ℕ) : ℝ) * (2194367 / 10000000000)) / 8) ≤ (4421835427 / 10000000000 : ℝ) := by
  have e : -(((29750 : ℕ) : ℝ) * (2194367 / 10000000000)) / 8 = -(261129673 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_435 : exp (-(((29750 : ℕ) : ℝ) * (1030871 / 5000000000)) / 8) ≤ (4645387477 / 10000000000 : ℝ) := by
  have e : -(((29750 : ℕ) : ℝ) * (1030871 / 5000000000)) / 8 = -(122673649 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.35`, every
`n ≥ 29750`** (exponents `τ_+ = 0.092381`, `τ_- = -0.230208`; `E_+ ≤ −0.000219437`,
`E_- ≤ −0.000206174`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.35/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_435 {n : ℕ} (hn : 29750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (435 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 29750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_435 Em_435 (by norm_num) (by norm_num) up_435 um_435 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.3`: `τ_+ = 0.09317`, `τ_- = -0.232437`, `n₀ = 29500` -/

lemma Ep_430 : Eplus aL (hAL + dsL) hWL cWL (430 / 100) (9317 / 100000) ≤ -(2213277 / 10000000000 : ℝ) := by
  have e : (9317 / 100000 : ℝ) * cWL = 12829509 / 100000000 := by unfold cWL; norm_num
  refine certP (eT := 284222109403 / 250000000000) (y := 44157023 / 100000000) (ehi := 311029448233 / 200000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_430 : Eminus aL (hAL + dsL) hWL cWL (430 / 100) (-(232437 / 1000000)) ≤ -(1040469 / 5000000000 : ℝ) := by
  have e : (-(232437 / 1000000) : ℝ) * cWL = -(320065749 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(82089193 / 100000000) : ℝ) / 2 = -(82089193 / 200000000) := by norm_num
  refine certM (eLo := 72610129507 / 100000000000) (eHi := 726101295071 / 1000000000000) (y := -(82089193 / 100000000)) (u := 331677175669 / 500000000000)
    (ehi := 5500487443 / 12500000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_430 : exp (-(((29500 : ℕ) : ℝ) * (2213277 / 10000000000)) / 8) ≤ (4421324003 / 10000000000 : ℝ) := by
  have e : -(((29500 : ℕ) : ℝ) * (2213277 / 10000000000)) / 8 = -(130583343 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_430 : exp (-(((29500 : ℕ) : ℝ) * (1040469 / 5000000000)) / 8) ≤ (2321217947 / 5000000000 : ℝ) := by
  have e : -(((29500 : ℕ) : ℝ) * (1040469 / 5000000000)) / 8 = -(61387671 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.3`, every
`n ≥ 29500`** (exponents `τ_+ = 0.09317`, `τ_- = -0.232437`; `E_+ ≤ −0.000221328`,
`E_- ≤ −0.000208094`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.3/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_430 {n : ℕ} (hn : 29500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (430 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 29500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_430 Em_430 (by norm_num) (by norm_num) up_430 um_430 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.25`: `τ_+ = 0.093972`, `τ_- = -0.234708`, `n₀ = 29250` -/

lemma Ep_425 : Eplus aL (hAL + dsL) hWL cWL (425 / 100) (23493 / 250000) ≤ -(2232519 / 10000000000 : ℝ) := by
  have e : (23493 / 250000 : ℝ) * cWL = 32349861 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 227628931687 / 200000000000) (y := 8808817 / 20000000) (ehi := 310678376079 / 200000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_425 : Eminus aL (hAL + dsL) hWL cWL (425 / 100) (-(58677 / 250000)) ≤ -(1050243 / 5000000000 : ℝ) := by
  have e : (-(58677 / 250000) : ℝ) * cWL = -(80798229 / 250000000) := by unfold cWL; norm_num
  have e2 : (-(81806229 / 100000000) : ℝ) / 2 = -(81806229 / 200000000) := by norm_num
  refine certM (eLo := 361917100849 / 500000000000) (eHi := 723834201699 / 1000000000000) (y := -(81806229 / 100000000)) (u := 332146771289 / 500000000000)
    (ehi := 441285910711 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_425 : exp (-(((29250 : ℕ) : ℝ) * (2232519 / 10000000000)) / 8) ≤ (442079849 / 1000000000 : ℝ) := by
  have e : -(((29250 : ℕ) : ℝ) * (2232519 / 10000000000)) / 8 = -(261204723 / 320000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_425 : exp (-(((29250 : ℕ) : ℝ) * (1050243 / 5000000000)) / 8) ≤ (4639445707 / 10000000000 : ℝ) := by
  have e : -(((29250 : ℕ) : ℝ) * (1050243 / 5000000000)) / 8 = -(122878431 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.25`, every
`n ≥ 29250`** (exponents `τ_+ = 0.093972`, `τ_- = -0.234708`; `E_+ ≤ −0.000223252`,
`E_- ≤ −0.000210049`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.25/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_425 {n : ℕ} (hn : 29250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (425 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 29250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_425 Em_425 (by norm_num) (by norm_num) up_425 um_425 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.2`: `τ_+ = 0.094788`, `τ_- = -0.237021`, `n₀ = 29000` -/

lemma Ep_420 : Eplus aL (hAL + dsL) hWL cWL (420 / 100) (23697 / 250000) ≤ -(1126051 / 5000000000 : ℝ) := by
  have e : (23697 / 250000 : ℝ) * cWL = 32630769 / 250000000 := by unfold cWL; norm_num
  refine certP (eT := 71214014559 / 62500000000) (y := 43929081 / 100000000) (ehi := 310321288891 / 200000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_420 : Eminus aL (hAL + dsL) hWL cWL (420 / 100) (-(237021 / 1000000)) ≤ -(530099 / 2500000000 : ℝ) := by
  have e : (-(237021 / 1000000) : ℝ) * cWL = -(326377917 / 1000000000) := by unfold cWL; norm_num
  have e2 : (-(10189701 / 12500000) : ℝ) / 2 = -(10189701 / 25000000) := by norm_num
  refine certM (eLo := 360766228259 / 500000000000) (eHi := 721532456519 / 1000000000000) (y := -(10189701 / 12500000)) (u := 665252879957 / 1000000000000)
    (ehi := 110640348573 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_420 : exp (-(((29000 : ℕ) : ℝ) * (1126051 / 5000000000)) / 8) ≤ (4420258233 / 10000000000 : ℝ) := by
  have e : -(((29000 : ℕ) : ℝ) * (1126051 / 5000000000)) / 8 = -(32655479 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_420 : exp (-(((29000 : ℕ) : ℝ) * (530099 / 2500000000)) / 8) ≤ (2318207743 / 5000000000 : ℝ) := by
  have e : -(((29000 : ℕ) : ℝ) * (530099 / 2500000000)) / 8 = -(15372871 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.2`, every
`n ≥ 29000`** (exponents `τ_+ = 0.094788`, `τ_- = -0.237021`; `E_+ ≤ −0.00022521`,
`E_- ≤ −0.00021204`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.2/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_420 {n : ℕ} (hn : 29000 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (420 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 29000) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_420 Em_420 (by norm_num) (by norm_num) up_420 um_420 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `4.1`: `τ_+ = 0.096465`, `τ_- = -0.241782`, `n₀ = 28500` -/

lemma Ep_410 : Eplus aL (hAL + dsL) hWL cWL (410 / 100) (19293 / 200000) ≤ -(286541 / 1250000000 : ℝ) := by
  have e : (19293 / 200000 : ℝ) * cWL = 26566461 / 200000000 := by unfold cWL; norm_num
  refine certP (eT := 571029232389 / 500000000000) (y := 4369337 / 10000000) (ehi := 1547953444341 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_410 : Eminus aL (hAL + dsL) hWL cWL (410 / 100) (-(120891 / 500000)) ≤ -(2161339 / 10000000000 : ℝ) := by
  have e : (-(120891 / 500000) : ℝ) * cWL = -(166466907 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(1618481 / 2000000) : ℝ) / 2 = -(1618481 / 4000000) := by norm_num
  refine certM (eLo := 716817635877 / 1000000000000) (eHi := 358408817939 / 500000000000) (y := -(1618481 / 2000000)) (u := 667230143401 / 1000000000000)
    (ehi := 445196064263 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_410 : exp (-(((28500 : ℕ) : ℝ) * (286541 / 1250000000)) / 8) ≤ (4419131763 / 10000000000 : ℝ) := by
  have e : -(((28500 : ℕ) : ℝ) * (286541 / 1250000000)) / 8 = -(16332837 / 20000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_410 : exp (-(((28500 : ℕ) : ℝ) * (2161339 / 10000000000)) / 8) ≤ (4630237091 / 10000000000 : ℝ) := by
  have e : -(((28500 : ℕ) : ℝ) * (2161339 / 10000000000)) / 8 = -(123196323 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `4.1`, every
`n ≥ 28500`** (exponents `τ_+ = 0.096465`, `τ_- = -0.241782`; `E_+ ≤ −0.000229233`,
`E_- ≤ −0.000216134`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `4.1/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_410 {n : ℕ} (hn : 28500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (410 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 28500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_410 Em_410 (by norm_num) (by norm_num) up_410 um_410 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_440
open BstLean.Part160 in
#print axioms classifier_frame_435
open BstLean.Part160 in
#print axioms classifier_frame_430
open BstLean.Part160 in
#print axioms classifier_frame_425
open BstLean.Part160 in
#print axioms classifier_frame_420
open BstLean.Part160 in
#print axioms classifier_frame_410
