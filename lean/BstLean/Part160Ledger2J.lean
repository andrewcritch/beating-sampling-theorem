import BstLean.Part160Ledger2Gen

/-!
# Part 160 (file `Ledger2J`): ledger certificates, frame constants 2.95 to 2.75

Do not use `sorry`, `native_decide` or `axiom`. The rational constants were computed outside
Lean (a python script with exact fractions); Lean checks every inequality.

For each frame constant: `Ep_<tag>` (`E_+ ≤ −e_+`), `Em_<tag>` (`E_- ≤ −e_-`), the two tails at
`n₀`, and `classifier_frame_<tag>`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157

/-! ### Frame constant `2.95`: `τ_+ = 0.121238`, `τ_- = -0.313024`, `n₀ = 22500` -/

lemma Ep_295 : Eplus aL (hAL + dsL) hWL cWL (295 / 100) (60619 / 500000) ≤ -(90227 / 312500000 : ℝ) := by
  have e : (60619 / 500000 : ℝ) * cWL = 83472363 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 1181688946829 / 1000000000000) (y := 20104121 / 50000000) (ehi := 186866817513 / 125000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_295 : Eminus aL (hAL + dsL) hWL cWL (295 / 100) (-(4891 / 15625)) ≤ -(277187 / 1000000000 : ℝ) := by
  have e : (-(4891 / 15625) : ℝ) * cWL = -(6734907 / 15625000) := by unfold cWL; norm_num
  have e2 : (-(71997943 / 100000000) : ℝ) / 2 = -(71997943 / 200000000) := by norm_num
  refine certM (eLo := 129967356951 / 200000000000) (eHi := 162459196189 / 250000000000) (y := -(71997943 / 100000000)) (u := 697683501709 / 1000000000000)
    (ehi := 486762268557 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_295 : exp (-(((22500 : ℕ) : ℝ) * (90227 / 312500000)) / 8) ≤ (443950149 / 1000000000 : ℝ) := by
  have e : -(((22500 : ℕ) : ℝ) * (90227 / 312500000)) / 8 = -(812043 / 1000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_295 : exp (-(((22500 : ℕ) : ℝ) * (277187 / 1000000000)) / 8) ≤ (4585947129 / 10000000000 : ℝ) := by
  have e : -(((22500 : ℕ) : ℝ) * (277187 / 1000000000)) / 8 = -(2494683 / 3200000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.95`, every
`n ≥ 22500`** (exponents `τ_+ = 0.121238`, `τ_- = -0.313024`; `E_+ ≤ −0.000288726`,
`E_- ≤ −0.000277187`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.95/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_295 {n : ℕ} (hn : 22500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (295 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 22500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_295 Em_295 (by norm_num) (by norm_num) up_295 um_295 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.9`: `τ_+ = 0.122614`, `τ_- = -0.317008`, `n₀ = 22250` -/

lemma Ep_290 : Eplus aL (hAL + dsL) hWL cWL (290 / 100) (61307 / 500000) ≤ -(1460173 / 5000000000 : ℝ) := by
  have e : (61307 / 500000 : ℝ) * cWL = 84419739 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 1183930076847 / 1000000000000) (y := 10003577 / 25000000) (ehi := 1492038163191 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_290 : Eminus aL (hAL + dsL) hWL cWL (290 / 100) (-(19813 / 62500)) ≤ -(350747 / 1250000000 : ℝ) := by
  have e : (-(19813 / 62500) : ℝ) * cWL = -(27282501 / 62500000) := by unfold cWL; norm_num
  have e2 : (-(8937031 / 12500000) : ℝ) / 2 = -(8937031 / 25000000) := by norm_num
  refine certM (eLo := 80785195223 / 125000000000) (eHi := 323140780893 / 500000000000) (y := -(8937031 / 12500000)) (u := 174858955059 / 250000000000)
    (ehi := 48921046663 / 100000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_290 : exp (-(((22250 : ℕ) : ℝ) * (1460173 / 5000000000)) / 8) ≤ (4438710303 / 10000000000 : ℝ) := by
  have e : -(((22250 : ℕ) : ℝ) * (1460173 / 5000000000)) / 8 = -(129955397 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_290 : exp (-(((22250 : ℕ) : ℝ) * (350747 / 1250000000)) / 8) ≤ (2291085763 / 5000000000 : ℝ) := by
  have e : -(((22250 : ℕ) : ℝ) * (350747 / 1250000000)) / 8 = -(31216483 / 40000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.9`, every
`n ≥ 22250`** (exponents `τ_+ = 0.122614`, `τ_- = -0.317008`; `E_+ ≤ −0.000292035`,
`E_- ≤ −0.000280598`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.9/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_290 {n : ℕ} (hn : 22250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (290 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 22250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_290 Em_290 (by norm_num) (by norm_num) up_290 um_290 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.85`: `τ_+ = 0.124023`, `τ_- = -0.321088`, `n₀ = 21750` -/

lemma Ep_285 : Eplus aL (hAL + dsL) hWL cWL (285 / 100) (124023 / 1000000) ≤ -(92319 / 312500000 : ℝ) := by
  have e : (124023 / 1000000 : ℝ) * cWL = 170779671 / 1000000000 := by unfold cWL; norm_num
  refine certP (eT := 1186229359499 / 1000000000000) (y := 7963199 / 20000000) (ehi := 1489082189557 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_285 : Eminus aL (hAL + dsL) hWL cWL (285 / 100) (-(5017 / 15625)) ≤ -(710223 / 2500000000 : ℝ) := by
  have e : (-(5017 / 15625) : ℝ) * cWL = -(6908409 / 15625000) := by unfold cWL; norm_num
  have e2 : (-(14196557 / 20000000) : ℝ) / 2 = -(14196557 / 40000000) := by norm_num
  refine certM (eLo := 642660829017 / 1000000000000) (eHi := 321330414509 / 500000000000) (y := -(14196557 / 20000000)) (u := 701233799311 / 1000000000000)
    (ehi := 491728841297 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_285 : exp (-(((21750 : ℕ) : ℝ) * (92319 / 312500000)) / 8) ≤ (4479044727 / 10000000000 : ℝ) := by
  have e : -(((21750 : ℕ) : ℝ) * (92319 / 312500000)) / 8 = -(8031753 / 10000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_285 : exp (-(((21750 : ℕ) : ℝ) * (710223 / 2500000000)) / 8) ≤ (4619181757 / 10000000000 : ℝ) := by
  have e : -(((21750 : ℕ) : ℝ) * (710223 / 2500000000)) / 8 = -(61789401 / 80000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.85`, every
`n ≥ 21750`** (exponents `τ_+ = 0.124023`, `τ_- = -0.321088`; `E_+ ≤ −0.000295421`,
`E_- ≤ −0.000284089`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.85/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_285 {n : ℕ} (hn : 21750 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (285 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 21750) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_285 Em_285 (by norm_num) (by norm_num) up_285 um_285 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.8`: `τ_+ = 0.125466`, `τ_- = -0.325264`, `n₀ = 21500` -/

lemma Ep_280 : Eplus aL (hAL + dsL) hWL cWL (280 / 100) (62733 / 500000) ≤ -(2988881 / 10000000000 : ℝ) := by
  have e : (62733 / 500000 : ℝ) * cWL = 86383341 / 500000000 := by unfold cWL; norm_num
  refine certP (eT := 1188588753579 / 1000000000000) (y := 39613059 / 100000000) (ehi := 185757921237 / 125000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_280 : Eminus aL (hAL + dsL) hWL cWL (280 / 100) (-(20329 / 62500)) ≤ -(575329 / 2000000000 : ℝ) := by
  have e : (-(20329 / 62500) : ℝ) * cWL = -(27993033 / 62500000) := by unfold cWL; norm_num
  have e2 : (-(35228307 / 50000000) : ℝ) / 2 = -(35228307 / 100000000) := by norm_num
  refine certM (eLo := 39935994249 / 62500000000) (eHi := 127795181597 / 200000000000) (y := -(35228307 / 50000000)) (u := 703081072647 / 1000000000000)
    (ehi := 98864598943 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_280 : exp (-(((21500 : ℕ) : ℝ) * (2988881 / 10000000000)) / 8) ≤ (2239328723 / 5000000000 : ℝ) := by
  have e : -(((21500 : ℕ) : ℝ) * (2988881 / 10000000000)) / 8 = -(128521883 / 160000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_280 : exp (-(((21500 : ℕ) : ℝ) * (575329 / 2000000000)) / 8) ≤ (1153951787 / 2500000000 : ℝ) := by
  have e : -(((21500 : ℕ) : ℝ) * (575329 / 2000000000)) / 8 = -(24739147 / 32000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.8`, every
`n ≥ 21500`** (exponents `τ_+ = 0.125466`, `τ_- = -0.325264`; `E_+ ≤ −0.000298888`,
`E_- ≤ −0.000287664`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.8/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_280 {n : ℕ} (hn : 21500 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (280 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 21500) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_280 Em_280 (by norm_num) (by norm_num) up_280 um_280 (by norm_num) D t hEv hsum
    hFW hFA hRA

/-! ### Frame constant `2.75`: `τ_+ = 0.126944`, `τ_- = -0.329542`, `n₀ = 21250` -/

lemma Ep_275 : Eplus aL (hAL + dsL) hWL cWL (275 / 100) (3967 / 31250) ≤ -(378049 / 1250000000 : ℝ) := by
  have e : (3967 / 31250 : ℝ) * cWL = 5462559 / 31250000 := by unfold cWL; norm_num
  refine certP (eT := 595505119909 / 500000000000) (y := 19702617 / 50000000) (ehi := 1482978165721 / 1000000000000) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · rw [e]
    refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num
  · refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · unfold cWL hWL; norm_num

lemma Em_275 : Eminus aL (hAL + dsL) hWL cWL (275 / 100) (-(164771 / 500000)) ≤ -(182079 / 625000000 : ℝ) := by
  have e : (-(164771 / 500000) : ℝ) * cWL = -(226889667 / 500000000) := by unfold cWL; norm_num
  have e2 : (-(69917811 / 100000000) : ℝ) / 2 = -(69917811 / 200000000) := by norm_num
  refine certM (eLo := 5081783119 / 8000000000) (eHi := 158805722469 / 250000000000) (y := -(69917811 / 100000000)) (u := 704977737277 / 1000000000000)
    (ehi := 496993610057 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
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

lemma up_275 : exp (-(((21250 : ℕ) : ℝ) * (378049 / 1250000000)) / 8) ≤ (4478243833 / 10000000000 : ℝ) := by
  have e : -(((21250 : ℕ) : ℝ) * (378049 / 1250000000)) / 8 = -(6426833 / 8000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma um_275 : exp (-(((21250 : ℕ) : ℝ) * (182079 / 625000000)) / 8) ≤ (2306202339 / 5000000000 : ℝ) := by
  have e : -(((21250 : ℕ) : ℝ) * (182079 / 625000000)) / 8 = -(3095343 / 4000000) := by norm_num
  rw [e]
  refine exp_le_taylor (b := 1) 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The conditional classifier theorem for the Agent frame constant `2.75`, every
`n ≥ 21250`** (exponents `τ_+ = 0.126944`, `τ_- = -0.329542`; `E_+ ≤ −0.000302439`,
`E_- ≤ −0.000291326`): IF the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, and on
the good set the World frame bound, the Agent frame bound `2.75/n` and the Agent
replacement hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_frame_275 {n : ℕ} (hn : 21250 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (275 / 100 / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  frame_entry (N0 := 21250) (by norm_num) hn (by norm_num) (by norm_num) (by norm_num)
    Ep_275 Em_275 (by norm_num) (by norm_num) up_275 um_275 (by norm_num) D t hEv hsum
    hFW hFA hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms classifier_frame_295
open BstLean.Part160 in
#print axioms classifier_frame_290
open BstLean.Part160 in
#print axioms classifier_frame_285
open BstLean.Part160 in
#print axioms classifier_frame_280
open BstLean.Part160 in
#print axioms classifier_frame_275
