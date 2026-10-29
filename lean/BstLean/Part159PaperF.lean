import BstLean.Part159Paper

/-!
# Part 159 (file `PaperF`): the classifier theorem for the World centre of the paper, with only
Agent-side hypotheses and two hypotheses on the computed constants

Role: `delegations/statements/p159-spec.md`, items 2 and 3. Do not use `sorry`, `native_decide`
or `axiom`.

* `vPert_pap_le`: the formula `vPert` at the constants of the paper's centre is at most
  `vPap = 7.37·10⁻⁹` for `n ≥ 16 384` (the ledger of Part 156 has `v_W = 1.1869648·10⁻⁸`).
* `pap_moment`: a majorant of `E_u H_u²` on `GPap n` with restricted mean `≤ vPap`.
* `HP n`, `events_paper`, `frame_w_paper`: `EVENTS_hyp` (World parts) and `FRAME_W_hyp` for every
  design with the World centre `bWp` and the scalar `tau0p` of the paper.
* **`classifier_paper_conditional_agent`**: for `paperDesign n fT wT` (Part 157) and every
  `n ≥ 16 384`: IF `ConstC n`, `ConstK n` (two statements about the computed constants `c̃_N`,
  `κ̃`), an event `E₁` with `Pr(HP n ∩ E₁ᶜ) ≤ δ_extra`, and the two Agent hypotheses hold, THEN
  the program succeeds with probability at least `99/100`.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le)
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN mW_ge_pow42 cHat2)
open BstLean.Part140
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- `ε = √(0.0645/m_W)`: `t_W|b_W − b̂|² ≤ γε²`. -/
noncomputable def εPap (n : ℕ) : ℝ := √(645 / 10 ^ 4 / (mW n : ℝ))

/-- The bound of the Hellinger moment for the centre of the paper, `n ≥ 16 384`: `7.37·10⁻⁹`. -/
noncomputable def vPap : ℝ := 737 / 10 ^ 11

lemma vPap_le : vPap ≤ vWL := by unfold vPap vWL; norm_num

/-- `c_ρ ≥ 5.38` at `A_lo = 1.994`, `A_hi = 2.057`, `ζ = 1/20`. -/
lemma cRhoG_pap : 538 / 100 ≤ cRhoG (1994 / 1000) (2057 / 1000) (1 / 20) := by
  have hr : 6503 / 10000 ≤ rLowG (1994 / 1000) (2057 / 1000) (1 / 20) := by
    unfold rLowG zetaG
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  have hs : 8064 / 10000 ≤ √(rLowG (1994 / 1000) (2057 / 1000) (1 / 20)) :=
    Real.le_sqrt_of_sq_le (le_trans (by norm_num) hr)
  unfold cRhoG
  have h1 : (1 + 8064 / 10000 : ℝ) ^ 2 ≤
      (1 + √(rLowG (1994 / 1000) (2057 / 1000) (1 / 20))) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h2 : (538 / 100 : ℝ) ≤ (1 + 8064 / 10000) ^ 2 * (1 + 6503 / 10000) := by norm_num
  have h3 : (1 + 8064 / 10000 : ℝ) ^ 2 * (1 + 6503 / 10000) ≤
      (1 + √(rLowG (1994 / 1000) (2057 / 1000) (1 / 20))) ^ 2 *
        (1 + rLowG (1994 / 1000) (2057 / 1000) (1 / 20)) :=
    mul_le_mul h1 (by linarith) (by norm_num) (sq_nonneg _)
  linarith

/-- **The numeric bound of the Hellinger moment for the centre of the paper** (`n ≥ 16 384`). -/
theorem vPert_pap_le (hn : 16384 ≤ n) :
    vPert n (εPap n) (ρPap n) (1994 / 1000) (2057 / 1000) (1001 / 1000) (1 / 20) ≤ vPap := by
  unfold vPert vPap
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have hmpos : (0 : ℝ) < mW n := by linarith
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  have hκ : 0 < kap1 (2 * n) := by linarith
  set r : ℝ := √(1 / (mW n : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 / (mW n : ℝ) := Real.sq_sqrt (by positivity)
  have hrle : r ≤ 1 / 2097152 := by
    rw [hr, Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hmpos]
    nlinarith
  -- `a_r`
  have harW : arW n ≤ 31623 / 10000 * r := by
    have e : (31623 / 10000 : ℝ) * r = √((31623 / 10000) ^ 2 * (1 / (mW n : ℝ))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)]
    rw [e]
    unfold arW
    refine Real.sqrt_le_sqrt ?_
    have h1 : 25 / (mW n : ℝ) ^ 2 ≤ 1 / 10 ^ 4 * (1 / (mW n : ℝ)) := by
      rw [div_le_iff₀ (by positivity)]
      have e2 : 1 / 10 ^ 4 * (1 / (mW n : ℝ)) * (mW n : ℝ) ^ 2 = 1 / 10 ^ 4 * (mW n : ℝ) := by
        field_simp
      rw [e2]
      linarith
    have e3 : 10 / (mW n : ℝ) = 10 * (1 / (mW n : ℝ)) := by ring
    have h2 : (0 : ℝ) ≤ 1 / (mW n : ℝ) := by positivity
    rw [e3]
    nlinarith
  have harW0 : 0 ≤ arW n := Real.sqrt_nonneg _
  have hsq1 : √(1 + arW n) ≤ 100001 / 100000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    nlinarith
  -- `ε`
  have hε : εPap n ≤ 254 / 1000 * r := by
    have e : (254 / 1000 : ℝ) * r = √((254 / 1000) ^ 2 * (1 / (mW n : ℝ))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)]
    rw [e]
    unfold εPap
    refine Real.sqrt_le_sqrt ?_
    have e2 : (645 : ℝ) / 10 ^ 4 / (mW n : ℝ) = 645 / 10 ^ 4 * (1 / (mW n : ℝ)) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hε0 : 0 ≤ εPap n := Real.sqrt_nonneg _
  have hεκ : εPap n / kap1 (2 * n) ≤ 5145 / 10000 * r := by
    rw [div_le_iff₀ hκ]
    have h1 : 254 / 1000 * r ≤ 5145 / 10000 * r * (49372 / 100000) := by nlinarith
    have h2 : 5145 / 10000 * r * (49372 / 100000) ≤ 5145 / 10000 * r * kap1 (2 * n) :=
      mul_le_mul_of_nonneg_left hk1 (by positivity)
    linarith
  have hεκ0 : 0 ≤ εPap n / kap1 (2 * n) := div_nonneg hε0 hκ.le
  have hcH := cHat2_div_le hn4
  have hcH0 : 0 ≤ cHat2 (2 * n) (mW n) / kap1 (2 * n) :=
    div_nonneg (BstLean.Part140.cHat2_nonneg _ _) hκ.le
  -- `l_x`
  have hlx : lxG n (εPap n) (ρPap n) (1001 / 1000) ≤ 6271 / 1000 * r := by
    unfold lxG ρPap
    have t1 : 1001 / 1000 * (cHat2 (2 * n) (mW n) / kap1 (2 * n)) ≤
        1001 / 1000 * (5741 / 1000 * r) := mul_le_mul_of_nonneg_left hcH (by norm_num)
    have t3 : 1001 / 1000 * (εPap n / kap1 (2 * n)) * √(1 + arW n) ≤
        1001 / 1000 * (5145 / 10000 * r) * (100001 / 100000) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hεκ (by norm_num)) hsq1 (Real.sqrt_nonneg _)
        (by positivity)
    nlinarith
  have hlx0 : 0 ≤ lxG n (εPap n) (ρPap n) (1001 / 1000) := by
    unfold lxG ρPap
    positivity
  -- the two terms
  have hc := cRhoG_pap
  have hcpos : 0 < cRhoG (1994 / 1000) (2057 / 1000) (1 / 20) := by linarith
  set lx := lxG n (εPap n) (ρPap n) (1001 / 1000) with hlxdef
  set cρ := cRhoG (1994 / 1000) (2057 / 1000) (1 / 20) with hcρ
  have hΩ : 2057 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx) ≤ 36509 / 1000 * r := by
    have h1 : arW n + (2 + 1 / 20) * lx ≤ (31623 / 10000 + (2 + 1 / 20) * (6271 / 1000)) * r := by
      nlinarith
    have h2 : (2057 / 1000 / (1 - 1 / 20) ^ 2 : ℝ) *
        ((31623 / 10000 + (2 + 1 / 20) * (6271 / 1000)) * r) ≤ 36509 / 1000 * r := by
      have : (2057 / 1000 / (1 - 1 / 20) ^ 2 : ℝ) *
          (31623 / 10000 + (2 + 1 / 20) * (6271 / 1000)) ≤ 36509 / 1000 := by norm_num
      nlinarith
    exact (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans h2
  have hΩ0 : 0 ≤ 2057 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx) := by positivity
  have hΩ2 : (2057 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx)) ^ 2 ≤
      (36509 / 1000) ^ 2 * (1 / (mW n : ℝ)) := by
    have h9 := pow_le_pow_left₀ hΩ0 hΩ 2
    have e9 : (36509 / 1000 * r) ^ 2 = (36509 / 1000) ^ 2 * (1 / (mW n : ℝ)) := by
      rw [mul_pow, hr2]
    rw [e9] at h9
    exact h9
  have hfac : (n : ℝ) / ((1994 / 1000 - 1) ^ 2 * cρ) ≤
      (n : ℝ) / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) :=
    div_le_div_of_nonneg_left hnpos.le (by norm_num)
      (mul_le_mul_of_nonneg_left hc (by norm_num))
  have hfirst : (n : ℝ) / ((1994 / 1000 - 1) ^ 2 * cρ) *
      (2057 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx)) ^ 2 ≤
      (n : ℝ) / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) *
        ((36509 / 1000) ^ 2 * (1 / (mW n : ℝ))) :=
    mul_le_mul hfac hΩ2 (sq_nonneg _) (by positivity)
  have ha2 : arW n ^ 2 ≤ (31623 / 10000) ^ 2 * (1 / (mW n : ℝ)) := by
    have := pow_le_pow_left₀ harW0 harW 2
    rwa [mul_pow, hr2] at this
  have hl2 : lx ^ 2 ≤ (6271 / 1000) ^ 2 * (1 / (mW n : ℝ)) := by
    have := pow_le_pow_left₀ hlx0 hlx 2
    rwa [mul_pow, hr2] at this
  have hsecond : 2 * ((arW n ^ 2 + lx ^ 2) / (1 / 20) ^ 2) ≤
      2 * ((((31623 / 10000) ^ 2 + (6271 / 1000) ^ 2) * (1 / (mW n : ℝ))) / (1 / 20) ^ 2) := by
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (by norm_num)) (by norm_num)
    linarith
  obtain ⟨a1, a2⟩ := inv_mW_le hn
  have b1 : 1 / (128 * (n : ℝ) ^ 2) ≤ 1 / (128 * (16384 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) (by gcongr)
  have b2 : 1 / (128 * (n : ℝ) ^ 3) ≤ 1 / (128 * (16384 : ℝ) ^ 3) :=
    one_div_le_one_div_of_le (by norm_num) (by gcongr)
  have e1 : (n : ℝ) / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) *
      ((36509 / 1000) ^ 2 * (1 / (mW n : ℝ))) =
      (36509 / 1000) ^ 2 / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) * ((n : ℝ) / (mW n : ℝ)) := by
    field_simp
  have e2 : 2 * ((((31623 / 10000) ^ 2 + (6271 / 1000) ^ 2) * (1 / (mW n : ℝ))) /
      (1 / 20) ^ 2) =
      2 * ((31623 / 10000) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2 * (1 / (mW n : ℝ)) := by
    ring
  have c1 : (36509 / 1000 : ℝ) ^ 2 / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) *
      ((n : ℝ) / (mW n : ℝ)) ≤
      (36509 / 1000 : ℝ) ^ 2 / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) *
        (1 / (128 * (16384 : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (a1.trans b1) (by norm_num)
  have c2 : (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
      (1 / (mW n : ℝ)) ≤
      (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
        (1 / (128 * (16384 : ℝ) ^ 3)) :=
    mul_le_mul_of_nonneg_left (a2.trans b2) (by norm_num)
  have c3 : (36509 / 1000 : ℝ) ^ 2 / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) *
        (1 / (128 * (16384 : ℝ) ^ 2)) +
      (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
        (1 / (128 * (16384 : ℝ) ^ 3)) ≤ 737 / 10 ^ 11 := by norm_num
  rw [e1] at hfirst
  rw [e2] at hsecond
  linarith

/-- **The Hellinger moment for the centre and the scalar of the paper.** For `n ≥ 16 384`, IF
`ConstC n` and `ConstK n`: there is a majorant `K` of `E_u H_u²` on `GPap n` with
`E[1_{GPap}·K] ≤ vPap = 7.37·10⁻⁹`. -/
theorem pap_moment (hn : 16384 ≤ n) (hC : ConstC n) (hK : ConstK n) :
    ∃ K : WHid n → ℝ, Integrable ((GPap n).indicator K) (hidGauss (2 * n) (mW n)) ∧
      (∀ θ ∈ GPap n, hellHid bWp tau0p θ ≤ K θ) ∧
      ∫ θ, (GPap n).indicator K θ ∂hidGauss (2 * n) (mW n) ≤ vPap := by
  have hn4 : 4096 ≤ n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have := mW_ge_million hn4
    exact_mod_cast (by omega : 0 < mW n)
  have hε2 : εPap n ^ 2 = 645 / 10 ^ 4 / (mW n : ℝ) := by
    unfold εPap
    exact Real.sq_sqrt (by positivity)
  obtain ⟨K, iK, hle, hint⟩ := pert_moment hn4 (b := bWp) measurable_bWp (cc := ccP n)
    (τ := tau0p) measurable_ccP (measurableSet_GPap (n := n) (by omega))
    (ε := εPap n) (ρ₂ := ρPap n) (Alo := 1994 / 1000) (Ahi := 2057 / 1000) (qhi := 1001 / 1000)
    (ζ := 1 / 20) (Real.sqrt_nonneg _) (by unfold ρPap; positivity) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun θ hθ => by rw [hε2]; exact bWp_dist (by omega) hC hθ.1.2 hθ.2)
    (fun θ hθ => ⟨(pap_window hn hC hK hθ).1, (pap_q (by omega) hK hθ.1.2).1⟩)
    (fun θ hθ => (pap_window hn hC hK hθ).2)
    (fun θ hθ => pap_tau hn hC hK hθ)
    (pap_qL2 (by omega) hK)
  exact ⟨K, iK, hle, hint.trans (vPert_pap_le hn)⟩

/-! ## The World hypotheses of Part 157 for the centre of the paper -/

/-- **The hidden World event for the centre of the paper**, as a set of retained data. -/
def HP (n : ℕ) : Set (Ret n) := Hof (GPap n)

/-- **`FRAME_W_hyp` for the World centre of the paper** (`1.377/n`; Lean has `1.36/n`), on every
set of retained data inside `HP n`, IF `ConstC n`. -/
theorem frame_w_paper (hn : 16384 ≤ n) (hC : ConstC n) (D : Centres n) (hD : D.bW = bWp)
    {E : Set (Ret n)} (hE : E ⊆ HP n) : FRAME_W_hyp D (cWL / n) E := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  refine frame_of_hid D (G := GPap n) (fun θ hθ w => ?_) hE
  rw [hD]
  have hc : (136 / 100 / (n : ℝ)) ≤ cWL / (n : ℝ) :=
    div_le_div_of_nonneg_right (by unfold cWL; norm_num) hnpos.le
  exact (pap_frame hn hC hθ w).trans
    (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun j _ => sq_nonneg _))

/-- **`EVENTS_hyp` with the World parts PROVED for the centre and the scalar of the paper**, IF
`ConstC n` and `ConstK n`: hidden charge `δPap = 0.00163204`, Hellinger moment
`vPap = 7.37·10⁻⁹`. -/
theorem events_paper (hn : 16384 ≤ n) (hC : ConstC n) (hK : ConstK n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁) {δextra : ℝ}
    (h3 : (retDist D.toCentres).real (HP n ∩ E₁ᶜ) ≤ δextra) :
    EVENTS_hyp D.toCentres (HP n) E₁ (HbarW D) δPap vPap δextra := by
  obtain ⟨K, iK, hle, hint⟩ := pap_moment hn hC hK
  refine events_of_hid (by omega) D (measurableSet_GPap (by omega)) iK (fun c hc => ?_) hE₁
    (pap_charge hn) hint h3
  rw [HbarW2_eq_hellHid D c (hτ c), hD]
  exact hle c.1.1 hc

/-- **The conditional classifier theorem for a design with the World centre and the scalar of the
paper, with only Agent-side hypotheses and two hypotheses on the computed constants (every
`n ≥ 16 384`).** -/
theorem classifier_networks_conditional_agent_paperW (hn : 16384 ≤ n) (hC : ConstC n)
    (hK : ConstK n) (D : Design n) (hD : D.bW = bWp)
    (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist D.toCentres).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet (HP n) E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet (HP n) E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_frames hn D t
    (events_mono (events_paper hn hC hK D hD hτ hE₁ hextra) δPap_le vPap_le le_rfl)
    (frame_w_paper hn hC D.toCentres hD (fun _ hc => hc.1.1)) hFA hRA

/-- **The conditional classifier theorem for the design of the paper's program (every
`n ≥ 16 384`).** The design is `paperDesign n fT wT` of Part 157: the binomial World centre and
`τ₀` of step 2, the Agent centre of step 3, the sampling of steps 4 and 6 with stored tables
`fT`, `wT`. IF the two computed constants of the program have `ConstC n` (`c̃_N` against `c_N`)
and `ConstK n` (`κ̃` against `κ₁`), `E₁` is a measurable event of the retained data with
`Pr(HP n ∩ E₁ᶜ) ≤ δ_extra`, and on `HP n ∩ {H̄_W ≤ h_W} ∩ E₁` the Agent frame bound and the
Agent replacement root hold, THEN the program succeeds with probability at least `99/100`. The
World frame bound, the hidden event with its charge and the Hellinger moment are PROVED. -/
theorem classifier_paper_conditional_agent (hn : 16384 ≤ n) (hC : ConstC n) (hK : ConstK n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {E₁ : Set (Ret n)}
    (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_agent_paperW hn hC hK (paperDesign n fT wT hf hw) rfl
    (fun _ => rfl) t hE₁ hextra hFA hRA

end BstLean.Part159

open BstLean.Part159 in
#print axioms vPert_pap_le
open BstLean.Part159 in
#print axioms pap_moment
open BstLean.Part159 in
#print axioms frame_w_paper
open BstLean.Part159 in
#print axioms events_paper
open BstLean.Part159 in
#print axioms classifier_networks_conditional_agent_paperW
open BstLean.Part159 in
#print axioms classifier_paper_conditional_agent
