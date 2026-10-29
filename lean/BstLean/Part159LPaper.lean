import BstLean.Part159LFrame

/-!
# Part 159 (file `LPaper`): the World package for the design of the paper, every `n ≥ 13 225`

Role: `delegations/statements/p159-spec.md`, item 3 (a larger overlap with the frontier interval
`4 096 ≤ n ≤ 16 384`). Do not use `sorry`, `native_decide` or `axiom`.

Files `Paper`, `PaperF`, `PaperW`, `Uncond` have the World package for `n ≥ 16 384` at the
constants of the ledger of Part 156. This file has the same package for every `n ≥ 13 225` (the
range of the `L` lemmas of Part 143), with weaker constants:

* `pap_charge_L`: `Pr((GPap n)ᶜ) ≤ 0.0019736`.
* `pap_frame_L`: the frame bound `1.40/n`.
* `pap_moment_L`: the Hellinger moment `≤ 1.276·10⁻⁸`.
* `theta_window_paper_L`: `0.991 ≤ w₀ ≤ 1.060`, `0.464 ≤ θ_in ≤ 0.531`; `world_window_up`: the
  window in the form of Corollary `t7:p02:window-up` of the paper.
* `paper_world_L`: `EVENTS_hyp` (World parts) and `FRAME_W_hyp` for `paperDesign`.
* **`classifier_paper_agent_free_L`**: the conditional theorem with free Agent constants for
  `paperDesign`, every `n ≥ 13 225`.

The numeric ledger of Part 156 is for `n ≥ 16 384` only: below `16 384` there is no Lean
statement at the level `99/100`; the bound of the failure probability is a formula.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le)
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN mW_ge_pow42 cHat2)
open BstLean.Part140
open BstLean.Part143 (nsq_div_mW_le115 goodHat_compl143L cExtra143L)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- The bound of the hidden charge of `goodHat n` for `n ≥ 13 225`: `0.0019735`. -/
noncomputable def δHatL : ℝ := 19735 / 10 ^ 7

/-- **The hidden charge of the computed centre, `n ≥ 13 225`** (from Part 143). -/
theorem hat_charge_L {n : ℕ} (hn : 13225 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ δHatL := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have h := goodHat_compl143L hn
  have h2 : cExtra143L / (n : ℝ) ≤ cExtra143L / 13225 :=
    div_le_div_of_nonneg_left (by unfold cExtra143L; norm_num) (by norm_num) hn'
  have h3 : (775 : ℝ) / 1000000 + cExtra143L / 13225 ≤ δHatL := by
    unfold cExtra143L δHatL; norm_num
  linarith

/-- `n/m_W ≤ 1/(115 n²)` and `1/m_W ≤ 1/(115 n³)` for `n ≥ 13 225`. -/
lemma inv_mW_le_L {n : ℕ} (hn : 13225 ≤ n) :
    (n : ℝ) / (mW n : ℝ) ≤ 1 / (115 * (n : ℝ) ^ 2) ∧ 1 / (mW n : ℝ) ≤ 1 / (115 * (n : ℝ) ^ 3) := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million (n := n) (by omega)
    exact_mod_cast (by omega : 0 < mW n)
  have h := nsq_div_mW_le115 hn
  have e1 : (n : ℝ) / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / (n : ℝ) := by field_simp
  have e2 : 1 / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / (n : ℝ) ^ 2 := by field_simp
  constructor
  · rw [e1]
    refine (div_le_div_of_nonneg_right h hnpos.le).trans (le_of_eq ?_)
    field_simp
  · rw [e2]
    refine (div_le_div_of_nonneg_right h (by positivity)).trans (le_of_eq ?_)
    field_simp

/-- The window of `B = t_W|b_W|²` on `GPap n`, `n ≥ 13 225`: `0.48612·γ ≤ B ≤ 0.50154·γ`. -/
lemma pap_B_L (hn : 13225 ≤ n) {θ : WHid n} (hθ : θ ∈ GPap n) :
    2 / ((2 * n : ℕ) : ℝ) * (48612 / 100000) ≤ 2 / (mW n : ℝ) * normSq (bWp θ) ∧
      2 / (mW n : ℝ) * normSq (bWp θ) ≤ 2 / ((2 * n : ℕ) : ℝ) * (50154 / 100000) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ 2 / (mW n : ℝ) := by positivity
  obtain ⟨hb1, hb2⟩ := Bh_window_L hn hθ.1.1
  unfold Bh at hb1 hb2
  have hd := bWp_dist hn (constC hn) hθ.1.2 hθ.2
  set δ := bWp θ - bhat θ with hδ
  have hdm : 2 / (mW n : ℝ) * normSq δ ≤ 2 / ((2 * n : ℕ) : ℝ) * (2 / 10 ^ 14) := by
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ hγ.le)
    rw [div_le_iff₀ hmpos]
    nlinarith
  have e1 : bWp θ = bhat θ + δ := by rw [hδ]; abel
  have e2 : bhat θ = bWp θ + (-δ) := by rw [hδ]; abel
  have hneg : normSq (-δ) = normSq δ := by simp [normSq]
  have h1 := normSq_add_eta (η := 1 / 10 ^ 6) (by norm_num) (bhat θ) δ
  rw [← e1] at h1
  have h2 := normSq_add_eta (η := 1 / 10 ^ 6) (by norm_num) (bWp θ) (-δ)
  rw [← e2, hneg] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 ht
  have h2' := mul_le_mul_of_nonneg_left h2 ht
  have hδ0 : 0 ≤ 2 / (mW n : ℝ) * normSq δ := mul_nonneg ht (normSq_nonneg _)
  set γ := (2 : ℝ) / ((2 * n : ℕ) : ℝ) with hγdef
  set Bb := 2 / (mW n : ℝ) * normSq (bWp θ) with hBb
  set Bh' := 2 / (mW n : ℝ) * normSq (bhat θ) with hBh
  set Dd := 2 / (mW n : ℝ) * normSq δ with hDd
  have h1'' : Bb ≤ (1 + 1 / 10 ^ 6) * Bh' + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
    have : 2 / (mW n : ℝ) * ((1 + 1 / 10 ^ 6) * normSq (bhat θ) +
        (1 + 1 / (1 / 10 ^ 6 : ℝ)) * normSq δ) =
        (1 + 1 / 10 ^ 6) * Bh' + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
      rw [hBh, hDd]; ring
    linarith
  have h2'' : Bh' ≤ (1 + 1 / 10 ^ 6) * Bb + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
    have : 2 / (mW n : ℝ) * ((1 + 1 / 10 ^ 6) * normSq (bWp θ) +
        (1 + 1 / (1 / 10 ^ 6 : ℝ)) * normSq δ) =
        (1 + 1 / 10 ^ 6) * Bb + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
      rw [hBb, hDd]; ring
    linarith
  have h3 : (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd ≤ γ * (3 / 10 ^ 8) := by
    have : (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd ≤ (1 + 1 / (1 / 10 ^ 6 : ℝ)) * (γ * (2 / 10 ^ 14)) :=
      mul_le_mul_of_nonneg_left hdm (by norm_num)
    nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- **The window of `B·c`** for the scalar of the paper on `GPap n`, `n ≥ 13 225`:
`1.991 ≤ B·c ≤ 2.060`, and `c ≥ 0`. -/
lemma pap_window_L (hn : 13225 ≤ n) {θ : WHid n} (hθ : θ ∈ GPap n) :
    0 ≤ ccP n θ ∧ 1991 / 1000 ≤ 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ∧
      2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ≤ 2060 / 1000 := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hκ1, hκ2⟩ := kapT_window hn (constK hn)
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hθ.1.2
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 1998 / 1000 ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2002 / 1000 := by linarith
  obtain ⟨hB1, hB2⟩ := pap_B_L hn hθ
  rw [hNcast] at hB1 hB2
  set Bb := 2 / (mW n : ℝ) * normSq (bWp θ) with hBb
  have hκ0 : 0 < kapT n := by linarith
  have hSκ : 0 < SWp θ * kapT n ^ 2 := by positivity
  have hκsq1 : (493719 / 1000000 : ℝ) ^ 2 ≤ kapT n ^ 2 := pow_le_pow_left₀ (by norm_num) hκ1 2
  have hκsq2 : kapT n ^ 2 ≤ (493801 / 1000000 : ℝ) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
  have hSκ1 : 1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2 ≤ SWp θ * kapT n ^ 2 :=
    mul_le_mul hS1 hκsq1 (by norm_num) (by linarith)
  have hSκ2 : SWp θ * kapT n ^ 2 ≤ 2002 / 1000 * (493801 / 1000000 : ℝ) ^ 2 :=
    mul_le_mul hS2 hκsq2 (sq_nonneg _) (by norm_num)
  have hcc0 : 0 ≤ ccP n θ := by unfold ccP; positivity
  have e : Bb * ccP n θ = Bb * (2 * (n : ℝ)) / (SWp θ * kapT n ^ 2) := by
    unfold ccP; ring
  have hBn1 : 2 * (48612 / 100000 : ℝ) ≤ Bb * (2 * (n : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hB1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have e2 : 2 / (2 * (n : ℝ)) * (48612 / 100000) * (2 * (n : ℝ)) = 2 * (48612 / 100000) := by
      field_simp
    linarith
  have hBn2 : Bb * (2 * (n : ℝ)) ≤ 2 * (50154 / 100000 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hB2 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have e2 : 2 / (2 * (n : ℝ)) * (50154 / 100000) * (2 * (n : ℝ)) = 2 * (50154 / 100000) := by
      field_simp
    linarith
  refine ⟨hcc0, ?_, ?_⟩
  · rw [e, le_div_iff₀ hSκ]
    have : (1991 / 1000 : ℝ) * (2002 / 1000 * (493801 / 1000000 : ℝ) ^ 2) ≤
        2 * (48612 / 100000) := by norm_num
    nlinarith
  · rw [e, div_le_iff₀ hSκ]
    have : 2 * (50154 / 100000 : ℝ) ≤
        2060 / 1000 * (1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2) := by norm_num
    nlinarith


/-- The bound of the Hellinger moment for the centre of the paper, `n ≥ 13 225`: `1.276·10⁻⁸`. -/
noncomputable def vPapL : ℝ := 1276 / 10 ^ 11

/-- `c_ρ ≥ 5.37` at `A_lo = 1.991`, `A_hi = 2.060`, `ζ = 1/20`. -/
lemma cRhoG_pap_L : 537 / 100 ≤ cRhoG (1991 / 1000) (2060 / 1000) (1 / 20) := by
  have hr : 6487 / 10000 ≤ rLowG (1991 / 1000) (2060 / 1000) (1 / 20) := by
    unfold rLowG zetaG
    refine le_trans ?_ (le_max_right _ _)
    norm_num
  have hs : 8054 / 10000 ≤ √(rLowG (1991 / 1000) (2060 / 1000) (1 / 20)) :=
    Real.le_sqrt_of_sq_le (le_trans (by norm_num) hr)
  unfold cRhoG
  have h1 : (1 + 8054 / 10000 : ℝ) ^ 2 ≤
      (1 + √(rLowG (1991 / 1000) (2060 / 1000) (1 / 20))) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h2 : (537 / 100 : ℝ) ≤ (1 + 8054 / 10000) ^ 2 * (1 + 6487 / 10000) := by norm_num
  have h3 : (1 + 8054 / 10000 : ℝ) ^ 2 * (1 + 6487 / 10000) ≤
      (1 + √(rLowG (1991 / 1000) (2060 / 1000) (1 / 20))) ^ 2 *
        (1 + rLowG (1991 / 1000) (2060 / 1000) (1 / 20)) :=
    mul_le_mul h1 (by linarith) (by norm_num) (sq_nonneg _)
  linarith

/-- **The numeric bound of the Hellinger moment for the centre of the paper** (`n ≥ 13 225`). -/
theorem vPert_pap_le_L (hn : 13225 ≤ n) :
    vPert n (εPap n) (ρPap n) (1991 / 1000) (2060 / 1000) (1001 / 1000) (1 / 20) ≤ vPapL := by
  unfold vPert vPapL
  have hn4 : 4096 ≤ n := by omega
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
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
  have hc := cRhoG_pap_L
  have hcpos : 0 < cRhoG (1991 / 1000) (2060 / 1000) (1 / 20) := by linarith
  set lx := lxG n (εPap n) (ρPap n) (1001 / 1000) with hlxdef
  set cρ := cRhoG (1991 / 1000) (2060 / 1000) (1 / 20) with hcρ
  have hΩ : 2060 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx) ≤ 36562 / 1000 * r := by
    have h1 : arW n + (2 + 1 / 20) * lx ≤ (31623 / 10000 + (2 + 1 / 20) * (6271 / 1000)) * r := by
      nlinarith
    have h2 : (2060 / 1000 / (1 - 1 / 20) ^ 2 : ℝ) *
        ((31623 / 10000 + (2 + 1 / 20) * (6271 / 1000)) * r) ≤ 36562 / 1000 * r := by
      have : (2060 / 1000 / (1 - 1 / 20) ^ 2 : ℝ) *
          (31623 / 10000 + (2 + 1 / 20) * (6271 / 1000)) ≤ 36562 / 1000 := by norm_num
      nlinarith
    exact (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans h2
  have hΩ0 : 0 ≤ 2060 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx) := by positivity
  have hΩ2 : (2060 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx)) ^ 2 ≤
      (36562 / 1000) ^ 2 * (1 / (mW n : ℝ)) := by
    have h9 := pow_le_pow_left₀ hΩ0 hΩ 2
    have e9 : (36562 / 1000 * r) ^ 2 = (36562 / 1000) ^ 2 * (1 / (mW n : ℝ)) := by
      rw [mul_pow, hr2]
    rw [e9] at h9
    exact h9
  have hfac : (n : ℝ) / ((1991 / 1000 - 1) ^ 2 * cρ) ≤
      (n : ℝ) / ((1991 / 1000 - 1) ^ 2 * (537 / 100)) :=
    div_le_div_of_nonneg_left hnpos.le (by norm_num)
      (mul_le_mul_of_nonneg_left hc (by norm_num))
  have hfirst : (n : ℝ) / ((1991 / 1000 - 1) ^ 2 * cρ) *
      (2060 / 1000 / (1 - 1 / 20) ^ 2 * (arW n + (2 + 1 / 20) * lx)) ^ 2 ≤
      (n : ℝ) / ((1991 / 1000 - 1) ^ 2 * (537 / 100)) *
        ((36562 / 1000) ^ 2 * (1 / (mW n : ℝ))) :=
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
  obtain ⟨a1, a2⟩ := inv_mW_le_L hn
  have b1 : 1 / (115 * (n : ℝ) ^ 2) ≤ 1 / (115 * (13225 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) (by gcongr)
  have b2 : 1 / (115 * (n : ℝ) ^ 3) ≤ 1 / (115 * (13225 : ℝ) ^ 3) :=
    one_div_le_one_div_of_le (by norm_num) (by gcongr)
  have e1 : (n : ℝ) / ((1991 / 1000 - 1) ^ 2 * (537 / 100)) *
      ((36562 / 1000) ^ 2 * (1 / (mW n : ℝ))) =
      (36562 / 1000) ^ 2 / ((1991 / 1000 - 1) ^ 2 * (537 / 100)) * ((n : ℝ) / (mW n : ℝ)) := by
    field_simp
  have e2 : 2 * ((((31623 / 10000) ^ 2 + (6271 / 1000) ^ 2) * (1 / (mW n : ℝ))) /
      (1 / 20) ^ 2) =
      2 * ((31623 / 10000) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2 * (1 / (mW n : ℝ)) := by
    ring
  have c1 : (36562 / 1000 : ℝ) ^ 2 / ((1991 / 1000 - 1) ^ 2 * (537 / 100)) *
      ((n : ℝ) / (mW n : ℝ)) ≤
      (36562 / 1000 : ℝ) ^ 2 / ((1991 / 1000 - 1) ^ 2 * (537 / 100)) *
        (1 / (115 * (13225 : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (a1.trans b1) (by norm_num)
  have c2 : (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
      (1 / (mW n : ℝ)) ≤
      (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
        (1 / (115 * (13225 : ℝ) ^ 3)) :=
    mul_le_mul_of_nonneg_left (a2.trans b2) (by norm_num)
  have c3 : (36562 / 1000 : ℝ) ^ 2 / ((1991 / 1000 - 1) ^ 2 * (537 / 100)) *
        (1 / (115 * (13225 : ℝ) ^ 2)) +
      (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
        (1 / (115 * (13225 : ℝ) ^ 3)) ≤ 1276 / 10 ^ 11 := by norm_num
  rw [e1] at hfirst
  rw [e2] at hsecond
  linarith

/-- The bound of the hidden charge for the centre of the paper, `n ≥ 13 225`: `0.0019736`. -/
noncomputable def δPapL : ℝ := 19736 / 10 ^ 7

/-- **The hidden charge for the centre of the paper, `n ≥ 13 225`.** -/
theorem pap_charge_L (hn : 13225 ≤ n) : (hidGauss (2 * n) (mW n)).real (GPap n)ᶜ ≤ δPapL := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h1 := hat_charge_L hn
  have h2 := goodS_charge (n := n) (by omega) hm
  have h3 := goodAo_charge hn4
  have hsub : (GPap n)ᶜ ⊆ ((goodHat n)ᶜ ∪ (goodS n)ᶜ) ∪ (goodAo n)ᶜ := by
    intro θ hθ
    simp only [GPap, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 := (measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have h5 : (10 : ℝ) ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) ≤ 1 / 10 ^ 8 := by
    have e : (10 : ℝ) ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) =
        10 ^ 6 / ((n : ℝ) * (mW n : ℝ)) := by
      rw [hNcast]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  unfold δPapL
  unfold δHatL at h1
  have h6 : (19735 / 10 ^ 7 : ℝ) + 1 / 10 ^ 8 + 9 / 10 ^ 8 ≤ 19736 / 10 ^ 7 := by norm_num
  linarith

/-- **The frame bound for the centre of the paper, `n ≥ 13 225`**: `1.40/n` on `GPap n`. -/
theorem pap_frame_L (hn : 13225 ≤ n) {θ : WHid n} (hθ : θ ∈ GPap n) (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bWp θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      140 / 100 / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 (by omega)
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hd := bWp_dist hn (constC hn) hθ.1.2 hθ.2
  refine pert_frame_L hn hθ.1.1 (e₁ := 645 / 10 ^ 4 * (n : ℝ) / (mW n : ℝ)) ?_ ?_ w
  · have h := nsq_div_mW_le115 hn
    have e : 645 / 10 ^ 4 * (n : ℝ) / (mW n : ℝ) =
        645 / 10 ^ 4 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) := by field_simp
    rw [e, div_le_iff₀ hnpos]
    have h2 : 1 / (115 * (n : ℝ)) ≤ 1 / (115 * 13225) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    nlinarith
  · refine hd.trans (le_of_eq ?_)
    field_simp

/-- **The Hellinger moment for the centre and the scalar of the paper, `n ≥ 13 225`**: a majorant
`K` of `E_u H_u²` on `GPap n` with `E[1_{GPap}·K] ≤ vPapL = 1.276·10⁻⁸`. -/
theorem pap_moment_L (hn : 13225 ≤ n) :
    ∃ K : WHid n → ℝ, Integrable ((GPap n).indicator K) (hidGauss (2 * n) (mW n)) ∧
      (∀ θ ∈ GPap n, hellHid bWp tau0p θ ≤ K θ) ∧
      ∫ θ, (GPap n).indicator K θ ∂hidGauss (2 * n) (mW n) ≤ vPapL := by
  have hn4 : 4096 ≤ n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have := mW_ge_million hn4
    exact_mod_cast (by omega : 0 < mW n)
  have hε2 : εPap n ^ 2 = 645 / 10 ^ 4 / (mW n : ℝ) := by
    unfold εPap
    exact Real.sq_sqrt (by positivity)
  obtain ⟨K, iK, hle, hint⟩ := pert_moment hn4 (b := bWp) measurable_bWp (cc := ccP n)
    (τ := tau0p) measurable_ccP (measurableSet_GPap (n := n) (by omega))
    (ε := εPap n) (ρ₂ := ρPap n) (Alo := 1991 / 1000) (Ahi := 2060 / 1000) (qhi := 1001 / 1000)
    (ζ := 1 / 20) (Real.sqrt_nonneg _) (by unfold ρPap; positivity) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun θ hθ => by rw [hε2]; exact bWp_dist hn (constC hn) hθ.1.2 hθ.2)
    (fun θ hθ => ⟨(pap_window_L hn hθ).1, (pap_q hn (constK hn) hθ.1.2).1⟩)
    (fun θ hθ => (pap_window_L hn hθ).2)
    (fun θ hθ => tau0p_of (by linarith [(pap_window_L hn hθ).2.1]))
    (pap_qL2 hn (constK hn))
  exact ⟨K, iK, hle, hint.trans (vPert_pap_le_L hn)⟩

/-! ## The World hypotheses of Part 157, `n ≥ 13 225` -/

/-- **`FRAME_W_hyp` for the World centre of the paper, `n ≥ 13 225`**, with the constant
`1.40/n`, on every set of retained data inside `HP n`. -/
theorem frame_w_paper_L (hn : 13225 ≤ n) (D : Centres n) (hD : D.bW = bWp)
    {E : Set (Ret n)} (hE : E ⊆ HP n) : FRAME_W_hyp D (140 / 100 / n) E := by
  refine frame_of_hid D (G := GPap n) (fun θ hθ w => ?_) hE
  rw [hD]
  exact pap_frame_L hn hθ w

/-- **`EVENTS_hyp` with the World parts PROVED for the centre and the scalar of the paper,
`n ≥ 13 225`**: hidden charge `δPapL = 0.0019736`, Hellinger moment `vPapL = 1.276·10⁻⁸`. -/
theorem events_paper_L (hn : 13225 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁) {δextra : ℝ}
    (h3 : (retDist D.toCentres).real (HP n ∩ E₁ᶜ) ≤ δextra) :
    EVENTS_hyp D.toCentres (HP n) E₁ (HbarW D) δPapL vPapL δextra := by
  obtain ⟨K, iK, hle, hint⟩ := pap_moment_L hn
  refine events_of_hid (by omega) D (measurableSet_GPap (by omega)) iK (fun c hc => ?_) hE₁
    (pap_charge_L hn) hint h3
  rw [HbarW2_eq_hellHid D c (hτ c), hD]
  exact hle c.1.1 hc

lemma sqrt12n_le_L (hn : 13225 ≤ n) : √(12 / (n : ℝ)) ≤ 30123 / 1000000 := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The retained World window for the centre and the scalar of the paper, every `n ≥ 13 225`**
(Lemma `t7:p02:window`): on `HP n`: `τ₀ > 0`, `τ₀² = t_W|b_W|²·w₀`, `0.991 ≤ w₀ ≤ 1.060`; on
`HP n ∩ E_{θ−}`: `θ_in ≥ 0.464`; on `HP n ∩ E_{θ+}`: `θ_in ≤ 0.531`. -/
theorem theta_window_paper_L (hn : 13225 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) {c : Ret n} (hc : c ∈ HP n) :
    0 < D.tau0 c ∧
      D.tau0 c ^ 2 = 2 / (mW n : ℝ) * normSq (D.bW c.1.1) *
        (2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1) ∧
      991 / 1000 ≤ 2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ∧
      2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ≤ 1060 / 1000 ∧
      (c ∈ Ethm D.toCentres → 464 / 1000 ≤ thetaIn D c) ∧
      (c ∈ Ethp D.toCentres → thetaIn D c ≤ 531 / 1000) := by
  have hθ : c.1.1 ∈ GPap n := hc
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨-, hA1, hA2⟩ := pap_window_L hn hθ
  obtain ⟨t2, t1⟩ := tau0p_of (θ := c.1.1) (by linarith)
  rw [hD, hτ]
  set B := 2 / (mW n : ℝ) * normSq (bWp c.1.1) with hB
  set w0 := B * ccP n c.1.1 - 1 with hw0
  have t3 : 991 / 1000 ≤ w0 := by linarith
  have t4 : w0 ≤ 1060 / 1000 := by linarith
  have hBnn : 0 ≤ B := mul_nonneg (by positivity) (normSq_nonneg _)
  have hBpos : 0 < B := by
    rcases hBnn.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hA1; norm_num at hA1
    · exact h0
  have hnB : 0 < (n : ℝ) * B := by positivity
  refine ⟨t1, t2, t3, t4, ?_, ?_⟩
  · intro hm
    have h1 : normSq c.1.2 ≤ cUp * n * B := by
      have : normSq c.1.2 ≤ cUp * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) := hm
      rwa [hD] at this
    have hcu : cUp ≤ 1143166 / 1000000 := by
      unfold cUp
      have := sqrt45_bounds.2
      linarith
    unfold thetaIn
    rw [hτ, t2, le_div_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (B * w0) := by positivity
      linarith)]
    have h2 : normSq c.1.2 ≤ 1143166 / 1000000 * ((n : ℝ) * B) := by
      have := mul_le_mul_of_nonneg_right hcu hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t3 hnB.le]
  · intro hp
    have h1 : (1 - 2 * √(12 / (n : ℝ))) * n * B ≤ normSq c.1.2 := by
      have : (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) ≤
          normSq c.1.2 := hp
      rwa [hD] at this
    have hcl : (939754 / 1000000 : ℝ) ≤ 1 - 2 * √(12 / (n : ℝ)) := by
      have := sqrt12n_le_L hn
      linarith
    unfold thetaIn
    rw [hτ, t2, div_le_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (B * w0) := by positivity
      linarith)]
    have h2 : 939754 / 1000000 * ((n : ℝ) * B) ≤ normSq c.1.2 := by
      have := mul_le_mul_of_nonneg_right hcl hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t4 hnB.le]

/-- **The World window in the form of Corollary `t7:p02:window-up` of the paper, every
`n ≥ 13 225`** (the paper: `n ≥ 16 384`). For a design with the World centre `bWp` and the scalar
`tau0p`, on `HP n ∩ E_{θ−} ∩ E_{θ+}`: `b_W ≠ 0`, `|ĉ| > 0`, `τ₀ > 0`,
`0.977 ≤ w₀ ≤ 1/0.4815 − 1` and `0.46 ≤ θ_in ≤ 0.54`. -/
theorem world_window_up (hn : 13225 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) {c : Ret n} (hc : c ∈ HP n)
    (hm : c ∈ Ethm D.toCentres) (hp : c ∈ Ethp D.toCentres) :
    D.bW c.1.1 ≠ 0 ∧ 0 < normSq c.1.2 ∧ 0 < D.tau0 c ∧
      977 / 1000 ≤ 2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ∧
      2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ≤ 1 / (4815 / 10000) - 1 ∧
      46 / 100 ≤ thetaIn D c ∧ thetaIn D c ≤ 54 / 100 := by
  have hθ : c.1.1 ∈ GPap n := hc
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨t1, -, t3, t4, t5, t6⟩ := theta_window_paper_L hn D hD hτ hc
  obtain ⟨-, hA1, -⟩ := pap_window_L hn hθ
  have hBnn : 0 ≤ 2 / (mW n : ℝ) * normSq (bWp c.1.1) :=
    mul_nonneg (by positivity) (normSq_nonneg _)
  have hBpos : 0 < 2 / (mW n : ℝ) * normSq (bWp c.1.1) := by
    rcases hBnn.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hA1; norm_num at hA1
    · exact h0
  have hb : D.bW c.1.1 ≠ 0 := by
    rw [hD]
    intro h0
    rw [h0] at hBpos
    simp [normSq] at hBpos
  have hcl : (939754 / 1000000 : ℝ) ≤ 1 - 2 * √(12 / (n : ℝ)) := by
    have := sqrt12n_le_L hn
    linarith
  have hchat : 0 < normSq c.1.2 := by
    have h1 : (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) ≤
        normSq c.1.2 := hp
    rw [hD] at h1
    have h2 : 0 < (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (bWp c.1.1)) := by
      have : (0 : ℝ) < 1 - 2 * √(12 / (n : ℝ)) := by linarith
      positivity
    linarith
  refine ⟨hb, hchat, t1, by linarith, ?_, by linarith [t5 hm], by linarith [t6 hp]⟩
  have : (1060 / 1000 : ℝ) ≤ 1 / (4815 / 10000) - 1 := by norm_num
  linarith

/-- **The World package for the centre and the scalar of the paper's program, every
`n ≥ 13 225`**, for every design with `b_W = bWp`, `τ₀ = tau0p`. -/
theorem paper_world_L (hn : 13225 ≤ n) (D : Design n) (hD : D.bW = bWp)
    (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) :
    (∀ {E₁ : Set (Ret n)}, MeasurableSet E₁ → ∀ {δextra : ℝ},
      (retDist D.toCentres).real (HP n ∩ E₁ᶜ) ≤ δextra →
        EVENTS_hyp D.toCentres (HP n) E₁ (HbarW D) δPapL vPapL δextra) ∧
    (∀ {E : Set (Ret n)}, E ⊆ HP n → FRAME_W_hyp D.toCentres (140 / 100 / n) E) :=
  ⟨fun hE₁ _ h3 => events_paper_L hn D hD hτ hE₁ h3,
    fun hE => frame_w_paper_L hn D.toCentres hD hE⟩

/-- **The conditional classifier theorem for the design of the paper's program with free Agent
constants, every `n ≥ 13 225`.** The World constants are PROVED: hidden charge
`δPapL = 0.0019736`, Hellinger moment `vPapL = 1.276·10⁻⁸`, frame constant `c_W = 1.40`. The
constants `a`, `h_W`, `τ_±`, `c_frame`, `h_A`, `d_s`, `k` are free. IF the side conditions of
Part 156 hold, `E₁` has `Pr(HP n ∩ E₁ᶜ) ≤ δ_extra`, and on `HP n ∩ {H̄_W ≤ h_W} ∩ E₁` the Agent
frame bound `c_frame/n` and the Agent replacement root `h_A` hold, THEN the failure probability
is at most `δPapL + vPapL/h_W² + δ_extra + B_+ + B_− + 2·exp(−k·d_s²)`. -/
theorem classifier_paper_agent_free_L (hn : 13225 ≤ n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) (k : ℕ) {E₁ : Set (Ret n)}
    (hE₁ : MeasurableSet E₁) {δextra cf hW hA ds a τp τm : ℝ}
    (hcf : 0 < cf) (hhW : 0 < hW) (hhA : 0 ≤ hA) (hds : 0 < ds) (ha : 1 < a)
    (hτp : 0 < τp) (hτm : τm < 0)
    (hside1 : (hA + ds) + hW < √(1 / 100 / a)) (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW (140 / 100) cf τp ≤ 0)
    (hEm : Eminus a (hA + ds) hW (140 / 100) cf τm ≤ 0)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextra)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cf / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hW))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hA
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hW)) :
    ((mlpTriple 2 n).prod (sampMeas k n)).real (failNet (paperDesign n fT wT hf hw) t a k) ≤
      δPapL + vPapL / hW ^ 2 + δextra + Bplus n a (hA + ds) hW (140 / 100) cf τp +
        Bminus n a (hA + ds) hW (140 / 100) cf τm + 2 * exp (-k * ds ^ 2) :=
  classifier_networks_free (by omega) (paperDesign n fT wT hf hw) t k (by norm_num) hcf hhW hhA
    hds ha hτp hτm hside1 hside2 hEp hEm
    (events_paper_L hn (paperDesign n fT wT hf hw) rfl (fun _ => rfl) hE₁ hextra)
    (frame_w_paper_L hn (paperCentres n) rfl (fun _ hc => hc.1.1)) hFA hRA

/-- Decrease in the dimension of the two endpoint tails, from every base dimension `n₀`
(Lemma `t7:p03:decrease`; Part 156 has the base `16 384`). -/
lemma Bplus_anti_gen {n n₀ a h hW cW cf τ : ℝ} (hn : n₀ ≤ n)
    (hE : Eplus a h hW cW cf τ ≤ 0) : Bplus n a h hW cW cf τ ≤ Bplus n₀ a h hW cW cf τ := by
  unfold Bplus
  exact exp_le_exp.2 (by nlinarith)

lemma Bminus_anti_gen {n n₀ a h hW cW cf τ : ℝ} (hn : n₀ ≤ n)
    (hE : Eminus a h hW cW cf τ ≤ 0) : Bminus n a h hW cW cf τ ≤ Bminus n₀ a h hW cW cf τ := by
  unfold Bminus
  exact exp_le_exp.2 (by nlinarith)

/-- **The same with the tails at a base dimension `n₀`**: for every `n ≥ n₀ ≥ 13 225` the failure
probability is at most `δPapL + vPapL/h_W² + δ_extra + B_+(n₀) + B_−(n₀) + 2·exp(−k·d_s²)`. A
numeric ledger at one dimension `n₀` then gives every larger dimension. -/
theorem classifier_paper_agent_free_base {n₀ : ℕ} (hn₀ : 13225 ≤ n₀) (hn : n₀ ≤ n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) (k : ℕ) {E₁ : Set (Ret n)}
    (hE₁ : MeasurableSet E₁) {δextra cf hW hA ds a τp τm : ℝ}
    (hcf : 0 < cf) (hhW : 0 < hW) (hhA : 0 ≤ hA) (hds : 0 < ds) (ha : 1 < a)
    (hτp : 0 < τp) (hτm : τm < 0)
    (hside1 : (hA + ds) + hW < √(1 / 100 / a)) (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW (140 / 100) cf τp ≤ 0)
    (hEm : Eminus a (hA + ds) hW (140 / 100) cf τm ≤ 0)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextra)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cf / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hW))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hA
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hW)) :
    ((mlpTriple 2 n).prod (sampMeas k n)).real (failNet (paperDesign n fT wT hf hw) t a k) ≤
      δPapL + vPapL / hW ^ 2 + δextra + Bplus n₀ a (hA + ds) hW (140 / 100) cf τp +
        Bminus n₀ a (hA + ds) hW (140 / 100) cf τm + 2 * exp (-k * ds ^ 2) := by
  have h := classifier_paper_agent_free_L (by omega : 13225 ≤ n) fT wT hf hw t k hE₁ hcf hhW hhA
    hds ha hτp hτm hside1 hside2 hEp hEm hextra hFA hRA
  have hn' : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 := Bplus_anti_gen hn' hEp
  have h2 := Bminus_anti_gen hn' hEm
  linarith

end BstLean.Part159

open BstLean.Part159 in
#print axioms pap_charge_L
open BstLean.Part159 in
#print axioms pap_frame_L
open BstLean.Part159 in
#print axioms pap_moment_L
open BstLean.Part159 in
#print axioms theta_window_paper_L
open BstLean.Part159 in
#print axioms world_window_up
open BstLean.Part159 in
#print axioms paper_world_L
open BstLean.Part159 in
#print axioms classifier_paper_agent_free_L
open BstLean.Part159 in
#print axioms classifier_paper_agent_free_base
