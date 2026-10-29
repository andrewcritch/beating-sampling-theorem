import BstLean.Part159PaperF
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R159Hat
import BstLean.Part187R159Win
import BstLean.Part187R159Frame
import BstLean.Part187R159Paper

/-! Part 187 (file `Part187R159PaperF`): copy of `Part159PaperF` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part159.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le)
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN mW_ge_pow42 cHat2)
open BstLean.Part140
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- The Hellinger moment of the paper's centre at the floor `16250` (Part 159: `7.37·10⁻⁹`). -/
noncomputable def vPap : ℝ := 755 / 10 ^ 11

/-- **The numeric bound of the Hellinger moment for the centre of the paper** (`n ≥ 16 384`). -/
theorem vPert_pap_le (hn : 16250 ≤ n) :
    vPert n (εPap n) (ρPap n) (1994 / 1000) (2057 / 1000) (1001 / 1000) (1 / 20) ≤ vPap := by
  unfold vPert vPap
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
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
  have b1 : 1 / (127 * (n : ℝ) ^ 2) ≤ 1 / (127 * (16250 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) (by gcongr)
  have b2 : 1 / (127 * (n : ℝ) ^ 3) ≤ 1 / (127 * (16250 : ℝ) ^ 3) :=
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
        (1 / (127 * (16250 : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (a1.trans b1) (by norm_num)
  have c2 : (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
      (1 / (mW n : ℝ)) ≤
      (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
        (1 / (127 * (16250 : ℝ) ^ 3)) :=
    mul_le_mul_of_nonneg_left (a2.trans b2) (by norm_num)
  have c3 : (36509 / 1000 : ℝ) ^ 2 / ((1994 / 1000 - 1) ^ 2 * (538 / 100)) *
        (1 / (127 * (16250 : ℝ) ^ 2)) +
      (2 * ((31623 / 10000 : ℝ) ^ 2 + (6271 / 1000) ^ 2) / (1 / 20) ^ 2) *
        (1 / (127 * (16250 : ℝ) ^ 3)) ≤ 755 / 10 ^ 11 := by norm_num
  rw [e1] at hfirst
  rw [e2] at hsecond
  linarith

/-- **The Hellinger moment for the centre and the scalar of the paper.** For `n ≥ 16 384`, IF
`ConstC n` and `ConstK n`: there is a majorant `K` of `E_u H_u²` on `GPap n` with
`E[1_{GPap}·K] ≤ vPap = 7.55·10⁻⁹`. -/
theorem pap_moment (hn : 16250 ≤ n) (hC : ConstC n) (hK : ConstK n) :
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


/-- **`FRAME_W_hyp` for the World centre of the paper** (`1.377/n`; Lean has `1.36/n`), on every
set of retained data inside `HP n`, IF `ConstC n`. -/
theorem frame_w_paper (hn : 16250 ≤ n) (hC : ConstC n) (D : Centres n) (hD : D.bW = bWp)
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
`vPap = 7.55·10⁻⁹`. -/
theorem events_paper (hn : 16250 ≤ n) (hC : ConstC n) (hK : ConstK n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁) {δextra : ℝ}
    (h3 : (retDist D.toCentres).real (HP n ∩ E₁ᶜ) ≤ δextra) :
    EVENTS_hyp D.toCentres (HP n) E₁ (HbarW D) δPap vPap δextra := by
  obtain ⟨K, iK, hle, hint⟩ := pap_moment hn hC hK
  refine events_of_hid (by omega) D (measurableSet_GPap (by omega)) iK (fun c hc => ?_) hE₁
    (pap_charge hn) hint h3
  rw [HbarW2_eq_hellHid D c (hτ c), hD]
  exact hle c.1.1 hc

end BstLean.Part159.R

