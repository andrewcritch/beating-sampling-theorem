import BstLean.Part151G1
import BstLean.Part151Num99

/-!
# Part 151 (file `G3`): the conditional level with the Gaussian step in moment form for the
`W` term

Role: `delegations/statements/p151-spec.md`, items 3 and 5 ("sharper constants"). This file
evaluates `theorem5_frameProgG` (`Part151G`) at `κ = 1/3`, `δ = 6/100`, `L_c = 12`, `u_F = 5`,
`ε_W = 22/100`, `θ = 35/100`, with the hypotheses `‖C_r‖_op ≤ 1.662·γ_A/n`, `n·Dv ≤ 4.193` of
`theorem5_cond_99`. The `W` term is divided by `3`, so the charge of the `A`-stage event may be
larger.

* `total_leG`: the sum of all charges except `Pr(X12ᶜ)` is at most `53/10000`, `n ≥ 16 384`.
* **`theorem5_cond_99G`**: level `99/100` for every `n ≥ 16 384`, `k ≥ 100n`, with
  `Pr(X12ᶜ) ≤ 47/10000` (`theorem5_cond_99`: `27/10000`).
* `total_leG2`, **`theorem5_cond_995G`**: level `995/1000` for every `n ≥ 32 768`, with
  `Pr(X12ᶜ) ≤ 22/10000`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (tauWA)
open BstLean.Part149 (thA tauOutOf)
open BstLean.Part150 (CMap gSampH bTW measurable_bTW fullProg150 fullVal)

variable {k n : ℕ}

lemma two_PhiBar_four {a : ℝ} (ha : 4 ≤ a) : 2 * PhiBar a ≤ 7 / 100000 := two_tail_four ha

/-- The sum of all charges except `Pr(X12ᶜ)` is at most `53/10000` (`n ≥ 16 384`,
`κ = 1/3`, `ε_W = 22/100`, `θ = 35/100`). -/
lemma total_leG (hn : 16384 ≤ n) {cV : ℝ} (hcV0 : 0 < cV) (hcV : cV ≤ 614 / 100) (p : ℝ) :
    1 / (n : ℝ) + 1 / 3 *
          (4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / n) +
        (p + Real.exp (-12) + 2 * Real.exp (-(5 : ℝ) ^ 2 / 2) + 3 * chF n (6 / 100) +
          3 * Real.exp (-12)) +
        2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - 22 / 100) * √(n * (35 / 100 * (222757 / 1000000)) / cV)) ≤
      p + 53 / 10000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have t1 : 1 / (n : ℝ) ≤ 1 / 16384 := one_div_le_one_div_of_le (by norm_num) hx
  have t2 : 4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / n ≤
      4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t3 : 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / n ≤
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t4 := exp_neg_twelve
  have t5 : Real.exp (-(5 : ℝ) ^ 2 / 2) ≤ Real.exp (-12) :=
    Real.exp_le_exp.mpr (by norm_num)
  have t6 := chF_le hn
  have t7 : 2 * PhiBar ((1 / 2 - 22 / 100) *
      √(n * (35 / 100 * (222757 / 1000000)) / cV)) ≤ 7 / 100000 := by
    refine two_PhiBar_four ?_
    have h1 : (100 / 7 : ℝ) ≤ √(n * (35 / 100 * (222757 / 1000000)) / cV) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hcV0]
      have : (100 / 7 : ℝ) ^ 2 * cV ≤ (100 / 7) ^ 2 * (614 / 100) :=
        mul_le_mul_of_nonneg_left hcV (by norm_num)
      nlinarith
    nlinarith
  have t8 : (1 : ℝ) / 16384 + 1 / 3 *
        (4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / 16384) +
      (62 / 10000000 + 2 * (62 / 10000000) + 3 * (152 / 10000000) + 3 * (62 / 10000000)) +
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / 16384 +
      7 / 100000 ≤ 53 / 10000 := by norm_num
  linarith

/-- The same for `n ≥ 32 768`: at most `28/10000`. -/
lemma total_leG2 (hn : 32768 ≤ n) {cV : ℝ} (hcV0 : 0 < cV) (hcV : cV ≤ 614 / 100) (p : ℝ) :
    1 / (n : ℝ) + 1 / 3 *
          (4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / n) +
        (p + Real.exp (-12) + 2 * Real.exp (-(5 : ℝ) ^ 2 / 2) + 3 * chF n (6 / 100) +
          3 * Real.exp (-12)) +
        2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - 22 / 100) * √(n * (35 / 100 * (222757 / 1000000)) / cV)) ≤
      p + 28 / 10000 := by
  have hx : (32768 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hn' : 16384 ≤ n := by omega
  have t1 : 1 / (n : ℝ) ≤ 1 / 32768 := one_div_le_one_div_of_le (by norm_num) hx
  have t2 : 4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / n ≤
      4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / 32768 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t3 : 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / n ≤
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / 32768 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t4 := exp_neg_twelve
  have t5 : Real.exp (-(5 : ℝ) ^ 2 / 2) ≤ Real.exp (-12) :=
    Real.exp_le_exp.mpr (by norm_num)
  have t6 := chF_le hn'
  have t7 : 2 * PhiBar ((1 / 2 - 22 / 100) *
      √(n * (35 / 100 * (222757 / 1000000)) / cV)) ≤ 7 / 100000 := by
    refine two_PhiBar_four ?_
    have h1 : (100 / 7 : ℝ) ≤ √(n * (35 / 100 * (222757 / 1000000)) / cV) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hcV0]
      have : (100 / 7 : ℝ) ^ 2 * cV ≤ (100 / 7) ^ 2 * (614 / 100) :=
        mul_le_mul_of_nonneg_left hcV (by norm_num)
      nlinarith
    nlinarith
  have t8 : (1 : ℝ) / 32768 + 1 / 3 *
        (4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / 32768) +
      (62 / 10000000 + 2 * (62 / 10000000) + 3 * (152 / 10000000) + 3 * (62 / 10000000)) +
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / 32768 +
      7 / 100000 ≤ 28 / 10000 := by norm_num
  linarith

/-- The common step: the bound of `theorem5_frameProgG` at the parameters of this file, for a
charge `p12` of the `A`-stage event. -/
lemma frameG_at (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ))
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK (bTW J) W A₁ A₂ (1662 / 1000 * (2 / (n : ℝ)) / n))
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ 4193 / 1000 / (n : ℝ)) :
    ∃ cV : ℝ, 0 < cV ∧ cV ≤ 614 / 100 ∧
    1 - (1 / (n : ℝ) + 1 / 3 *
          (4849 / 20000 / ((22 / 100 : ℝ) ^ 2 * (35 / 100 * (222757 / 1000000))) / n) +
        (p12 + Real.exp (-12) + 2 * Real.exp (-(5 : ℝ) ^ 2 / 2) + 3 * chF n (6 / 100) +
          3 * Real.exp (-12)) +
        2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 35 / 100) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - 22 / 100) * √(n * (35 / 100 * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real
        {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hMr0 : (0 : ℝ) < 1662 / 1000 * (2 / (n : ℝ)) / n := by positivity
  have h := theorem5_frameProgG (κ := 1 / 3) (fun a ha => two_PhiBar_le_third ha)
    (k := k) (n := n) (J := J) (by omega) (by omega) h12 hp12 hb he hτ
    hMr0 hCr hDv (δ := 6 / 100) (uF := 5) (Lc := 12) (by norm_num) (by norm_num) (by norm_num)
    (εW := 22 / 100) (θ := 35 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hv := vbar_num hn hk
  have hv0 := (vbar_pos' n k (δ := 6 / 100)
    (Dbar := (1 + deltaC n 12) * (4193 / 1000 / (n : ℝ))) (Ebar := 2 * (1 + deltaC n 12))
    (LF := LFc n 5) (Lc := 12) (by norm_num) hMr0).resolve_right hx0.ne'
  exact ⟨_, hv0, hv, h⟩

/-- **The level `99/100` with the Gaussian step for the `W` term**: for every `n ≥ 16 384`,
`k ≥ 100n`, every atom count `J`: under the hypotheses of `theorem5_cond_99` on the set `X12`,
with the charge `Pr(X12ᶜ) ≤ 47/10000` (in the place of `27/10000`), the straight-line program
`fullProg150 k n J` of Part 150 succeeds with probability at least `99/100`. -/
theorem theorem5_cond_99G (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ 47 / 10000)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ))
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK (bTW J) W A₁ A₂ (1662 / 1000 * (2 / (n : ℝ)) / n))
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ 4193 / 1000 / (n : ℝ)) :
    99 / 100 ≤ (jointP k n).real
      {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  obtain ⟨cV, hv0, hv, h⟩ := frameG_at hn hk h12 hp12 hb he hτ hCr hDv
  refine le_trans ?_ h
  have ht := total_leG hn hv0 hv (47 / 10000)
  linarith

/-- **The level `995/1000`**: for every `n ≥ 32 768`, `k ≥ 100n`, under the same hypotheses
with the charge `Pr(X12ᶜ) ≤ 22/10000`. -/
theorem theorem5_cond_995G (hn : 32768 ≤ n) (hk : 100 * n ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ 22 / 10000)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ))
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK (bTW J) W A₁ A₂ (1662 / 1000 * (2 / (n : ℝ)) / n))
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ 4193 / 1000 / (n : ℝ)) :
    995 / 1000 ≤ (jointP k n).real
      {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  obtain ⟨cV, hv0, hv, h⟩ := frameG_at (by omega) hk h12 hp12 hb he hτ hCr hDv
  refine le_trans ?_ h
  have ht := total_leG2 hn hv0 hv (22 / 10000)
  linarith

end BstLean.Part151
