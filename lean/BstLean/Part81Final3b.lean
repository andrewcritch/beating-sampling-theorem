import BstLean.Part81Asm2
import BstLean.Part81UY
import BstLean.Part81Cost
import BstLean.Part81Final3
import BstLean.Part81K3
import BstLean.Part81F3

/-!
# Part 81: Theorem 4 at `(d_M, d_f) = (3,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`,
every `n ≥ 6700`

This file is generated from a template (the constants are computed by a script with exact rational
arithmetic; Lean checks every inequality). The transfer uses the eighth-moment radius tail and the
weighted deterministic core (`fail81_asm2`, `k = 5`, `μ = 1 / 50`).
Floor `3333 / 2000‖a‖² + 3472 / 625‖H‖²`; `c₁ = 20097 / 10000`; `c_V` is the constant of `part81_varBoundW3b`
(about `18.06`); `κ = 59 / 200`, `ε₁ = 263 / 1000`, `λ = 1 / 100`, `t = 40`.
-/

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59
open BstLean.Part78 (nsq frobH trH)

theorem part81_featOp3b (n : ℕ) (hn : 6700 ≤ n) : FeatOp n 3 (20009 / 20000) := by
  have hn' : (6700 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine featOp_mono ?_ (featOp3 n (by omega))
  have : 3 / ((n : ℝ) + 2) ≤ 9 / 20000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  linarith

theorem part81_sphC3b (n : ℕ) (hn : 6700 ≤ n) :
    SphC n 3 1 (541 / 500) (3) (4 / 1005) (3) := by
  have hn' : (6700 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine sphC_mono le_rfl ?_ (sphC_setS2 ((ss2U n 3 (by norm_num) (by omega)).trans (le_of_eq (by norm_num)))
    (sphC3 n (by omega) (kerGen n 3 (by omega)) (20009 / 20000) (by norm_num) (part81_featOp3b n hn)))
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem part81_mb3b (n : ℕ) (hn : 6700 ≤ n) :
    MB n 3 (3333 / 2000) (3472 / 625) 1 (2 * (541 / 500) + (3) ^ 2) (eD 3 + (3) / (n : ℝ)) (4 / 1005 + 2 * ((eD 3 + (3) / (n : ℝ)) ^ 2 + (4 / 1005) / (n : ℝ))) := by
  have hn' : (6700 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : 1 / (n : ℝ) ≤ 1 / 6700 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have h2 : (541 / 500 : ℝ) / (n : ℝ) = 541 / 500 * (1 / n) := by ring
  refine mb_of n 3 (by omega) (by rw [eD_three]; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (part81_sphC3b n hn)
    (meanIds n 3 (by omega) BstLean.Part78.wickTwoPoint) ?_ ?_
  · rw [eD_three]; linarith
  · rw [eD_three, h2]; nlinarith

theorem part81_varBoundW3b (n : ℕ) (hn : 6700 ≤ n) :
    VarBoundW n 3 (3333 / 2000) (3472 / 625)
      (1 / 2 * (4 * (20009 / 20000) * (1733 / 1000) * (4184 / 1000) * (12001 / 10000 + 87 / 50000)) + 1 / 2 * (4 * (20009 / 20000) * (3117 / 10000))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (6700 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 6700 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have e3 : (3 : ℝ) / n = 3 * (1 / n) := by ring
  have e1 : (541 / 500 : ℝ) / n = 541 / 500 * (1 / n) := by ring
  have e2 : (4 / 1005 : ℝ) / n = 4 / 1005 * (1 / n) := by ring
  have hF := part81_featOp3b n hn
  refine varBoundW_of n 3 hn1 (η := 19 / 1000) (by rw [eD_three]; norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (part81_sphC3b n hn) (part81_mb3b n hn)
    (wQId n 3 hn1 BstLean.Part78.wickTwoPoint)
    (varBoundK n 3 hn1 (20009 / 20000) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin)
    (varBoundK2 n 3 hn1 (20009 / 20000) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv2 hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin
      BstLean.Part78.wickTwoPoint)
    (by norm_num) (by rw [eD_three]; norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ (by norm_num)
  · rw [eD_three, e3, e1]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 6700)]
  · rw [e3]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 6700)]
  · rw [eD_three, e3, e2]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 6700)]

/-- Failure `≤ 1/100` at `ε = 1/2`, map degree 3, for every `n ≥ 6700`. -/
theorem part81_32_fail (n : ℕ) (hn : 6700 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 3 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn' : (6700 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 6700 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have e3 : (3 : ℝ) / n = 3 * (1 / n) := by ring
  have e2 : (4 / 1005 : ℝ) / n = 4 / 1005 * (1 / n) := by ring
  have hUA0 : 0 ≤ (eD 3 + (3) / (n : ℝ)) := by rw [eD_three]; positivity
  have hUv0 : 0 ≤ (4 / 1005 + 2 * ((eD 3 + (3) / (n : ℝ)) ^ 2 + (4 / 1005) / (n : ℝ))) := by positivity
  refine (fail81_asm2 n 3 (by omega) (by norm_num) (c1 := 20097 / 10000) (κ := 59 / 200)
    (ε := 1 / 2) (ε₁ := 263 / 1000) (lam := 1 / 100) (t := 40) (μ := 1 / 50) (k := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hUA0 hUv0
    (part81_mb3b n hn) (part81_varBoundW3b n hn) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [eD_three]
    have e : (1 : ℝ) / ((5) ^ 2 * (n : ℝ)) = 1 / (5) ^ 2 * (1 / n) := by
      field_simp
    rw [e]
    have : (2 * (1 + 1 / (1 / 50 : ℝ)) * (1 + 409 / 100 * (5 / 3 : ℝ) ^ 2) +
        (1 / 2) ^ 2 * (40) / (1 / 100)) * (1 / (5) ^ 2 * (1 / (n : ℝ))) / (3472 / 625) ≤
        243 / 100000 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  · rw [eD_three, e3, e2]
    set x := 1 / (n : ℝ)
    have hxx : x * x ≤ 1 / 6700 * (1 / 6700) := mul_le_mul hx hx hx0.le (by norm_num)
    have hx3 : x ^ 3 ≤ (1 / 6700) ^ 3 := pow_le_pow_left₀ hx0.le hx 3
    have hU : (4 * (5 / 3 + (3) * x) + (4 / 1005 + 2 * ((5 / 3 + (3) * x) ^ 2 + (4 / 1005) * x))) / (40) ≤ 1529 / 5000 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [mul_nonneg hx0.le hx0.le]
    have hS : 27200 * (5 : ℝ) ^ 8 * x ^ 3 + 20097 / 10000 / (263 / 1000 : ℝ) ^ 2 +
        (1 / 2 * (4 * (20009 / 20000) * (1733 / 1000) * (4184 / 1000) * (12001 / 10000 + 87 / 50000)) + 1 / 2 * (4 * (20009 / 20000) * (3117 / 10000))) / (1 - 59 / 200 : ℝ) ^ 2 +
        (4 * (5 / 3 + (3) * x) + (4 / 1005 + 2 * ((5 / 3 + (3) * x) ^ 2 + (4 / 1005) * x))) / (40) +
        (4 * 1 + (2 * (541 / 500) + (3) ^ 2)) * x ≤ 329 / 5 := by
      have h1 : (20097 / 10000 : ℝ) / (263 / 1000) ^ 2 ≤ 1453 / 50 := by norm_num
      have h2 : ((1 / 2 * (4 * (20009 / 20000) * (1733 / 1000) * (4184 / 1000) * (12001 / 10000 + 87 / 50000)) + 1 / 2 * (4 * (20009 / 20000) * (3117 / 10000))) : ℝ) / (1 - 59 / 200) ^ 2 ≤ 1817 / 50 := by norm_num
      have h3 : 27200 * (5 : ℝ) ^ 8 * x ^ 3 ≤ 27200 * (5) ^ 8 * (1 / 6700) ^ 3 :=
        mul_le_mul_of_nonneg_left hx3 (by norm_num)
      norm_num at h3
      nlinarith
    have hS0 : (0 : ℝ) ≤ 329 / 5 := by norm_num
    calc _ ≤ 329 / 5 * x := mul_le_mul_of_nonneg_right hS hx0.le
      _ ≤ 329 / 5 * (1 / 6700) := mul_le_mul_of_nonneg_left hx hS0
      _ ≤ 1 / 100 := by norm_num

/-- **Theorem 4 at `(d_M, d_f) = (3,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 6700`.** -/
theorem part81_32 :
    ∀ n : ℕ, 6700 ≤ n → ∃ pg : Prog (In59 n 3 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 3 2 → ℝ, pg.eval v () = g0Q n 3 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 3 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro n hn
  obtain ⟨pg, h0, hread, hspec, hcost, heval⟩ := prog81_unif n 3 (by norm_num) (by omega) (1 / 2)
  refine ⟨pg, h0, hread, hspec, hcost, ?_⟩
  intro c hc
  simp only [heval]
  exact part81_32_fail n hn c hc

end BstLean.Part81

#print axioms BstLean.Part81.part81_32
