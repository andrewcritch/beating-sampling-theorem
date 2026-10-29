import BstLean.Part81Asm2
import BstLean.Part81UY
import BstLean.Part81Cost
import BstLean.Part81Final3
import BstLean.Part81K2

/-!
# Part 81: Theorem 4 at `(d_M, d_f) = (2,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`,
every `n ≥ 5400`

This file is generated from a template (the constants are computed by a script with exact rational
arithmetic; Lean checks every inequality). The transfer uses the eighth-moment radius tail and the
weighted deterministic core (`fail81_asm2`, `k = 5`, `μ = 3 / 100`).
Floor `7499 / 5000‖a‖² + 11249 / 2500‖H‖²`; `c₁ = 1891 / 2000`; `c_V` is the constant of `part81_varBoundW2`
(about `20.02`); `κ = 9 / 40`, `ε₁ = 2271 / 10000`, `λ = 1 / 50`, `t = 40`.
-/

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59
open BstLean.Part78 (nsq frobH trH)

theorem part81_featOp2 (n : ℕ) (hn : 5400 ≤ n) : FeatOp n 2 (1) := by
  have hn' : (5400 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  exact featOp2 n (by omega)

theorem part81_sphC2 (n : ℕ) (hn : 5400 ≤ n) :
    SphC n 2 1 (501 / 500) (3 / 2) (1 / 1440) (2) := by
  have hn' : (5400 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine sphC_mono le_rfl ?_ (sphC2 n (by omega))
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem part81_mb2 (n : ℕ) (hn : 5400 ≤ n) :
    MB n 2 (7499 / 5000) (11249 / 2500) 1 (2 * (501 / 500) + (3 / 2) ^ 2) (eD 2 + (3 / 2) / (n : ℝ)) (1 / 1440 + 2 * ((eD 2 + (3 / 2) / (n : ℝ)) ^ 2 + (1 / 1440) / (n : ℝ))) := by
  have hn' : (5400 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : 1 / (n : ℝ) ≤ 1 / 5400 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have h2 : (501 / 500 : ℝ) / (n : ℝ) = 501 / 500 * (1 / n) := by ring
  refine mb_of n 2 (by omega) (by rw [eD_two]; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (part81_sphC2 n hn)
    (meanIds n 2 (by omega) BstLean.Part78.wickTwoPoint) ?_ ?_
  · rw [eD_two]; linarith
  · rw [eD_two, h2]; nlinarith

theorem part81_varBoundW2 (n : ℕ) (hn : 5400 ≤ n) :
    VarBoundW n 2 (7499 / 5000) (11249 / 2500)
      (1 / 2 * (4 * (1) * (1733 / 1000) * (4184 / 1000) * (2667 / 2000 + 51 / 100000)) + 1 / 2 * (4 * (1) * (679 / 2000))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (5400 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 5400 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have e3 : (3 / 2 : ℝ) / n = 3 / 2 * (1 / n) := by ring
  have e1 : (501 / 500 : ℝ) / n = 501 / 500 * (1 / n) := by ring
  have e2 : (1 / 1440 : ℝ) / n = 1 / 1440 * (1 / n) := by ring
  have hF := part81_featOp2 n hn
  refine varBoundW_of n 2 hn1 (η := 9 / 1000) (by rw [eD_two]; norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (part81_sphC2 n hn) (part81_mb2 n hn)
    (wQId n 2 hn1 BstLean.Part78.wickTwoPoint)
    (varBoundK n 2 hn1 (1) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin)
    (varBoundK2 n 2 hn1 (1) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv2 hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin
      BstLean.Part78.wickTwoPoint)
    (by norm_num) (by rw [eD_two]; norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ (by norm_num)
  · rw [eD_two, e3, e1]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 5400)]
  · rw [e3]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 5400)]
  · rw [eD_two, e3, e2]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 5400)]

/-- Failure `≤ 1/100` at `ε = 1/2`, map degree 2, for every `n ≥ 5400`. -/
theorem part81_22_fail (n : ℕ) (hn : 5400 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn' : (5400 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 5400 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have e3 : (3 / 2 : ℝ) / n = 3 / 2 * (1 / n) := by ring
  have e2 : (1 / 1440 : ℝ) / n = 1 / 1440 * (1 / n) := by ring
  have hUA0 : 0 ≤ (eD 2 + (3 / 2) / (n : ℝ)) := by rw [eD_two]; positivity
  have hUv0 : 0 ≤ (1 / 1440 + 2 * ((eD 2 + (3 / 2) / (n : ℝ)) ^ 2 + (1 / 1440) / (n : ℝ))) := by positivity
  refine (fail81_asm2 n 2 (by omega) (by norm_num) (c1 := 1891 / 2000) (κ := 9 / 40)
    (ε := 1 / 2) (ε₁ := 2271 / 10000) (lam := 1 / 50) (t := 40) (μ := 3 / 100) (k := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hUA0 hUv0
    (part81_mb2 n hn) (part81_varBoundW2 n hn) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [eD_two]
    have e : (1 : ℝ) / ((5) ^ 2 * (n : ℝ)) = 1 / (5) ^ 2 * (1 / n) := by
      field_simp
    rw [e]
    have : (2 * (1 + 1 / (3 / 100 : ℝ)) * (1 + 409 / 100 * (3 / 2 : ℝ) ^ 2) +
        (1 / 2) ^ 2 * (40) / (1 / 50)) * (1 / (5) ^ 2 * (1 / (n : ℝ))) / (11249 / 2500) ≤
        99 / 50000 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  · rw [eD_two, e3, e2]
    set x := 1 / (n : ℝ)
    have hxx : x * x ≤ 1 / 5400 * (1 / 5400) := mul_le_mul hx hx hx0.le (by norm_num)
    have hx3 : x ^ 3 ≤ (1 / 5400) ^ 3 := pow_le_pow_left₀ hx0.le hx 3
    have hU : (4 * (3 / 2 + (3 / 2) * x) + (1 / 1440 + 2 * ((3 / 2 + (3 / 2) * x) ^ 2 + (1 / 1440) * x))) / (40) ≤ 1313 / 5000 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [mul_nonneg hx0.le hx0.le]
    have hS : 27200 * (5 : ℝ) ^ 8 * x ^ 3 + 1891 / 2000 / (2271 / 10000 : ℝ) ^ 2 +
        (1 / 2 * (4 * (1) * (1733 / 1000) * (4184 / 1000) * (2667 / 2000 + 51 / 100000)) + 1 / 2 * (4 * (1) * (679 / 2000))) / (1 - 9 / 40 : ℝ) ^ 2 +
        (4 * (3 / 2 + (3 / 2) * x) + (1 / 1440 + 2 * ((3 / 2 + (3 / 2) * x) ^ 2 + (1 / 1440) * x))) / (40) +
        (4 * 1 + (2 * (501 / 500) + (3 / 2) ^ 2)) * x ≤ 521 / 10 := by
      have h1 : (1891 / 2000 : ℝ) / (2271 / 10000) ^ 2 ≤ 917 / 50 := by norm_num
      have h2 : ((1 / 2 * (4 * (1) * (1733 / 1000) * (4184 / 1000) * (2667 / 2000 + 51 / 100000)) + 1 / 2 * (4 * (1) * (679 / 2000))) : ℝ) / (1 - 9 / 40) ^ 2 ≤ 1667 / 50 := by norm_num
      have h3 : 27200 * (5 : ℝ) ^ 8 * x ^ 3 ≤ 27200 * (5) ^ 8 * (1 / 5400) ^ 3 :=
        mul_le_mul_of_nonneg_left hx3 (by norm_num)
      norm_num at h3
      nlinarith
    have hS0 : (0 : ℝ) ≤ 521 / 10 := by norm_num
    calc _ ≤ 521 / 10 * x := mul_le_mul_of_nonneg_right hS hx0.le
      _ ≤ 521 / 10 * (1 / 5400) := mul_le_mul_of_nonneg_left hx hS0
      _ ≤ 1 / 100 := by norm_num

/-- **Theorem 4 at `(d_M, d_f) = (2,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 5400`.** -/
theorem part81_22 :
    ∀ n : ℕ, 5400 ≤ n → ∃ pg : Prog (In59 n 2 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 2 2 → ℝ, pg.eval v () = g0Q n 2 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 2 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro n hn
  obtain ⟨pg, h0, hread, hspec, hcost, heval⟩ := prog81_unif n 2 (by norm_num) (by omega) (1 / 2)
  refine ⟨pg, h0, hread, hspec, hcost, ?_⟩
  intro c hc
  simp only [heval]
  exact part81_22_fail n hn c hc

end BstLean.Part81

#print axioms BstLean.Part81.part81_22
