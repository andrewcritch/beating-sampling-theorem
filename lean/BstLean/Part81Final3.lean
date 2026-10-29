import BstLean.Part81Asm
import BstLean.Part81K3
import BstLean.Part81F3
import BstLean.Part81Cost

/-!
# Part 81: Theorem 4 at `(d_M, d_f) = (3,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`,
every `n ≥ 8000`

Role: `delegations/statements/p81-spec.md`.
* `featOp_mono`, `sphC_mono`: the interface constants can be increased.
* `part81_mb3`, `part81_varBoundW3`: the mean bounds and the conditional variance bound at `d = 3`
  with numeric constants (`n ≥ 8000`): floor `1.6665‖a‖² + 5.555‖H‖²`, `c_V ≤ 18.06`.
* `fail81_32`, `part81_32`: the coefficient-sphere theorem.
-/

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59
open BstLean.Part78 (nsq frobH trH)

lemma featOp_mono {n d : ℕ} {CF CF' : ℝ} (h : CF ≤ CF') (hF : FeatOp n d CF) : FeatOp n d CF' := by
  intro c
  refine (hF c).trans ?_
  have h0 : 0 ≤ ∑ q, c q ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h hn0) h0

lemma sphC_mono {n d : ℕ} {M1 S2 B1 VK sM S2' VK' : ℝ} (hS2 : S2 ≤ S2') (hVK : VK ≤ VK')
    (hS : SphC n d M1 S2 B1 VK sM) : SphC n d M1 S2' B1 VK' sM := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hS
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact ⟨a1, a2, a3, a4, a5, a6.trans (div_le_div_of_nonneg_right hS2 hn0), a7,
    a8.trans (div_le_div_of_nonneg_right hVK hn0), a9⟩

theorem part81_featOp3 (n : ℕ) (hn : 8000 ≤ n) : FeatOp n 3 (10004 / 10000) := by
  refine featOp_mono ?_ (featOp3 n (by omega))
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have : 3 / ((n : ℝ) + 2) ≤ 4 / 10000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  linarith

theorem part81_sphC3 (n : ℕ) (hn : 8000 ≤ n) : SphC n 3 1 (1668 / 1000) 3 (1 / 300) 3 := by
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine sphC_mono ?_ ?_ (sphC3 n (by omega) (kerGen n 3 (by omega)) (10004 / 10000) (by norm_num)
    (part81_featOp3 n hn))
  · have : 3 / (n : ℝ) ≤ 3 / 8000 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem part81_mb3 (n : ℕ) (hn : 8000 ≤ n) :
    MB n 3 (16665 / 10000) (5555 / 1000) 1 (2 * (1668 / 1000) + 3 ^ 2) (eD 3 + 3 / (n : ℝ))
      (1 / 300 + 2 * ((eD 3 + 3 / (n : ℝ)) ^ 2 + 1 / 300 / (n : ℝ))) := by
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : 1 / (n : ℝ) ≤ 1 / 8000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have h2 : 1668 / 1000 / (n : ℝ) = 1668 / 1000 * (1 / n) := by ring
  refine mb_of n 3 (by omega) (by rw [eD_three]; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (part81_sphC3 n hn)
    (meanIds n 3 (by omega) BstLean.Part78.wickTwoPoint) ?_ ?_
  · rw [eD_three]; linarith
  · rw [eD_three, h2]; nlinarith

theorem part81_varBoundW3 (n : ℕ) (hn : 8000 ≤ n) :
    VarBoundW n 3 (16665 / 10000) (5555 / 1000)
      (1 / 2 * (4 * (10004 / 10000) * (1733 / 1000) * (4184 / 1000) *
        (12002 / 10000 + 15 / 10000)) + 1 / 2 * (4 * (10004 / 10000) * (311 / 1000))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have e3 : (3 : ℝ) / n = 3 * (1 / n) := by ring
  have e1 : (1668 / 1000 : ℝ) / n = 1668 / 1000 * (1 / n) := by ring
  have e2 : (1 / 300 : ℝ) / n = 1 / 300 * (1 / n) := by ring
  have hF := part81_featOp3 n hn
  refine varBoundW_of n 3 hn1 (η := 1 / 58) (by rw [eD_three]; norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (part81_sphC3 n hn) (part81_mb3 n hn)
    (wQId n 3 hn1 BstLean.Part78.wickTwoPoint)
    (varBoundK n 3 hn1 (10004 / 10000) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin)
    (varBoundK2 n 3 hn1 (10004 / 10000) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv2 hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin
      BstLean.Part78.wickTwoPoint)
    (by norm_num) (by rw [eD_three]; norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ (by norm_num)
  · rw [eD_three, e3, e1]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 8000)]
  · rw [e3]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 8000)]
  · rw [eD_three, e3, e2]
    set x := 1 / (n : ℝ)
    nlinarith [mul_nonneg hx0.le hx0.le, mul_le_mul hx hx hx0.le (by norm_num : (0:ℝ) ≤ 1 / 8000)]

/-- Failure `≤ 1/100` at `ε = 1/2`, map degree 3, for every `n ≥ 8000`. -/
theorem fail81_32 (n : ℕ) (hn : 8000 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 3 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have e3 : (3 : ℝ) / n = 3 * (1 / n) := by ring
  have e2 : (1 / 300 : ℝ) / n = 1 / 300 * (1 / n) := by ring
  have hUA0 : 0 ≤ eD 3 + 3 / (n : ℝ) := by rw [eD_three]; positivity
  have hUv0 : 0 ≤ 1 / 300 + 2 * ((eD 3 + 3 / (n : ℝ)) ^ 2 + 1 / 300 / (n : ℝ)) := by positivity
  refine (fail81_asm n 3 (by omega) (by norm_num) (c1 := 2221 / 1000) (κ := 33 / 100)
    (ε := 1 / 2) (ε₁ := 2558 / 10000) (lam := 3 / 100) (t := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hUA0 hUv0
    (part81_mb3 n hn) (part81_varBoundW3 n hn) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [eD_three]
    have : (22 + 22 * (409 / 100) * (5 / 3 : ℝ) ^ 2 + (1 / 2) ^ 2 * 10 / (3 / 100)) *
        (1 / (n : ℝ)) / (5555 / 1000) ≤ 8 / 1000 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  · rw [eD_three, e3, e2]
    set x := 1 / (n : ℝ)
    have hxx : x * x ≤ 1 / 8000 * (1 / 8000) := mul_le_mul hx hx hx0.le (by norm_num)
    have hU : (4 * (5 / 3 + 3 * x) + (1 / 300 + 2 * ((5 / 3 + 3 * x) ^ 2 + 1 / 300 * x))) / 10 ≤
        1224 / 1000 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [mul_nonneg hx0.le hx0.le]
    have hS : 4 + 2221 / 1000 / (2558 / 10000 : ℝ) ^ 2 +
        (1 / 2 * (4 * (10004 / 10000) * (1733 / 1000) * (4184 / 1000) *
          (12002 / 10000 + 15 / 10000)) + 1 / 2 * (4 * (10004 / 10000) * (311 / 1000))) /
          (1 - 33 / 100 : ℝ) ^ 2 +
        (4 * (5 / 3 + 3 * x) + (1 / 300 + 2 * ((5 / 3 + 3 * x) ^ 2 + 1 / 300 * x))) / 10 +
        (4 * 1 + (2 * (1668 / 1000) + 3 ^ 2)) * x ≤ 795 / 10 := by
      have h1 : (2221 / 1000 : ℝ) / (2558 / 10000) ^ 2 ≤ 3395 / 100 := by norm_num
      have h2 : (1 / 2 * (4 * (10004 / 10000) * (1733 / 1000) * (4184 / 1000) *
          (12002 / 10000 + 15 / 10000)) + 1 / 2 * (4 * (10004 / 10000) * (311 / 1000)) : ℝ) /
          (1 - 33 / 100) ^ 2 ≤ 4023 / 100 := by norm_num
      nlinarith
    have hS0 : (0 : ℝ) ≤ 795 / 10 := by norm_num
    calc _ ≤ 795 / 10 * x := mul_le_mul_of_nonneg_right hS hx0.le
      _ ≤ 795 / 10 * (1 / 8000) := mul_le_mul_of_nonneg_left hx hS0
      _ ≤ 1 / 100 := by norm_num

/-- **Theorem 4 at `(d_M, d_f) = (3,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 8000`.** The statement of `Part78.part78_22_6600` with the map degree 3. -/
theorem part81_32_8000 :
    ∀ n : ℕ, 8000 ≤ n → ∃ pg : Prog (In59 n 3 2) Unit,
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
  exact fail81_32 n hn c hc

end BstLean.Part81

#print axioms BstLean.Part81.part81_32_8000
