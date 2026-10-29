import BstLean.Part81D1
import BstLean.Part81Rad
import BstLean.Part81Final1

/-!
# Part 81: Theorem 4 at `(d_M, d_f) = (1,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`,
every `n ≥ 8200`

This improves `Part81Final1` (`n ≥ 13000`). At `d_M = 1` the error on the coefficient sphere is
exactly `τ² R` with `R = E(W) − tr H (‖Z‖²/𝒟 − 1)` and `E R² ≤ 2‖H‖²/n` (`fail81_core1`): the radius
term cancels against the Gaussian-model error. Radius level `δ = 15/(2n)` with the eighth-moment
tail; `κ = 23/100`, `θ = 2011/50000`, `λ = 3/20`, `TQ = (3/2) n`.
-/

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59
open BstLean.Part78 (nsq frobH trH)

theorem part81_mb1b (n : ℕ) (hn : 8200 ≤ n) :
    MB n 1 1 (19997 / 10000) 0 (2 * 1 + 0 ^ 2) (eD 1 + 0 / (n : ℝ))
      (0 + 2 * ((eD 1 + 0 / (n : ℝ)) ^ 2 + 0 / (n : ℝ))) := by
  have hn' : (8200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : 1 / (n : ℝ) ≤ 1 / 8200 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  refine mb_of n 1 (by omega) (by rw [eD_one]; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sphC1 n (by omega))
    (meanIds n 1 (by omega) BstLean.Part78.wickTwoPoint) ?_ ?_
  · rw [eD_one]; simp
  · rw [eD_one]; nlinarith

theorem part81_varBoundW1b (n : ℕ) (hn : 8200 ≤ n) :
    VarBoundW n 1 1 (19997 / 10000)
      (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20004 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000))) := by
  have hn1 : 1 ≤ n := by omega
  have hF := featOp1 n hn1
  refine varBoundW_of n 1 hn1 (η := 1 / 1000) (by rw [eD_one]; norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sphC1 n hn1) (part81_mb1b n hn)
    (wQId n 1 hn1 BstLean.Part78.wickTwoPoint)
    (varBoundK n 1 hn1 1 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin)
    (varBoundK2 n 1 hn1 1 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv2 hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin
      BstLean.Part78.wickTwoPoint)
    (by norm_num) (by rw [eD_one]; norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_ (by norm_num)
  · rw [eD_one]; simp
  · simp
  · rw [eD_one]; simp; norm_num

set_option maxHeartbeats 800000 in
/-- Failure `≤ 1/100` at `ε = 1/2`, map degree 1, for every `n ≥ 8200`. -/
theorem fail81_12b (n : ℕ) (hn : 8200 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 1) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 1 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (8200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8200 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hDD : DD n 1 = (n : ℝ) * ((n : ℝ) + 1) := DD_one n
  have hDn2 : (n : ℝ) ^ 2 ≤ DD n 1 := by rw [hDD]; nlinarith
  have hD4000 : 4000 ≤ DD n 1 := by nlinarith
  have hDpos : 0 < DD n 1 := by linarith
  have hδ0 : (0 : ℝ) < 15 / 2 * (1 / (n : ℝ)) := by positivity
  have hδ : (15 : ℝ) / 2 * (1 / (n : ℝ)) ≤ 1 / 100 := by nlinarith
  have hUA0 : 0 ≤ eD 1 + 0 / (n : ℝ) := by rw [eD_one]; simp
  have hUv0 : 0 ≤ 0 + 2 * ((eD 1 + 0 / (n : ℝ)) ^ 2 + 0 / (n : ℝ)) := by positivity
  have hRad0 : 0 ≤ 1700 / DD n 1 ^ 4 / (15 / 2 * (1 / (n : ℝ))) ^ 8 := by positivity
  have key := fail81_core1 n hn1 (δ := 15 / 2 * (1 / (n : ℝ))) (TQ := 3 / 2 * n)
    (ε := 1 / 2) (κ := 23 / 100) (θ := 2011 / 50000) (lam := 3 / 20)
    (by norm_num) (by norm_num) (by norm_num) hUA0 hUv0
    (part81_mb1b n hn) (part81_varBoundW1b n hn) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) hδ0 hδ hRad0
    (radTail8 n 1 hn1 hD4000 _ hδ0)
    (by
      have e : (1 / 2 : ℝ) ^ 2 * (15 / 2 * (1 / (n : ℝ))) ^ 2 * (3 / 2 * (n : ℝ)) /
          (3 / 20 * (19997 / 10000)) =
          (1 / 4 * (225 / 4) * (3 / 2) / (3 / 20 * (19997 / 10000))) * (1 / (n : ℝ)) := by
        field_simp; norm_num
      rw [e]
      have h2 : (1 / 4 * (225 / 4) * (3 / 2) / (3 / 20 * (19997 / 10000)) : ℝ) * (1 / (n : ℝ)) ≤
          429 / 50000 := by
        calc _ ≤ (1 / 4 * (225 / 4) * (3 / 2) / (3 / 20 * (19997 / 10000)) : ℝ) * (1 / 8200) :=
              mul_le_mul_of_nonneg_left hx (by norm_num)
          _ ≤ _ := by norm_num
      have h3 : (1 + 15 / 2 * (1 / (n : ℝ))) ^ 2 ≤ (1 + 15 / 2 * (1 / 8200)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h4 : (1 + 15 / 2 * (1 / (n : ℝ))) ^ 2 * (2011 / 50000) ≤
          (1 + 15 / 2 * (1 / 8200)) ^ 2 * (2011 / 50000) :=
        mul_le_mul_of_nonneg_right h3 (by norm_num)
      norm_num at h2 h4 ⊢
      linarith) c hc
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have t1 : 1700 / DD n 1 ^ 4 / (15 / 2 * (1 / (n : ℝ))) ^ 8 ≤ 17 / 100000 := by
    have e : 1700 / DD n 1 ^ 4 / (15 / 2 * (1 / (n : ℝ))) ^ 8 =
        1700 / (15 / 2 : ℝ) ^ 8 * ((n : ℝ) ^ 8 / DD n 1 ^ 4) := by
      field_simp
    have hD4 : ((n : ℝ) ^ 2) ^ 4 ≤ DD n 1 ^ 4 := pow_le_pow_left₀ (by positivity) hDn2 4
    have h8 : (n : ℝ) ^ 8 / DD n 1 ^ 4 ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc (n : ℝ) ^ 8 = ((n : ℝ) ^ 2) ^ 4 := by ring
        _ ≤ _ := hD4
    rw [e]
    calc 1700 / (15 / 2 : ℝ) ^ 8 * ((n : ℝ) ^ 8 / DD n 1 ^ 4) ≤ 1700 / (15 / 2 : ℝ) ^ 8 * 1 :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
      _ ≤ 17 / 100000 := by norm_num
  have t2 : (2 : ℝ) / (n * (19997 / 10000) * (2011 / 50000)) ≤ 2487 / 100 * (1 / n) := by
    have : (2 : ℝ) / (n * (19997 / 10000) * (2011 / 50000)) =
        2 / ((19997 / 10000) * (2011 / 50000)) * (1 / n) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by norm_num) hx0.le
  have t3 : (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20004 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000)) : ℝ) / (n * (1 - 23 / 100) ^ 2) ≤
      5062 / 100 * (1 / n) := by
    have : (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20004 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000)) : ℝ) / (n * (1 - 23 / 100) ^ 2) =
        (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20004 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000))) / (1 - 23 / 100) ^ 2 * (1 / n) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by norm_num) hx0.le
  have t4 : (4 * (eD 1 + 0 / (n : ℝ)) + (0 + 2 * ((eD 1 + 0 / (n : ℝ)) ^ 2 + 0 / (n : ℝ)))) /
      (3 / 2 * (n : ℝ)) = 4 * (1 / n) := by
    rw [eD_one]; field_simp; ring
  rw [t4]
  nlinarith

/-- **Theorem 4 at `(d_M, d_f) = (1,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 8200`.** -/
theorem part81_12 :
    ∀ n : ℕ, 8200 ≤ n → ∃ pg : Prog (In59 n 1 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 1 2 → ℝ, pg.eval v () = g0Q n 1 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 1 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n 1) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro n hn
  obtain ⟨pg, h0, hread, hspec, hcost, heval⟩ := prog81_unif n 1 (by norm_num) (by omega) (1 / 2)
  refine ⟨pg, h0, hread, hspec, hcost, ?_⟩
  intro c hc
  simp only [heval]
  exact fail81_12b n hn c hc

end BstLean.Part81

#print axioms BstLean.Part81.part81_12
