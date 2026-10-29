import BstLean.Part81Asm2
import BstLean.Part81K1
import BstLean.Part81Final3

/-!
# Part 81: Theorem 4 at `(d_M, d_f) = (1,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`,
every `n ≥ 13000`

At `d_M = 1`, `𝒟 = n(n+1)`, and the radius step of Part 78 (level `1/n`, second moment) fails.
The replacement: the radius level `δ = 25/(4n)` with the eighth-moment tail `radTail8`
(probability `≤ 1700/(25/4)⁸ < 7.4·10⁻⁴`), and the weighted deterministic core (`μ = 7/10`).
-/

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59
open BstLean.Part78 (nsq frobH trH)

theorem part81_mb1 (n : ℕ) (hn : 13000 ≤ n) :
    MB n 1 1 (19998 / 10000) 0 (2 * 1 + 0 ^ 2) (eD 1 + 0 / (n : ℝ))
      (0 + 2 * ((eD 1 + 0 / (n : ℝ)) ^ 2 + 0 / (n : ℝ))) := by
  have hn' : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : 1 / (n : ℝ) ≤ 1 / 13000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  refine mb_of n 1 (by omega) (by rw [eD_one]; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sphC1 n (by omega))
    (meanIds n 1 (by omega) BstLean.Part78.wickTwoPoint) ?_ ?_
  · rw [eD_one]; simp
  · rw [eD_one]; nlinarith

theorem part81_varBoundW1 (n : ℕ) (hn : 13000 ≤ n) :
    VarBoundW n 1 1 (19998 / 10000)
      (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20003 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000))) := by
  have hn1 : 1 ≤ n := by omega
  have hF := featOp1 n hn1
  refine varBoundW_of n 1 hn1 (η := 1 / 1000) (by rw [eD_one]; norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (sphC1 n hn1) (part81_mb1 n hn)
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
/-- Failure `≤ 1/100` at `ε = 1/2`, map degree 1, for every `n ≥ 13000`. -/
theorem fail81_12 (n : ℕ) (hn : 13000 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 1) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 1 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (13000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 13000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hDD : DD n 1 = (n : ℝ) * ((n : ℝ) + 1) := DD_one n
  have hDn2 : (n : ℝ) ^ 2 ≤ DD n 1 := by rw [hDD]; nlinarith
  have hD4000 : 4000 ≤ DD n 1 := by nlinarith
  have hDpos : 0 < DD n 1 := by linarith
  have hδ0 : (0 : ℝ) < 25 / 4 * (1 / (n : ℝ)) := by positivity
  have hδ : (25 : ℝ) / 4 * (1 / (n : ℝ)) ≤ 1 / 100 := by nlinarith
  have hUA0 : 0 ≤ eD 1 + 0 / (n : ℝ) := by rw [eD_one]; simp
  have hUv0 : 0 ≤ 0 + 2 * ((eD 1 + 0 / (n : ℝ)) ^ 2 + 0 / (n : ℝ)) := by positivity
  have hRad0 : 0 ≤ 1700 / DD n 1 ^ 4 / (25 / 4 * (1 / (n : ℝ))) ^ 8 := by positivity
  have key := fail81_coreW n 1 hn1 (δ := 25 / 4 * (1 / (n : ℝ))) (TQ := 3 / 2 * n) (T2 := 1)
    (ε := 1 / 2) (μ := 7 / 10) (c1 := 10002 / 10000) (κ := 345 / 1000) (ε₁ := 1579 / 10000)
    (lam := 8 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hUA0 hUv0
    (part81_mb1 n hn) (part81_varBoundW1 n hn) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by norm_num) hδ0 hδ (by norm_num) hRad0 (radTail8 n 1 hn1 hD4000 _ hδ0)
    (by
      rw [eD_one]
      have e : (2 * (1 + 1 / (7 / 10 : ℝ)) * ((25 / 4 * (1 / (n : ℝ))) ^ 2 * 1 +
          409 / 100 * (1 : ℝ) ^ 2 * (25 / 4 * (1 / (n : ℝ))) ^ 2 * (n : ℝ)) +
          (1 / 2 : ℝ) ^ 2 * (25 / 4 * (1 / (n : ℝ))) ^ 2 * (3 / 2 * (n : ℝ)) / (8 / 100)) =
          (2 * (1 + 10 / 7) * (625 / 16 * (1 / (n : ℝ)) + 409 / 100 * (625 / 16)) +
            1 / 4 * (625 / 16) * (3 / 2) * (100 / 8)) * (1 / (n : ℝ)) := by
        field_simp; ring
      rw [e]
      have h2 : (2 * (1 + 10 / 7) * (625 / 16 * (1 / (n : ℝ)) + 409 / 100 * (625 / 16)) +
            1 / 4 * (625 / 16) * (3 / 2) * (100 / 8)) * (1 / (n : ℝ)) / (19998 / 10000) ≤
          369 / 10000 := by
        rw [div_le_iff₀ (by norm_num)]
        have h3 : (2 * (1 + 10 / 7) * (625 / 16 * (1 / (n : ℝ)) + 409 / 100 * (625 / 16)) +
            1 / 4 * (625 / 16) * (3 / 2) * (100 / 8)) ≤ 9593 / 10 := by nlinarith
        calc _ ≤ 9593 / 10 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right h3 hx0.le
          _ ≤ 9593 / 10 * (1 / 13000) := mul_le_mul_of_nonneg_left hx (by norm_num)
          _ ≤ _ := by norm_num
      nlinarith) c hc
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have t1 : 1700 / DD n 1 ^ 4 / (25 / 4 * (1 / (n : ℝ))) ^ 8 ≤ 74 / 100000 := by
    have e : 1700 / DD n 1 ^ 4 / (25 / 4 * (1 / (n : ℝ))) ^ 8 =
        1700 / (25 / 4 : ℝ) ^ 8 * ((n : ℝ) ^ 8 / DD n 1 ^ 4) := by
      field_simp
    have hD4 : ((n : ℝ) ^ 2) ^ 4 ≤ DD n 1 ^ 4 := pow_le_pow_left₀ (by positivity) hDn2 4
    have h8 : (n : ℝ) ^ 8 / DD n 1 ^ 4 ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc (n : ℝ) ^ 8 = ((n : ℝ) ^ 2) ^ 4 := by ring
        _ ≤ _ := hD4
    rw [e]
    calc 1700 / (25 / 4 : ℝ) ^ 8 * ((n : ℝ) ^ 8 / DD n 1 ^ 4) ≤ 1700 / (25 / 4 : ℝ) ^ 8 * 1 :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
      _ ≤ 74 / 100000 := by norm_num
  have t2 : (10002 / 10000 : ℝ) / (n * (1579 / 10000) ^ 2) ≤ 4012 / 100 * (1 / n) := by
    have : (10002 / 10000 : ℝ) / (n * (1579 / 10000) ^ 2) =
        10002 / 10000 / (1579 / 10000) ^ 2 * (1 / n) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by norm_num) hx0.le
  have t3 : (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20003 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000)) : ℝ) / (n * (1 - 345 / 1000) ^ 2) ≤
      6996 / 100 * (1 / n) := by
    have : (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20003 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000)) : ℝ) / (n * (1 - 345 / 1000) ^ 2) =
        (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (20003 / 10000 + 0)) +
        1 / 2 * (4 * 1 * (5006 / 10000))) / (1 - 345 / 1000) ^ 2 * (1 / n) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by norm_num) hx0.le
  have t4 : (4 * (eD 1 + 0 / (n : ℝ)) + (0 + 2 * ((eD 1 + 0 / (n : ℝ)) ^ 2 + 0 / (n : ℝ)))) /
      (3 / 2 * (n : ℝ)) = 4 * (1 / n) := by
    rw [eD_one]; field_simp; ring
  have t5 : (4 * 0 + (2 * 1 + 0 ^ 2) : ℝ) / (n * 1) = 2 * (1 / n) := by field_simp; norm_num
  rw [t4, t5]
  nlinarith

/-- **Theorem 4 at `(d_M, d_f) = (1,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 13000`.** -/
theorem part81_12_13000 :
    ∀ n : ℕ, 13000 ≤ n → ∃ pg : Prog (In59 n 1 2) Unit,
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
  exact fail81_12 n hn c hc

end BstLean.Part81

#print axioms BstLean.Part81.part81_12_13000
