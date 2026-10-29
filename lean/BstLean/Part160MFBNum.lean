import BstLean.Part160MFB4

/-!
# Part 160 (file `MFBNum`): numeric instances of the centre charge with change (B)

Do not use `sorry`, `native_decide` or `axiom`. The certificates are generated; each side
condition is closed by `norm_num`.

* `centre16_B`, `centre26k_B`: changes (A), (B), (C); the whole window.
* `centre16_BD`, `centre26k_BD`: changes (A), (B), (C), (D); the whole window.
* `centre22k_46`, …, `centre22k_54`: changes (A), (B), (C), (D) on the nine pieces of width
  `0.01`, `n ≥ 22000`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part154
open BstLean.Part153 (hid2Mean_cr)

/-- Changes (A), (B), (C): `t_A·|μ − b|² ≤ 0.1465·γ_A/n` for `n ≥ 16384`,
`0.46 ≤ θ_in ≤ 0.55` (`J ≥ 0.53588`, `√M₁ ≤ 0.73425`, `(4c_H)^(1/4) ≤ 1.21399`,
`√ξ ≤ 0.25574 + 0.10885 + 0.01063 + 0.0075`). -/
theorem centre16_B {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1465 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_B_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h
    (n1 := 16384) (θlo := (23 / 50)) (θhi := (11 / 20)) (u := (3383 / 125000)) (Jlo := (13397 / 25000))
    (sm := (2937 / 4000)) (y := (121399 / 100000)) (s := (3391 / 5000)) (k := (1448 / 1)) (d := (499 / 50000)) (r := (37081 / 50000))
    (sx := (12787 / 50000)) (dv := (2177 / 20000)) (sqn := (128 / 1)) (q := (80939 / 100000)) (xr := (1063 / 100000))
    (X := (1196 / 3125))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C): `t_A·|μ − b|² ≤ 0.1272·γ_A/n` for `n ≥ 26000`,
`0.46 ≤ θ_in ≤ 0.55` (`J ≥ 0.53812`, `√M₁ ≤ 0.73312`, `(4c_H)^(1/4) ≤ 1.21306`,
`√ξ ≤ 0.25422 + 0.08641 + 0.00844 + 0.0075`). -/
theorem centre26k_B {n : ℕ} (hn : 26000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1272 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_B_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h
    (n1 := 26000) (θlo := (23 / 50)) (θhi := (11 / 20)) (u := (5371 / 250000)) (Jlo := (13453 / 25000))
    (sm := (2291 / 3125)) (y := (60653 / 50000)) (s := (3391 / 5000)) (k := (2047 / 1)) (d := (353 / 50000)) (r := (37081 / 50000))
    (sx := (12711 / 50000)) (dv := (8641 / 100000)) (sqn := (806 / 5)) (q := (80939 / 100000)) (xr := (211 / 25000))
    (X := (35657 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D): `t_A·|μ − b|² ≤ 0.1022·γ_A/n` for `n ≥ 16384`,
`0.46 ≤ θ_in ≤ 0.55` (`J ≥ 0.53588`, `√M₁ ≤ 0.73425`, `(4c_H)^(1/4) ≤ 1.21399`,
`√ξ ≤ 0.25574 + 0.04571 + 0.01063 + 0.0075`). -/
theorem centre16_BD {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1022 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16384) (θlo := (23 / 50)) (θhi := (11 / 20)) (u := (3383 / 125000)) (Jlo := (13397 / 25000))
    (sm := (2937 / 4000)) (y := (121399 / 100000)) (s := (3391 / 5000)) (k := (1448 / 1)) (d := (499 / 50000)) (r := (37081 / 50000))
    (sx := (12787 / 50000)) (dv := (4571 / 100000)) (sqn := (128 / 1)) (q := (80939 / 100000)) (xr := (1063 / 100000))
    (X := (15979 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D): `t_A·|μ − b|² ≤ 0.094·γ_A/n` for `n ≥ 26000`,
`0.46 ≤ θ_in ≤ 0.55` (`J ≥ 0.53812`, `√M₁ ≤ 0.73312`, `(4c_H)^(1/4) ≤ 1.21306`,
`√ξ ≤ 0.25422 + 0.03629 + 0.00844 + 0.0075`). -/
theorem centre26k_BD {n : ℕ} (hn : 26000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      940 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 26000) (θlo := (23 / 50)) (θhi := (11 / 20)) (u := (5371 / 250000)) (Jlo := (13453 / 25000))
    (sm := (2291 / 3125)) (y := (60653 / 50000)) (s := (3391 / 5000)) (k := (2047 / 1)) (d := (353 / 50000)) (r := (37081 / 50000))
    (sx := (12711 / 50000)) (dv := (3629 / 100000)) (sqn := (806 / 5)) (q := (80939 / 100000)) (xr := (211 / 25000))
    (X := (6129 / 20000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0803·γ_A/n` for `n ≥ 22000`,
`0.46 ≤ θ_in ≤ 0.47` (`J ≥ 0.53738`, `√M₁ ≤ 0.7335`, `(4c_H)^(1/4) ≤ 1.21337`,
`√ξ ≤ 0.22809 + 0.03945 + 0.00822 + 0.0075`). -/
theorem centre22k_46 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 47 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      803 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (23 / 50)) (θhi := (47 / 100)) (u := (4671 / 200000)) (Jlo := (26869 / 50000))
    (sm := (1467 / 2000)) (y := (121337 / 100000)) (s := (3391 / 5000)) (k := (1806 / 1)) (d := (4001 / 500000)) (r := (68557 / 100000))
    (sx := (22809 / 100000)) (dv := (789 / 20000)) (sqn := (1483 / 10)) (q := (74821 / 100000)) (xr := (411 / 50000))
    (X := (14163 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0815·γ_A/n` for `n ≥ 22000`,
`0.47 ≤ θ_in ≤ 0.48` (`J ≥ 0.54507`, `√M₁ ≤ 0.72965`, `(4c_H)^(1/4) ≤ 1.21019`,
`√ξ ≤ 0.23031 + 0.03927 + 0.00834 + 0.0075`). -/
theorem centre22k_47 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 47 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 48 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      815 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (47 / 100)) (θhi := (12 / 25)) (u := (4671 / 200000)) (Jlo := (54507 / 100000))
    (sm := (14593 / 20000)) (y := (121019 / 100000)) (s := (1371 / 2000)) (k := (1806 / 1)) (d := (1979 / 250000)) (r := (69283 / 100000))
    (sx := (23031 / 100000)) (dv := (3927 / 100000)) (sqn := (1483 / 10)) (q := (75613 / 100000)) (xr := (417 / 50000))
    (X := (14271 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0827·γ_A/n` for `n ≥ 22000`,
`0.48 ≤ θ_in ≤ 0.49` (`J ≥ 0.55276`, `√M₁ ≤ 0.72581`, `(4c_H)^(1/4) ≤ 1.20702`,
`√ξ ≤ 0.23249 + 0.03909 + 0.00846 + 0.0075`). -/
theorem centre22k_48 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 48 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 49 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      827 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (12 / 25)) (θhi := (49 / 100)) (u := (4671 / 200000)) (Jlo := (13819 / 25000))
    (sm := (72581 / 100000)) (y := (60351 / 50000)) (s := (433 / 625)) (k := (1806 / 1)) (d := (7833 / 1000000)) (r := (70001 / 100000))
    (sx := (23249 / 100000)) (dv := (3909 / 100000)) (sqn := (1483 / 10)) (q := (76397 / 100000)) (xr := (423 / 50000))
    (X := (14377 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0839·γ_A/n` for `n ≥ 22000`,
`0.49 ≤ θ_in ≤ 0.5` (`J ≥ 0.56045`, `√M₁ ≤ 0.72196`, `(4c_H)^(1/4) ≤ 1.20382`,
`√ξ ≤ 0.23461 + 0.03891 + 0.00858 + 0.0075`). -/
theorem centre22k_49 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 49 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 50 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      839 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (49 / 100)) (θhi := (1 / 2)) (u := (4671 / 200000)) (Jlo := (11209 / 20000))
    (sm := (18049 / 25000)) (y := (60191 / 50000)) (s := (7 / 10)) (k := (1806 / 1)) (d := (969 / 125000)) (r := (70711 / 100000))
    (sx := (23461 / 100000)) (dv := (3891 / 100000)) (sqn := (1483 / 10)) (q := (19293 / 25000)) (xr := (429 / 50000))
    (X := (181 / 625))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0851·γ_A/n` for `n ≥ 22000`,
`0.5 ≤ θ_in ≤ 0.51` (`J ≥ 0.56814`, `√M₁ ≤ 0.71812`, `(4c_H)^(1/4) ≤ 1.20063`,
`√ξ ≤ 0.2367 + 0.03873 + 0.0087 + 0.0075`). -/
theorem centre22k_50 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 50 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 51 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      851 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (1 / 2)) (θhi := (51 / 100)) (u := (4671 / 200000)) (Jlo := (28407 / 50000))
    (sm := (17953 / 25000)) (y := (120063 / 100000)) (s := (7071 / 10000)) (k := (1806 / 1)) (d := (307 / 40000)) (r := (14283 / 20000))
    (sx := (2367 / 10000)) (dv := (3873 / 100000)) (sqn := (1483 / 10)) (q := (3897 / 5000)) (xr := (87 / 10000))
    (X := (29163 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0862·γ_A/n` for `n ≥ 22000`,
`0.51 ≤ θ_in ≤ 0.52` (`J ≥ 0.57584`, `√M₁ ≤ 0.71427`, `(4c_H)^(1/4) ≤ 1.19742`,
`√ξ ≤ 0.23872 + 0.03854 + 0.00882 + 0.0075`). -/
theorem centre22k_51 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 51 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 52 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      862 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (51 / 100)) (θhi := (13 / 25)) (u := (4671 / 200000)) (Jlo := (3599 / 6250))
    (sm := (71427 / 100000)) (y := (59871 / 50000)) (s := (7141 / 10000)) (k := (1806 / 1)) (d := (7599 / 1000000)) (r := (4507 / 6250))
    (sx := (746 / 3125)) (dv := (1927 / 50000)) (sqn := (1483 / 10)) (q := (78701 / 100000)) (xr := (441 / 50000))
    (X := (14679 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0874·γ_A/n` for `n ≥ 22000`,
`0.52 ≤ θ_in ≤ 0.53` (`J ≥ 0.58354`, `√M₁ ≤ 0.71042`, `(4c_H)^(1/4) ≤ 1.1942`,
`√ξ ≤ 0.2407 + 0.03836 + 0.00894 + 0.0075`). -/
theorem centre22k_52 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 52 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 53 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      874 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (13 / 25)) (θhi := (53 / 100)) (u := (4671 / 200000)) (Jlo := (29177 / 50000))
    (sm := (35521 / 50000)) (y := (5971 / 5000)) (s := (7211 / 10000)) (k := (1806 / 1)) (d := (3763 / 500000)) (r := (36401 / 50000))
    (sx := (2407 / 10000)) (dv := (959 / 25000)) (sqn := (1483 / 10)) (q := (39727 / 50000)) (xr := (447 / 50000))
    (X := (591 / 2000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0885·γ_A/n` for `n ≥ 22000`,
`0.53 ≤ θ_in ≤ 0.54` (`J ≥ 0.59126`, `√M₁ ≤ 0.70656`, `(4c_H)^(1/4) ≤ 1.19096`,
`√ξ ≤ 0.24262 + 0.03818 + 0.00906 + 0.0075`). -/
theorem centre22k_53 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 53 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 54 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      885 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (53 / 100)) (θhi := (27 / 50)) (u := (4671 / 200000)) (Jlo := (29563 / 50000))
    (sm := (2208 / 3125)) (y := (14887 / 12500)) (s := (91 / 125)) (k := (1806 / 1)) (d := (3727 / 500000)) (r := (14697 / 20000))
    (sx := (12131 / 50000)) (dv := (1909 / 50000)) (sqn := (1483 / 10)) (q := (401 / 500)) (xr := (453 / 50000))
    (X := (3717 / 12500))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Changes (A), (B), (C), (D), one piece of the window: `t_A·|μ − b|² ≤ 0.0895·γ_A/n` for `n ≥ 22000`,
`0.54 ≤ θ_in ≤ 0.55` (`J ≥ 0.59898`, `√M₁ ≤ 0.7027`, `(4c_H)^(1/4) ≤ 1.18772`,
`√ξ ≤ 0.2445 + 0.03799 + 0.00917 + 0.0075`). -/
theorem centre22k_54 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 54 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      895 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (27 / 50)) (θhi := (11 / 20)) (u := (4671 / 200000)) (Jlo := (29949 / 50000))
    (sm := (7027 / 10000)) (y := (29693 / 25000)) (s := (1837 / 2500)) (k := (1806 / 1)) (d := (1477 / 200000)) (r := (37081 / 50000))
    (sx := (489 / 2000)) (dv := (3799 / 100000)) (sqn := (1483 / 10)) (q := (80939 / 100000)) (xr := (917 / 100000))
    (X := (7479 / 25000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end BstLean.Part160

open BstLean.Part160 in
#print axioms centre16_B
open BstLean.Part160 in
#print axioms centre26k_B
open BstLean.Part160 in
#print axioms centre16_BD
open BstLean.Part160 in
#print axioms centre26k_BD
open BstLean.Part160 in
#print axioms centre22k_46
open BstLean.Part160 in
#print axioms centre22k_47
open BstLean.Part160 in
#print axioms centre22k_48
open BstLean.Part160 in
#print axioms centre22k_49
open BstLean.Part160 in
#print axioms centre22k_50
open BstLean.Part160 in
#print axioms centre22k_51
open BstLean.Part160 in
#print axioms centre22k_52
open BstLean.Part160 in
#print axioms centre22k_53
open BstLean.Part160 in
#print axioms centre22k_54
