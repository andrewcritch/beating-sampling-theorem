import BstLean.Part160MFDC

/-!
# Part 160 (file `MFDNum`): numeric instances of the centre charge with changes (A), (C), (D)

Do not use `sorry`, `native_decide` or `axiom`. The certificates are generated; each side
condition is closed by `norm_num`.

* `centre16_D`, `centre26k_D`: the whole window `0.46 ≤ θ_in ≤ 0.55`.
* `centre22k_D_46`, …, `centre22k_D_54`: the nine pieces of width `0.01`, `n ≥ 22000`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part154
open BstLean.Part153 (hid2Mean_cr)

/-- `t_A·|μ − b|² ≤ 0.1653·γ_A/n` for `n ≥ 16384`, `0.46 ≤ θ_in ≤ 0.55`
(`√ξ ≤ 0.34266 + 0.04571 + 0.01063 + 0.0075`). -/
theorem centre16_D {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1653 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((16384 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ hθ0 hθ1 h hD
    (n1 := 16384) (θlo := (23 / 50)) (θhi := (11 / 20)) (r := (37081 / 50000)) (sx := (17133 / 50000)) (dv := (4571 / 100000))
    (sqn := (128 / 1)) (q := (80939 / 100000)) (xr := (1063 / 100000)) (X := (813 / 2000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.156·γ_A/n` for `n ≥ 26000`, `0.46 ≤ θ_in ≤ 0.55`
(`√ξ ≤ 0.34266 + 0.03629 + 0.00844 + 0.0075`). -/
theorem centre26k_D {n : ℕ} (hn : 26000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1560 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((26000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ hθ0 hθ1 h hD
    (n1 := 26000) (θlo := (23 / 50)) (θhi := (11 / 20)) (r := (37081 / 50000)) (sx := (17133 / 50000)) (dv := (3629 / 100000))
    (sqn := (806 / 5)) (q := (80939 / 100000)) (xr := (211 / 25000)) (X := (39489 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1304·γ_A/n` for `n ≥ 22000`, `0.46 ≤ θ_in ≤ 0.47`
(`√ξ ≤ 0.30582 + 0.03945 + 0.00822 + 0.0075`). -/
theorem centre22k_D_46 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 47 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1304 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ hθ0 (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (23 / 50)) (θhi := (47 / 100)) (r := (68557 / 100000)) (sx := (15291 / 50000)) (dv := (789 / 20000))
    (sqn := (1483 / 10)) (q := (74821 / 100000)) (xr := (411 / 50000)) (X := (36099 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1337·γ_A/n` for `n ≥ 22000`, `0.47 ≤ θ_in ≤ 0.48`
(`√ξ ≤ 0.3105 + 0.03927 + 0.00834 + 0.0075`). -/
theorem centre22k_D_47 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 47 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 48 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1337 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (47 / 100)) (θhi := (12 / 25)) (r := (69283 / 100000)) (sx := (621 / 2000)) (dv := (3927 / 100000))
    (sqn := (1483 / 10)) (q := (75613 / 100000)) (xr := (417 / 50000)) (X := (36561 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1371·γ_A/n` for `n ≥ 22000`, `0.48 ≤ θ_in ≤ 0.49`
(`√ξ ≤ 0.31516 + 0.03909 + 0.00846 + 0.0075`). -/
theorem centre22k_D_48 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 48 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 49 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1371 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (12 / 25)) (θhi := (49 / 100)) (r := (70001 / 100000)) (sx := (7879 / 25000)) (dv := (3909 / 100000))
    (sqn := (1483 / 10)) (q := (76397 / 100000)) (xr := (423 / 50000)) (X := (37021 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1405·γ_A/n` for `n ≥ 22000`, `0.49 ≤ θ_in ≤ 0.5`
(`√ξ ≤ 0.31979 + 0.03891 + 0.00858 + 0.0075`). -/
theorem centre22k_D_49 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 49 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 50 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1405 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (49 / 100)) (θhi := (1 / 2)) (r := (70711 / 100000)) (sx := (31979 / 100000)) (dv := (3891 / 100000))
    (sqn := (1483 / 10)) (q := (19293 / 25000)) (xr := (429 / 50000)) (X := (18739 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1439·γ_A/n` for `n ≥ 22000`, `0.5 ≤ θ_in ≤ 0.51`
(`√ξ ≤ 0.32441 + 0.03873 + 0.0087 + 0.0075`). -/
theorem centre22k_D_50 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 50 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 51 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1439 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (1 / 2)) (θhi := (51 / 100)) (r := (14283 / 20000)) (sx := (32441 / 100000)) (dv := (3873 / 100000))
    (sqn := (1483 / 10)) (q := (3897 / 5000)) (xr := (87 / 10000)) (X := (18967 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1474·γ_A/n` for `n ≥ 22000`, `0.51 ≤ θ_in ≤ 0.52`
(`√ξ ≤ 0.329 + 0.03854 + 0.00882 + 0.0075`). -/
theorem centre22k_D_51 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 51 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 52 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1474 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (51 / 100)) (θhi := (13 / 25)) (r := (4507 / 6250)) (sx := (329 / 1000)) (dv := (1927 / 50000))
    (sqn := (1483 / 10)) (q := (78701 / 100000)) (xr := (441 / 50000)) (X := (19193 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1509·γ_A/n` for `n ≥ 22000`, `0.52 ≤ θ_in ≤ 0.53`
(`√ξ ≤ 0.33357 + 0.03836 + 0.00894 + 0.0075`). -/
theorem centre22k_D_52 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 52 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 53 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1509 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (13 / 25)) (θhi := (53 / 100)) (r := (36401 / 50000)) (sx := (33357 / 100000)) (dv := (959 / 25000))
    (sqn := (1483 / 10)) (q := (39727 / 50000)) (xr := (447 / 50000)) (X := (38837 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1544·γ_A/n` for `n ≥ 22000`, `0.53 ≤ θ_in ≤ 0.54`
(`√ξ ≤ 0.33813 + 0.03818 + 0.00906 + 0.0075`). -/
theorem centre22k_D_53 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 53 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 54 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1544 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 22000) (θlo := (53 / 100)) (θhi := (27 / 50)) (r := (14697 / 20000)) (sx := (33813 / 100000)) (dv := (1909 / 50000))
    (sqn := (1483 / 10)) (q := (401 / 500)) (xr := (453 / 50000)) (X := (39287 / 100000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `t_A·|μ − b|² ≤ 0.1579·γ_A/n` for `n ≥ 22000`, `0.54 ≤ θ_in ≤ 0.55`
(`√ξ ≤ 0.34266 + 0.03799 + 0.00917 + 0.0075`). -/
theorem centre22k_D_54 {n : ℕ} (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 54 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1579 / 10000 * (2 / (n : ℝ)) / n := by
  have hnR : ((22000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact centre_D_gen (by omega) hτ (le_trans (by norm_num) hθ0) hθ1 h hD
    (n1 := 22000) (θlo := (27 / 50)) (θhi := (11 / 20)) (r := (37081 / 50000)) (sx := (17133 / 50000)) (dv := (3799 / 100000))
    (sqn := (1483 / 10)) (q := (80939 / 100000)) (xr := (917 / 100000)) (X := (9933 / 25000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end BstLean.Part160

open BstLean.Part160 in
#print axioms centre16_D
open BstLean.Part160 in
#print axioms centre26k_D
open BstLean.Part160 in
#print axioms centre22k_D_46
open BstLean.Part160 in
#print axioms centre22k_D_47
open BstLean.Part160 in
#print axioms centre22k_D_48
open BstLean.Part160 in
#print axioms centre22k_D_49
open BstLean.Part160 in
#print axioms centre22k_D_50
open BstLean.Part160 in
#print axioms centre22k_D_51
open BstLean.Part160 in
#print axioms centre22k_D_52
open BstLean.Part160 in
#print axioms centre22k_D_53
open BstLean.Part160 in
#print axioms centre22k_D_54
