import BstLean.Part187All
import BstLean.Part160MFBNum
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final
import BstLean.Part188R154C16
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16
import BstLean.Part188R154Num16
import BstLean.Part188R160Lib
import BstLean.Part188R160Event
import BstLean.Part188R160MFNum
import BstLean.Part188R160MFB3
import BstLean.Part188R160MFB4





namespace BstLean.Part188.Base160_R
open BstLean.Part160 BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part154
open BstLean.Part153 (hid2Mean_cr)

/-- Changes (A), (B), (C), (D): `t_A·|μ − b|² ≤ 0.1024·γ_A/n` for `n ≥ 16200`,
`0.46 ≤ θ_in ≤ 0.55` (`J ≥ 0.53588`, `√M₁ ≤ 0.73425`, `(4c_H)^(1/4) ≤ 1.21399`,
`√ξ ≤ 0.25574 + 0.04571 + 0.01063 + 0.0075`). -/
theorem centre16_BD {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      41 / 400 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (23 / 50)) (θhi := (11 / 20)) (u := (27217 / 1000000)) (Jlo := (267913 / 500000))
    (sm := (734277 / 1000000)) (y := (1214023 / 1000000)) (s := (84779 / 125000)) (k := (1435 / 1)) (d := (1007 / 100000)) (r := (37081 / 50000))
    (sx := (255861 / 1000000)) (dv := (45969 / 1000000)) (sqn := (6363961 / 50000)) (q := (404693 / 500000)) (xr := (5343 / 500000))
    (X := (80009 / 250000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end BstLean.Part188.Base160_R

