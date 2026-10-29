import BstLean.Part160MFBNum
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Lib
import BstLean.Part187R160Event
import BstLean.Part187R160MFNum
import BstLean.Part187R160MFB3
import BstLean.Part187R160MFB4

/-! Part 187 (file `Part187R160MFBNum`): copy of `Part160MFBNum` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part154
open BstLean.Part153 (hid2Mean_cr)

/-- Changes (A), (B), (C), (D): `t_A·|μ − b|² ≤ 0.1024·γ_A/n` for `n ≥ 16250`,
`0.46 ≤ θ_in ≤ 0.55` (`J ≥ 0.53588`, `√M₁ ≤ 0.73425`, `(4c_H)^(1/4) ≤ 1.21399`,
`√ξ ≤ 0.25574 + 0.04571 + 0.01063 + 0.0075`). -/
theorem centre16_BD {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1024 / 10000 * (2 / (n : ℝ)) / n := by
  exact centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16250) (θlo := (23 / 50)) (θhi := (11 / 20)) (u := (3397 / 125000)) (Jlo := (13396 / 25000))
    (sm := (73427 / 100000)) (y := (121402 / 100000)) (s := (3391 / 5000)) (k := (1439 / 1)) (d := (503 / 50000)) (r := (37081 / 50000))
    (sx := (12791 / 50000)) (dv := (4590 / 100000)) (sqn := (127 / 1)) (q := (80939 / 100000)) (xr := (1071 / 100000))
    (X := (15998 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end BstLean.Part160.R

