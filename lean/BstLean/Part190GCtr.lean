import BstLean.Part188All
import BstLean.Part188R160MFB4



namespace BstLean.Part190.Frame16200
open BstLean.Part183 BstLean.Part183.F16250

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part160
open BstLean.Part153 (hid2Mean_cr)

theorem centreF16200_46 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 23 / 50 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 47 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      427 / 5000 * (2 / (n : ℝ)) / n := by
  exact BstLean.Part188.Base160_R.centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (23 / 50)) (θhi := (47 / 100)) (u := (27217 / 1000000)) (Jlo := (267913 / 500000))
    (sm := (734277 / 1000000)) (y := (1214023 / 1000000)) (s := (84779 / 125000)) (k := (1435 / 1)) (d := (1007 / 100000)) (r := (342783 / 500000))
    (sx := (45823 / 200000)) (dv := (45969 / 1000000)) (sqn := (6363961 / 50000)) (q := (74821 / 100000)) (xr := (1197 / 125000))
    (X := (14609 / 50000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem centreF16200_47 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 47 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 12 / 25)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      867 / 10000 * (2 / (n : ℝ)) / n := by
  exact BstLean.Part188.Base160_R.centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (47 / 100)) (θhi := (12 / 25)) (u := (27217 / 1000000)) (Jlo := (271757 / 500000))
    (sm := (730433 / 1000000)) (y := (1210853 / 1000000)) (s := (137113 / 200000)) (k := (1435 / 1)) (d := (4981 / 500000)) (r := (692821 / 1000000))
    (sx := (57837 / 250000)) (dv := (45759 / 1000000)) (sqn := (6363961 / 50000)) (q := (756127 / 1000000)) (xr := (9717 / 1000000))
    (X := (36793 / 125000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem centreF16200_48 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 12 / 25 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 49 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      879 / 10000 * (2 / (n : ℝ)) / n := by
  exact BstLean.Part188.Base160_R.centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (12 / 25)) (θhi := (49 / 100)) (u := (27217 / 1000000)) (Jlo := (689 / 1250))
    (sm := (72659 / 100000)) (y := (301919 / 250000)) (s := (34641 / 50000)) (k := (1435 / 1)) (d := (4929 / 500000)) (r := (7 / 10))
    (sx := (23353 / 100000)) (dv := (45549 / 1000000)) (sqn := (6363961 / 50000)) (q := (763963 / 1000000)) (xr := (9857 / 1000000))
    (X := (37057 / 125000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem centreF16200_49 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 49 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 1 / 2)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      223 / 2500 * (2 / (n : ℝ)) / n := by
  exact BstLean.Part188.Base160_R.centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (49 / 100)) (θhi := (1 / 2)) (u := (27217 / 1000000)) (Jlo := (69861 / 125000))
    (sm := (361373 / 500000)) (y := (120449 / 100000)) (s := (7 / 10)) (k := (1435 / 1)) (d := (9757 / 1000000)) (r := (707107 / 1000000))
    (sx := (235663 / 1000000)) (dv := (22669 / 500000)) (sqn := (6363961 / 50000)) (q := (771719 / 1000000)) (xr := (9997 / 1000000))
    (X := (149259 / 500000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem centreF16200_50 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 1 / 2 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 51 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      113 / 1250 * (2 / (n : ℝ)) / n := by
  exact BstLean.Part188.Base160_R.centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (1 / 2)) (θhi := (51 / 100)) (u := (27217 / 1000000)) (Jlo := (28329 / 50000))
    (sm := (718901 / 1000000)) (y := (600647 / 500000)) (s := (353553 / 500000)) (k := (1435 / 1)) (d := (9659 / 1000000)) (r := (714143 / 1000000))
    (sx := (14859 / 62500)) (dv := (22563 / 500000)) (sqn := (6363961 / 50000)) (q := (389699 / 500000)) (xr := (1267 / 125000))
    (X := (150263 / 500000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem centreF16200_51 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 51 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 13 / 25)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      183 / 2000 * (2 / (n : ℝ)) / n := by
  exact BstLean.Part188.Base160_R.centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (51 / 100)) (θhi := (13 / 25)) (u := (27217 / 1000000)) (Jlo := (574277 / 1000000))
    (sm := (178763 / 250000)) (y := (599043 / 500000)) (s := (357071 / 500000)) (k := (1435 / 1)) (d := (9563 / 1000000)) (r := (721111 / 1000000))
    (sx := (7493 / 31250)) (dv := (44913 / 1000000)) (sqn := (6363961 / 50000)) (q := (393501 / 500000)) (xr := (5137 / 500000))
    (X := (302483 / 1000000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem centreF16200_52 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 13 / 25 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 66 / 125)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      923 / 10000 * (2 / (n : ℝ)) / n := by
  exact BstLean.Part188.Base160_R.centre_BD_gen (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) h hD
    (n1 := 16200) (θlo := (13 / 25)) (θhi := (66 / 125)) (u := (27217 / 1000000)) (Jlo := (290991 / 500000))
    (sm := (889 / 1250)) (y := (298717 / 250000)) (s := (72111 / 100000)) (k := (1435 / 1)) (d := (9471 / 1000000)) (r := (726637 / 1000000))
    (sx := (241117 / 1000000)) (dv := (44699 / 1000000)) (sqn := (6363961 / 50000)) (q := (793033 / 1000000)) (xr := (649 / 62500))
    (X := (7593 / 25000))
    (by norm_num) (by exact_mod_cast hn) (by norm_num) (le_trans (by norm_num) hθ0)
    (le_trans hθ1 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end BstLean.Part190.Frame16200

open BstLean.Part190.Frame16200 in
#print axioms centreF16200_52
