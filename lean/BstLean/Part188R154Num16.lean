import BstLean.Part187All
import BstLean.Part154Num16
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16





namespace BstLean.Part188.Base154_R
open BstLean.Part154 BstLean.Part154.R

open Real
open BstLean.Part150 (epsJ)
open BstLean.Part153 (wn N22bar N24bar)

theorem rhoBar_lt16 {n : ℕ} (hn : 16200 ≤ n) : rhoBar n csC < 1 / 4 :=
  rhoBar_ltA16 hn

theorem eMP_le16 {n : ℕ} (hn : 16200 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    eMP n (11 / 1000) (xiCn n θ) (bN n csC θ) ≤ 1 / 10 :=
  eMP_leA16 hn h0 h1

/-- `√ξ°_hp ≤ 0.6890`. -/
theorem x1_le16 {n : ℕ} (hn : 16200 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    cD n 12 (11 / 1000) (xiCn n θ) + xiNr n θ (11911 / 10000) ≤ 6890 / 10000 :=
  x1_leB16 hn h0 h1 (xiCn_leA16 hn h0 h1).1 (xiCn_leA16 hn h0 h1).2.1

/-- `√ξ°_∥ ≤ 0.1601`. -/
theorem x2_le16 {n : ℕ} (hn : 16200 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    LamMP n 12 (11 / 1000) (xiCn n θ) (bN n csC θ) + xiNr n θ (11911 / 10000) ≤
      1601 / 10000 :=
  x2_leB16 hn h0 h1 (xiCn_leA16 hn h0 h1).1 (xiCn_leA16 hn h0 h1).2.1 (xiCn_leA16 hn h0 h1).2.2.1 (xiCn_leA16 hn h0 h1).2.2.2

theorem plow_ge16 {n : ℕ} (hn : 16200 ≤ n) : 56 / 100 ≤ plow n (11 / 1000) :=
  plow_geB16 hn

/-- `ϵ_J ≤ 0.00752` for `J = n` atoms. -/
theorem epsJ_le16 {n : ℕ} (hn : 16200 ≤ n) :
    0 ≤ epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ∧
    epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ 752 / 100000 :=
  epsJ_leB16 hn

/-- The norm deviations in the form of Part 151. -/
theorem Nbar_le16 {n : ℕ} (hn : 16200 ≤ n) :
    0 ≤ N22bar n 12 ∧ N22bar n 12 ≤ 18334 / 1000 / (n : ℝ) ∧
    0 ≤ N24bar n 12 ∧ N24bar n 12 ≤ 24779 / 1000 / (n : ℝ) :=
  Nbar_leB16 hn

end BstLean.Part188.Base154_R
