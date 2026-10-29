import BstLean.Part154Event

/-!
# Part 154: the centre bounds on `GoodC` (`n ≥ 8192`, `M_P = 1.2578`) with the facts of Part 153
that the transport lemma needs
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part153 (nrm GamS wn Eop Pb XiS Xi4 N2 hid2Mean_cr GoodAs nuA N22bar N24bar)

/-- The analogue of `GoodC16_centre` on `GoodC` (`n ≥ 8192`, `M_P = 1.2578`). -/
theorem GoodC8_centre {n : ℕ} (hn : 8192 ≤ n) {J : ℕ} (hJ : 1 ≤ J) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (h : (A₁, A₂) ∈ GoodC n J c τ)
    (hϱ : rhoBar n csC < 1 / 4)
    (he : eMP n (11 / 1000) (xiCn n (thetaC c τ)) (bN n csC (thetaC c τ)) ≤ 1 / 10)
    {θlo : ℝ} (hθ : θlo ≤ thetaC c τ) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cD n 12 (11 / 1000) (xiCn n (thetaC c τ)) +
        xiNr n (thetaC c τ) (12578 / 10000)) ∧
    rhoC c τ * √(2 / (n : ℝ)) * plow n (11 / 1000) ≤ Pb A₁ c τ A₂ ∧
    |(√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)| ≤
      √(2 / (n : ℝ) / n) *
        (LamMP n 12 (11 / 1000) (xiCn n (thetaC c τ)) (bN n csC (thetaC c τ)) +
          xiNr n (thetaC c τ) (12578 / 10000)) ∧
    √(2 / ((mA n : ℕ) : ℝ)) * nrm (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ ≤
      epsJ n J J (wn n) csC (11 / 1000) (deltaChi n 12) * √(2 / (n : ℝ) / n) ∧
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (csC / 2) * θlo ∧
    Xi4 A₁ A₂ c τ ≤ 12578 / 10000 * (2 / (n : ℝ)) / n ∧
    N2 2 A₁ A₂ c τ ≤ N22bar n 12 ∧ N2 4 A₁ A₂ c τ ≤ N24bar n 12 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, c2, c3, c4, c5⟩ := GoodC_centre hn hJ hτ h hϱ he
  have hAs := h.1
  obtain ⟨-, -, hN22, hN24, -⟩ := BstLean.Part153.GoodA_norms hn1 hAs
  have hX4 : Xi4 A₁ A₂ c τ ≤ 12578 / 10000 * (2 / (n : ℝ)) / n :=
    not_lt.mp (BstLean.Part153.GoodA_unpack hAs).2.2.2.2.2.2.2.2
  have hρ2 := rhoC_sqP c τ
  have heb0 := BstLean.Part153.AStage_eb hn hτ (θlo := θlo)
    (by rw [← hρ2]; exact hθ) hAs
  rw [← hρ2] at heb0
  have heb : 2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (csC / 2) * θlo := heb0
  exact ⟨c2, c3, c4, c5, heb, hX4, hN22, hN24⟩

end BstLean.Part154
