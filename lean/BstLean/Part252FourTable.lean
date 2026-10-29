import BstLean.Part252TableEvent
import BstLean.Part223FourSupply
import BstLean.Part242Norm

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327203636 / 10 ^ 10, 320924275 / 10 ^ 10,
    1806348476 / 10 ^ 10, 344674081 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12225) (i : Fin 4) (a : Ix 12225) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12225) (a : Ix 12225) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12225) : Prop where
  moment : ∀ i, MomentBound (muI 12225) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12225} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12225) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part252
