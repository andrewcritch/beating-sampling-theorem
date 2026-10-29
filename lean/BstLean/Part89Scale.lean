import BstLean.Part89SDefs
import BstLean.Part86Scale

/-!
# Part 89, `Scale`: the pointwise scale comparison between two scales in the abstract model

`scaleE89 : ScaleE M k`, given the two-point identity `TwoPt n J`. Both conjuncts of
`Part84.ScaleIface` at `s = lam² κ`, `s' = lam'² κ`, `s₀ = min(lam², lam'²) κ`.
-/

namespace BstLean.Part89

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (frob IsSymmT Tens)
open BstLean.Part53 (heatA tinner fvA)
open BstLean.Part59 (tensOf)
open BstLean.Part78 (zv)
open BstLean.Part84 (hmean en scaleIface)
open BstLean.Part84.Rep (cOf polyEval_cOf)
open BstLean.Part86
open BstLean.Part86.ScaleAux

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

/-- **Scale comparison between two scales, pointwise.** -/
theorem scaleE89 (M : Mod n I J S G) (k : ℕ) (hk : 1 ≤ k) (hT : TwoPt n J) (hn : 1 ≤ n) :
    ScaleE M k := by
  intro P hP lam lam' hlam hlam' x
  have : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  set Q := Px (M.b x) P with hQ
  have hQd : Q.totalDegree ≤ k := (Px_deg _ _).trans hP
  set A : Tens n := tensOf k (cOf k Q) with hAdef
  have hA : ∀ j, IsSymmT (A j) := BstLean.Part59.tensOf_symm59x n k (cOf k Q)
  have hF : ∀ (l : ℝ) (W : J × Fin n → ℝ),
      Fm M P l W x = fvA k A (fun i => l * zv W (M.ps x) i) := by
    intro l W
    rw [hAdef, BstLean.Part59.fvA_tensOf59x, polyEval_cOf k Q hQd, hQ, Px_eval]
    rfl
  set κ := ∑ q, M.ps x q ^ 2 with hκ
  have hκ0 : 0 ≤ κ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hPhi : ∀ l : ℝ, Phi M P l x = hmean k (l ^ 2 * κ) A := by
    intro l
    unfold Phi
    simp_rw [hF]
    exact (rep hT k A hA l (M.ps x)).1
  have hVar : ∀ l : ℝ, ∫ W : J × Fin n → ℝ, (Fm M P l W x - Phi M P l x) ^ 2
      ∂stdGauss (J × Fin n) = en k (l ^ 2 * κ) A := by
    intro l
    rw [hPhi]
    simp_rw [hF]
    exact (rep hT k A hA l (M.ps x)).2
  rw [hVar, hVar, hPhi, hPhi]
  rcases hκ0.eq_or_lt with h0 | hpos
  · have hen0 : en k 0 A = 0 := by
      unfold en
      apply Finset.sum_eq_zero
      intro c hc
      have hc1 : c ≠ 0 := by
        have := (Finset.mem_Icc.mp hc).1
        omega
      simp [zero_pow hc1]
    rw [← h0]
    simp only [mul_zero, sub_self, hen0]
    constructor <;> simp
  have hl : 0 < lam ^ 2 := by positivity
  have hl' : 0 < lam' ^ 2 := by positivity
  have hm : 0 < min (lam ^ 2) (lam' ^ 2) := lt_min hl hl'
  have hs0 : 0 < min (lam ^ 2) (lam' ^ 2) * κ := mul_pos hm hpos
  have h1 : min (lam ^ 2) (lam' ^ 2) * κ ≤ lam ^ 2 * κ :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hpos.le
  have h2 : min (lam ^ 2) (lam' ^ 2) * κ ≤ lam' ^ 2 * κ :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
  have ht : |lam' ^ 2 * κ - lam ^ 2 * κ| * Real.sqrt n / (min (lam ^ 2) (lam' ^ 2) * κ) =
      tSc n lam lam' := by
    unfold tSc
    rw [show lam' ^ 2 * κ - lam ^ 2 * κ = (lam' ^ 2 - lam ^ 2) * κ by ring, abs_mul,
      abs_of_pos hpos]
    field_simp
  have h := scaleIface n k A hA (lam ^ 2 * κ) (lam' ^ 2 * κ) (min (lam ^ 2) (lam' ^ 2) * κ)
    hs0 h1 h2
  rw [ht] at h
  exact h

end BstLean.Part89

#print axioms BstLean.Part89.scaleE89
