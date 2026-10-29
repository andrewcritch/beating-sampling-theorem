import BstLean.Part86Asm
import BstLean.Part74SingleG
import BstLean.Part74Single33

/-!
# Part 86: Theorem 1 (the line program) at every degree pair `2 ≤ d_f ≤ d_M`, `C = 1`, `ε = 1/2`,
failure `≤ 1/100`, strict cost, for every `n ≥ N86 d_M d_f`

`N86 d k = 70000 (2k+1)² C_Λ(d) 9^{dk}`, `C_Λ(d) = CLn d = (d(d+1)/2) Σ_{b=1}^d C(d,b)² (2b−1)!!`.

* `part86_line_gen`: every `2 ≤ k ≤ d`; the cost clause holds from `n ≥ max (N86 d k) (40 B)`, `B`
  the constant of the moment program of Part 74 (`momProgGen74`, not explicit).
* `part86_line_33`: `(3, 3)`, every `n ≥ N86 3 3` (`= 70000 · 49 · 306 · 9⁹ ≈ 4.07 · 10¹⁷`).
* `part86_line_33_num`: the same for every `n ≥ 5 · 10¹⁷`.
-/

namespace BstLean.Part86

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part56
open BstLean.Part74 (MomSpecUsed74)
open BstLean.Part80 (e80)

/-- **Theorem 1 at every degree pair `2 ≤ k = d_f ≤ d = d_M`**, `C = 1`, `ε = 1/2`, failure
`≤ 1/100`, strict cost, for every `n ≥ N86 d k` with `n ≥ 40 B`. -/
theorem part86_line_gen (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    ∃ B : ℕ, ∀ n : ℕ, N86 d k ≤ n → 40 * B ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n e80) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n d ε := by
  obtain ⟨B, hB⟩ := BstLean.Part74.momProgGen74 k d
  refine ⟨B, fun n hn hnB => ?_⟩
  have h7 := N86_ge d k (by omega)
  exact part86_line_of d k B hB (failHyp86 d k hk hkd)
    (fun n hn hB pmc pgc hpm hpg => cost86 d k n B hk hkd hn hB pmc pgc hpm hpg) n hn hnB
    (by omega)

theorem N86_33_ge : 40 * 1200035 ≤ N86 3 3 := by
  have h := N86_ge 3 3 (by norm_num)
  unfold N86 at h ⊢
  rw [CLn_three] at h ⊢
  norm_num

/-- **Theorem 1 at `(d_M, d_f) = (3, 3)`**, `C = 1`, `ε = 1/2`, failure `≤ 1/100`, strict cost, for
every `n ≥ N86 3 3 = 70000 · 49 · 306 · 9⁹`. -/
theorem part86_line_33 : ∀ n : ℕ, N86 3 3 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n e80) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ (1200035 : ℕ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
        stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n 3 ε := by
  intro n hn
  have h7 := N86_ge 3 3 (by norm_num)
  exact part86_line_of 3 3 1200035 BstLean.Part74.progHyp33
    (failHyp86 3 3 (by norm_num) le_rfl)
    (fun n hn hB pmc pgc hpm hpg =>
      cost86 3 3 n 1200035 (by norm_num) le_rfl hn hB pmc pgc hpm hpg) n hn
    (le_trans N86_33_ge hn) (by omega)

/-- **Theorem 1 at `(3, 3)` for every `n ≥ 5 · 10¹⁷`.** -/
theorem part86_line_33_num : ∀ n : ℕ, 5 * 10 ^ 17 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n e80) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ (1200035 : ℕ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
        stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n 3 ε :=
  fun n hn => part86_line_33 n (le_trans N86_33_le hn)

end BstLean.Part86

#print axioms BstLean.Part86.part86_line_gen
#print axioms BstLean.Part86.part86_line_33
#print axioms BstLean.Part86.part86_line_33_num
