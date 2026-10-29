import BstLean.Part74W33
import BstLean.Part74Expr
import BstLean.Part74Tab33
import BstLean.Part74Final33

/-!
# Part 74: Theorem 1 at `(d_M, d_f) = (3, 3)` at strict cost (no amortization)

* `momProg74_33`: the moment program (constants `0`, `1`; reads `t`, `v`; cost
  `≤ 154 n + 238 K + 35 + B33`, `B33 ≤ 1200000`) returns the surrogate weights at every key that
  `pg` reads (`MomSpecUsed74`).
* `part74_single_33`: Theorem 1 at `(3, 3)`, `C = 1`, `ε = 1/2`, failure `1/100`, for every
  `n ≥ 10^125`, with `cost(pm) + cost(pg) < baseline n 3 ε` and no counter.
-/

namespace BstLean.Part74

open MeasureTheory BstLean.Cost
open BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)

/-- **The moment program at `(d_M, d_f) = (3, 3)`**: constants `0`, `1` only; its value at every
key is the explicit weight `w33`; cost `≤ 154 n + 238 K + 35 + B33`. -/
theorem momProg74_33_nat (n K : ℕ) :
    ∃ pm : Prog (InM56 n) (KeyRK 3 3), heavyCount pm = 0 ∧
      (∀ (t : ℝ) (v : Fin n → ℝ) κ, pm.eval (inRK t v) κ = w33 n K t v κ) ∧
      pm.cost ≤ 154 * n + 238 * K + 35 + B33 := by
  obtain ⟨p, hp, ep, cp⟩ := hp_seq (hInp33 n K) hp33Y
  refine ⟨p, BstLean.Part56.MomProg.clean_heavyCount hp, ?_, cp⟩
  intro t v κ
  rw [ep]
  have h := hInp33_val n K t v
  simp only at h
  show w33Y (inp33 n K (inRK t v (Sum.inl ())) fun i => inRK t v (Sum.inr i)) κ = _
  rw [h, w33Y_inp]

/-- The moment program meets the specification of the read keys, at cost
`≤ 154 n + 238 K + 1200035`. -/
theorem momProg74_33 (n K : ℕ) (hn : 2 ≤ n) :
    ∃ pm : Prog (InM56 n) (KeyRK 3 3), heavyCount pm = 0 ∧ MomSpecUsed74 pm K ∧
      pm.cost ≤ 154 * n + 238 * K + 1200035 := by
  obtain ⟨pm, h0, he, hc⟩ := momProg74_33_nat n K
  refine ⟨pm, h0, ?_, by have := B33_le; omega⟩
  intro t v ht hv κ hκ
  rw [he, weights33_74 hn K t ht v hv κ hκ]

theorem progHyp33 : ProgHyp33 1200035 := by
  intro n K hn
  obtain ⟨pm, h0, hs, hc⟩ := momProg74_33 n K hn
  exact ⟨pm, h0, hs, by nlinarith⟩

/-- **Theorem 1 at `(d_M, d_f) = (3, 3)`, `C = 1`, `ε = 1/2`, failure `1/100`, at strict cost, for
every `n ≥ 10^125`.** -/
theorem part74_single_33 : ∀ n : ℕ, 10 ^ 125 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n eC74_33) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ (1200035 : ℕ) * ((n : ℝ) + (KRK 1 n eC74_33 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
        stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n 3 ε :=
  part74_single_33_of 1200035 (by norm_num) progHyp33

end BstLean.Part74

#print axioms BstLean.Part74.part74_single_33
#print axioms BstLean.Part74.momProg74_33
