import BstLean.Part74LineW
import BstLean.Part74ExprG
import BstLean.Part74TabG
import BstLean.Part74FinalG

/-!
# Part 74: the line program's moment program at a general degree pair, and Theorem 1 at strict
cost for every `2 ≤ d_f ≤ d_M`

* `momProgGen74`: for every `(d, k)` there is a constant `B` such that, for every `n ≥ 2` and `K`,
  a program with the constants `0`, `1` only and cost `≤ B (n + K + 1)` returns the surrogate
  weights at every key that the line program reads. `B` is not explicit.
* `part74_single_gen`: Theorem 1 without amortization for every `2 ≤ k ≤ d`, with an existential
  threshold `n0`.
-/

namespace BstLean.Part74

open MeasureTheory BstLean.Cost
open BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)

/-- **The moment program of the line program at a general degree pair `(d, k)`**: cost
`≤ B (n + K + 1)` with `B` depending on `(d, k)` only. -/
theorem momProgGen74 (k d : ℕ) :
    ∃ B : ℕ, ∀ n K : ℕ, 2 ≤ n → ∃ pm : Prog (InM56 n) (KeyRK k d), heavyCount pm = 0 ∧
      MomSpecUsed74 pm K ∧ pm.cost ≤ B * (n + K + 1) := by
  obtain ⟨B1, h1⟩ := hInpG d k
  obtain ⟨B2, h2⟩ := hpGenY d k
  refine ⟨B1 + B2, fun n K hn => ?_⟩
  obtain ⟨p, hp, ep, cp⟩ := hp_seq (h1 n K) h2
  refine ⟨p, BstLean.Part56.MomProg.clean_heavyCount hp, ?_, ?_⟩
  · intro t v ht hv κ hκ
    rw [ep]
    have h := hInpG_val d k n K t v
    simp only at h
    show wGenY (inpG d k n K (inRK t v (Sum.inl ())) fun i => inRK t v (Sum.inr i)) κ = _
    rw [h, wGenY_inp, weightsGen74 hn K t ht v hv κ hκ]
  · have : B2 ≤ B2 * (n + K + 1) := Nat.le_mul_of_pos_right _ (by omega)
    calc p.cost ≤ B1 * (n + K + 1) + B2 := cp
      _ ≤ B1 * (n + K + 1) + B2 * (n + K + 1) := by omega
      _ = (B1 + B2) * (n + K + 1) := by ring

/-- **Theorem 1 at strict cost (no amortization) for every `2 ≤ d_f = k ≤ d = d_M`**, with a
constant `B` depending on `(d, k)` only and an existential threshold. -/
theorem part74_single_gen (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    ∃ B : ℕ, ∀ (C εlo εhi : ℝ), 0 < εlo → εlo ≤ εhi → εhi ^ 2 < 91 / 200 →
    ∃ (η : ℝ) (n0 : ℕ), 0 < η ∧ 100 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK C n η) ∧ GSpec56 pg ∧
        (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK C n η : ℝ) + 1) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
        ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
        ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          (pm.cost : ℝ) + pg.cost < baseline n d ε := by
  obtain ⟨B, hB⟩ := momProgGen74 k d
  exact ⟨B, fun C εlo εhi hlo hlh hhi =>
    part74_single_gen_of k d hk hkd B hB C εlo εhi hlo hlh hhi⟩

end BstLean.Part74

#print axioms BstLean.Part74.momProgGen74
#print axioms BstLean.Part74.part74_single_gen
