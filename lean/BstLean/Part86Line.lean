import BstLean.Part86Defs
import BstLean.Part80Cost
import BstLean.Part74FinalG

/-!
# Part 86: from the failure bound on the coefficient sphere to Theorem 1 with programs

`FailHyp d k`: the failure bound for the weight form of the line program at the surrogate of
order `KRK 1 n e80`, for every `n ≥ N86 d k`.
`part86_line_of`: Theorem 1 at `(d_M, d_f) = (d, k)`, `C = 1`, `ε = 1/2`, failure `≤ 1/100`, strict
cost, from `FailHyp`, a moment program of cost `≤ B (n + K + 1)`, and the cost comparison.
-/

namespace BstLean.Part86

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part56
open BstLean.Part74 (MomSpecUsed74 eval74)
open BstLean.Part80 (e80)

/-- The failure bound on the coefficient sphere, for every `n ≥ N86 d k`. -/
def FailHyp (d k : ℕ) : Prop :=
  ∀ n : ℕ, N86 d k ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ n →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      stdGauss (CoefIdxD n d) (SphereFail86 n d k (KRK 1 n e80) t v f0 T) ≤
        ENNReal.ofReal (1 / 100)

/-- The cost comparison, for every `n ≥ N86 d k` with `40 B ≤ n`. -/
def CostHyp (d k B : ℕ) : Prop :=
  ∀ n : ℕ, N86 d k ≤ n → 40 * B ≤ n → ∀ pmc pgc : ℕ,
    (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) →
    (pgc : ℝ) ≤ costLine56 n d k → (pmc : ℝ) + pgc < baseline n d (1 / 2)

/-- **Theorem 1 at `(d, k)` from the failure bound**, `C = 1`, `ε = 1/2`, failure `≤ 1/100`, strict
cost: for every `n ≥ N86 d k` with `40 B ≤ n`, `B` the constant of the moment program. -/
theorem part86_line_of (d k : ℕ) (B : ℕ)
    (hprog : ∀ n K : ℕ, 2 ≤ n → ∃ pm : Prog (InM56 n) (KeyRK k d), heavyCount pm = 0 ∧
      MomSpecUsed74 pm K ∧ pm.cost ≤ B * (n + K + 1))
    (hF : FailHyp d k) (hC : CostHyp d k B) :
    ∀ n : ℕ, N86 d k ≤ n → 40 * B ≤ n → 2 ≤ n →
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
  intro n hn hB hn2
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n d k (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := hprog n (KRK 1 n e80) hn2
  have hpmc' : (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) := by exact_mod_cast hpmc
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc', fun v hv t ht0 ht ε hε1 hε2 f0 T hT _ => ?_⟩
  have hε : ε = 1 / 2 := le_antisymm hε2 hε1
  subst hε
  refine ⟨?_, hC n hn hB pm.cost pg.cost hpmc' hpgc⟩
  have heval : ∀ M : CoefIdxD n d → ℝ,
      pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
        gLineW (surrRK n (KRK 1 n e80) t v) k f0 T v M :=
    fun M => eval74 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
  simp only [heval]
  exact hF n hn v hv t ht0 (by simpa using ht) f0 T hT

end BstLean.Part86

#print axioms BstLean.Part86.part86_line_of
