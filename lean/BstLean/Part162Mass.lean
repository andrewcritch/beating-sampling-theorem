import BstLean.Part162VS
import BstLean.Part160Mass

/-!
# Part 162: the mass below the floor from Part 160's base-event quantities

Role: `delegations/statements/p162-spec.md`, items 3 and 4. Do not use `sorry`, `native_decide`
or `axiom`.

* `mass_eq_stand`: `∫_a ν{σ < σ_l} = ν'{σ < σ_l}` (latitude decomposition).
* **`mass_of_base`**: the hypothesis `hmass` (`β_low`) of the interface from the quantities of
  Part 160's `mass_bound4` (`Ξ`, `Ξ₄`, `e_b`, `ξ`, `N₂₂`): `β_low = (2a + √(4a² + N²))²/(n²(s − sd)⁴)`
  for the floor `σ_l = √(2/n)·sd`. (This uses a fourth moment of `σ`; the paper uses order 320,
  so this `β_low` is weaker than the paper's.)
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg hid2 sphPt mA)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- **The mass below the floor is a stand-in mass**: `∫_a ν{σ(a, v) < σ_l} = ν'{σ(x) < σ_l}`
(by the latitude decomposition `nuStand_latitude`). -/
theorem mass_eq_stand (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < D.tau0 c) (σl : ℝ) :
    ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n =
      (stdGauss (Fin n)).real {ξ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < σl} := by
  set ν := stdGauss (Fin (n - 1))
  set S := {p : Ix n × (Fin (n - 1) → ℝ) | sgA D c p.1 p.2 < σl} with hS
  have mS : MeasurableSet S := measurableSet_lt (measurable_sgA D c) measurable_const
  have h1 : ∫ a, ν.real {v | sgA D c a v < σl} ∂muI n = ((muI n).prod ν).real S := by
    rw [measureReal_def, Measure.prod_apply mS, ← integral_toReal]
    · rfl
    · exact (measurable_measure_prodMk_left mS).aemeasurable
    · exact Filter.Eventually.of_forall fun a => measure_lt_top _ _
  rw [h1]
  have hmapF : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
      xLat c (latitude (√(normSq c.1.2)) (D.tau0 c) p.1) (unitF53 p.2)) := measurable_xA D c
  have hT : MeasurableSet {x : Fin n → ℝ | sigX D c x < σl} :=
    measurableSet_lt (measurable_sigX D c) measurable_const
  have h2 : (stdGauss (Fin n)).real {ξ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < σl} =
      (nuStand D c).real {x | sigX D c x < σl} := by
    rw [nuStand, map_measureReal_apply _ hT]
    · rfl
    · exact BstLean.Part130.measurable_sphPt.comp (by fun_prop)
  rw [h2, nuStand_latitude hn D c hc hτ, map_measureReal_apply hmapF hT]
  rfl

open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr) in
open BstLean.Part134 (res sig) in
/-- **The mass below the floor from the base-event quantities of Part 160** (`mass_bound4`: the
fourth moment of `σ` on the stand-in input; Part 06's `β_d` in a weaker form): with the floor
`σ_l = √(2/n)·sd`, `∫_a ν{σ < σ_l} ≤ (2a + √(4a² + N²))²/(n·(s − sd)⁴)/n`. -/
theorem mass_of_base (hn : 6 ≤ n) (D : Design n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {N a eb xi N22 e1 e2 sd s : ℝ}
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hsd : 0 ≤ sd) (hs : sd < s)
    (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n) :
    ∫ a', (stdGauss (Fin (n - 1))).real {v | sgA D c a' v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      (2 * a + √(4 * a ^ 2 + N ^ 2)) ^ 2 / (n * (s - sd) ^ 4) / n := by
  rw [mass_eq_stand (by omega) D c hc hτ]
  have h := BstLean.Part160.mass_bound4 hn c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb hXi hXi4 heb hxi hN22
    he1 he1' he2 he2' hsd hs hs2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hset : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < √(2 / (n : ℝ)) * sd} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1)
        (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    simp only [Set.mem_setOf_eq]
    set R := normSq (res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))))
    have hR : 0 ≤ R := normSq_nonneg _
    have hsig : sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) = √(2 / (mA n : ℝ)) * √R := rfl
    rw [hsig, ← Real.sqrt_mul (by positivity)]
    have e : √(2 / (n : ℝ)) * sd = √(2 / (n : ℝ) * sd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hsd]
    rw [e]
    exact Real.sqrt_lt_sqrt_iff (by positivity)
  rw [hset]
  rw [le_div_iff₀ hnR, mul_comm]
  exact h

end BstLean.Part162

open BstLean.Part162 in
#print axioms mass_of_base
