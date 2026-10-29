import BstLean.Part86Defs
import BstLean.Part84Poly

/-!
# Part 86, the failure bound from the interfaces

* `PU_degree`: the polynomial given the anchors has total degree `≤ k`.
* `fail86_core`: polar reduction, the sphere step in the scale window, and the scale tail give the
  failure bound on the coefficient sphere.
-/

namespace BstLean.Part86

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono Tens TSymm)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV)

theorem fPoly_degree {n : ℕ} (k : ℕ) (f0 : ℝ) (T : Tens n) : (fPoly k f0 T).totalDegree ≤ k := by
  unfold fPoly
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine BstLean.Part84.totalDegree_finset_sum_le (fun j hj => ?_)
  refine BstLean.Part84.totalDegree_finset_sum_le (fun w _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ t : Fin j, (MvPolynomial.X (w t) : MvPolynomial (Fin n) ℝ).totalDegree
      = ∑ _t : Fin j, 1 := by simp
    _ = j := by simp
    _ ≤ k := (Finset.mem_Icc.mp hj).2

theorem PU_degree {n : ℕ} {I : Type} [Fintype I] (k : ℕ) (f0 : ℝ) (T : Tens n)
    (U : I × Fin n → ℝ) (r sc : ℝ) : (PU k f0 T U r sc).totalDegree ≤ k := by
  unfold PU
  refine le_trans ?_ (fPoly_degree k f0 T)
  refine BstLean.Part84.deg_aeval _ (fun i => ?_) _
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine BstLean.Part84.totalDegree_finset_sum_le (fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

/-- **The failure bound from the interfaces.** -/
theorem fail86_core (m d k K : ℕ) (bound Ct : ℝ) (t : ℝ) (v : Fin (m + 1) → ℝ) (ht : 0 ≤ t)
    (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (hE : RotE v E)
    (hPol : PolarRed86 m d k K)
    (hRem : RemezStep86 (modRK m d t v E) k (gqRK m d K t v E) bound)
    (hTail : TailIface86 (m + 1) d Ct)
    (f0 : ℝ) (T : Tens (m + 1)) (hT : TSymm k T) :
    stdGauss (CoefIdxD (m + 1) d) (SphereFail86 (m + 1) d k K t v f0 T) ≤
      ENNReal.ofReal bound + ENNReal.ofReal (Ct / ((m + 1 : ℕ) : ℝ)) := by
  classical
  set S : Set ((Fin (d + 1) × Fin (m + 1) → ℝ) × (JR (m + 1) d × Fin (m + 1) → ℝ)) :=
    {p | 1 / (((m + 1 : ℕ) : ℝ)) <
      |lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) p.1 (radF53 p.2) ^ 2 - 1|} with hS
  have hpt : ∀ (U : Fin (d + 1) × Fin (m + 1) → ℝ) (W' : JR (m + 1) d × Fin (m + 1) → ℝ),
      stdGauss (JR (m + 1) d × Fin (m + 1))
          (badSet86 (modRK m d t v E) (gqRK m d K t v E)
            (PU k f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
              (1 / Real.sqrt (DD (m + 1) d)))
            (lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W'))) ≤
        ENNReal.ofReal bound + S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W') := by
    intro U W'
    by_cases h : (U, W') ∈ S
    · rw [Set.indicator_of_mem h]
      exact (prob_le_one).trans le_add_self
    · rw [Set.indicator_of_notMem h, add_zero]
      have h' : |lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W') ^ 2 - 1| ≤
          1 / (((m + 1 : ℕ) : ℝ)) := by
        simpa [hS, not_lt] using h
      exact hRem _ (PU_degree k f0 T U _ _) _ h'
  refine (hPol t v ht hv E hE f0 T hT).trans ?_
  refine (lintegral_mono fun U => lintegral_mono fun W' => hpt U W').trans ?_
  have e1 : ∀ U : Fin (d + 1) × Fin (m + 1) → ℝ, ∫⁻ W' : JR (m + 1) d × Fin (m + 1) → ℝ,
      (ENNReal.ofReal bound + S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W'))
      ∂stdGauss (JR (m + 1) d × Fin (m + 1)) =
      ENNReal.ofReal bound +
        ∫⁻ W' : JR (m + 1) d × Fin (m + 1) → ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W')
          ∂stdGauss (JR (m + 1) d × Fin (m + 1)) := by
    intro U
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  simp_rw [e1]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  gcongr
  exact hTail

end BstLean.Part86

#print axioms BstLean.Part86.fail86_core
