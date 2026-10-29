import BstLean.Part89QCore

/-!
# Part 89, `failQ_core2`: the failure bound with a general affine sphere-step bound

Same as `failQ_core`, with the sphere-step bound `A0 + A1 * Ỹ(U)` for any `A0, A1 ≥ 0`.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part89

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono Tens TSymm)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV)
open BstLean.Part86

/-- **The failure bound from the interfaces, with a general sphere-step bound affine in `Ỹ(U)`.** -/
theorem failQ_core2 (m d K : ℕ) (Ct A0 A1 : ℝ) (t : ℝ) (v : Fin (m + 1) → ℝ)
    (ht : 0 ≤ t) (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (hE : RotE v E)
    (hPol : PolarRed86 m d 2 K) (hTail : TailIface86 (m + 1) d Ct)
    (f0 : ℝ) (T : Tens (m + 1)) (hT : TSymm 2 T) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hDW : 0 < DWr (m + 1) (JR (m + 1) d))
    (hpt : ∀ (U : Fin (d + 1) × Fin (m + 1) → ℝ) (W' : JR (m + 1) d × Fin (m + 1) → ℝ),
      |lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W') ^ 2 - 1| ≤
          1 / (((m + 1 : ℕ) : ℝ)) →
      100 / 101 * DWr (m + 1) (JR (m + 1) d) ≤ radF53 W' ^ 2 →
      stdGauss (JR (m + 1) d × Fin (m + 1))
          (badSet86 (modRK m d t v E) (gqRK m d K t v E)
            (PU 2 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
              (1 / Real.sqrt (DD (m + 1) d)))
            (lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W'))) ≤
        ENNReal.ofReal (A0 + A1 * Ytil H U)) :
    stdGauss (CoefIdxD (m + 1) d) (SphereFail86 (m + 1) d 2 K t v f0 T) ≤
      ENNReal.ofReal (A0 + A1 * ((d : ℝ) + 1)) +
        ENNReal.ofReal (Ct / ((m + 1 : ℕ) : ℝ)) +
        ENNReal.ofReal (20808 / DWr (m + 1) (JR (m + 1) d)) := by
  classical
  set S : Set ((Fin (d + 1) × Fin (m + 1) → ℝ) × (JR (m + 1) d × Fin (m + 1) → ℝ)) :=
    {p | 1 / (((m + 1 : ℕ) : ℝ)) <
      |lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) p.1 (radF53 p.2) ^ 2 - 1|} with hS
  set S2 : Set (JR (m + 1) d × Fin (m + 1) → ℝ) :=
    {W' | radF53 W' ^ 2 < 100 / 101 * DWr (m + 1) (JR (m + 1) d)} with hS2
  have hS2m : MeasurableSet S2 :=
    measurableSet_lt ((BstLean.Part53.measurable_radF).pow_const 2) measurable_const
  set g : (Fin (d + 1) × Fin (m + 1) → ℝ) → ℝ := fun U => A0 + A1 * Ytil H U with hg
  have hgnn : ∀ U, 0 ≤ g U := fun U =>
    add_nonneg hA0 (mul_nonneg hA1 (Ytil_nonneg H U))
  have hgint : Integrable g (stdGauss (Fin (d + 1) × Fin (m + 1))) :=
    (integrable_const _).add ((Ytil_integrable H).const_mul A1)
  have hgmeas : Measurable g := measurable_const.add ((Ytil_measurable H).const_mul A1)
  have hgI : ∫ U, g U ∂stdGauss (Fin (d + 1) × Fin (m + 1)) ≤ A0 + A1 * ((d : ℝ) + 1) := by
    rw [hg, integral_add (integrable_const _) ((Ytil_integrable H).const_mul A1),
      integral_const_mul]
    have hc0 : ∫ _U : Fin (d + 1) × Fin (m + 1) → ℝ, A0
        ∂stdGauss (Fin (d + 1) × Fin (m + 1)) = A0 := by simp
    rw [hc0]
    have hY := Ytil_int (I := Fin (d + 1)) H
    rw [Fintype.card_fin] at hY
    push_cast at hY
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hY hA1)
  have hpt' : ∀ (U : Fin (d + 1) × Fin (m + 1) → ℝ) (W' : JR (m + 1) d × Fin (m + 1) → ℝ),
      stdGauss (JR (m + 1) d × Fin (m + 1))
          (badSet86 (modRK m d t v E) (gqRK m d K t v E)
            (PU 2 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
              (1 / Real.sqrt (DD (m + 1) d)))
            (lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W'))) ≤
        (ENNReal.ofReal (g U) + S2.indicator (fun _ => (1 : ℝ≥0∞)) W') +
          S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W') := by
    intro U W'
    by_cases h : (U, W') ∈ S
    · rw [Set.indicator_of_mem h]
      exact (prob_le_one).trans le_add_self
    by_cases h2 : W' ∈ S2
    · rw [Set.indicator_of_mem h2]
      exact (prob_le_one).trans (le_trans le_add_self le_self_add)
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h2, add_zero, add_zero]
      have h' : |lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W') ^ 2 - 1| ≤
          1 / (((m + 1 : ℕ) : ℝ)) := by
        simpa [hS, not_lt] using h
      have h2' : 100 / 101 * DWr (m + 1) (JR (m + 1) d) ≤ radF53 W' ^ 2 := by
        simpa [hS2, not_lt] using h2
      exact hpt U W' h' h2'
  refine (hPol t v ht hv E hE f0 T hT).trans ?_
  refine (lintegral_mono fun U => lintegral_mono fun W' => hpt' U W').trans ?_
  have e1 : ∀ U : Fin (d + 1) × Fin (m + 1) → ℝ, ∫⁻ W' : JR (m + 1) d × Fin (m + 1) → ℝ,
      ((ENNReal.ofReal (g U) + S2.indicator (fun _ => (1 : ℝ≥0∞)) W') +
        S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W'))
      ∂stdGauss (JR (m + 1) d × Fin (m + 1)) =
      (ENNReal.ofReal (g U) + stdGauss (JR (m + 1) d × Fin (m + 1)) S2) +
        ∫⁻ W' : JR (m + 1) d × Fin (m + 1) → ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (U, W')
          ∂stdGauss (JR (m + 1) d × Fin (m + 1)) := by
    intro U
    have hm1 : Measurable (fun W' : JR (m + 1) d × Fin (m + 1) → ℝ =>
        ENNReal.ofReal (g U) + S2.indicator (fun _ => (1 : ℝ≥0∞)) W') :=
      (Measurable.indicator (f := fun _ => (1 : ℝ≥0∞)) measurable_const hS2m).const_add _
    rw [lintegral_add_left hm1, lintegral_add_left measurable_const, lintegral_const,
      measure_univ, mul_one, lintegral_indicator hS2m]
    simp
  simp_rw [e1]
  have hm2 : Measurable (fun U : Fin (d + 1) × Fin (m + 1) → ℝ =>
      ENNReal.ofReal (g U) + stdGauss (JR (m + 1) d × Fin (m + 1)) S2) :=
    hgmeas.ennreal_ofReal.add measurable_const
  rw [lintegral_add_left hm2,
    lintegral_add_left hgmeas.ennreal_ofReal, lintegral_const, measure_univ, mul_one,
    ← ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall hgnn)]
  have hrad : stdGauss (JR (m + 1) d × Fin (m + 1)) S2 ≤
      ENNReal.ofReal (20808 / DWr (m + 1) (JR (m + 1) d)) :=
    rad_tail (JR (m + 1) d × Fin (m + 1)) hDW
  calc _ ≤ ENNReal.ofReal (A0 + A1 * ((d : ℝ) + 1)) +
        ENNReal.ofReal (20808 / DWr (m + 1) (JR (m + 1) d)) +
        ENNReal.ofReal (Ct / ((m + 1 : ℕ) : ℝ)) :=
        add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hgI) hrad) hTail
    _ = _ := by ring

end BstLean.Part89

#print axioms BstLean.Part89.failQ_core2
