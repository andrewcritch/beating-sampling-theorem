import BstLean.Part86Core
import BstLean.Part86Tail
import BstLean.Part89Defs

/-!
# Part 89, the failure bound with a sphere-step bound that depends on the anchors

* `Ytil H U = Σ_j ‖H U_j‖² / ‖H‖_F²`, with `E Ỹ ≤ card I` (`Ytil_int`).
* `failQ_core`: polar reduction, the sphere step in the scale window and on the radius event
  `ρ² ≥ (100/101) D_W` with a bound affine in `Ỹ(U)`, the scale tail, and the radius tail.

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

/-- `Ỹ(U) = Σ_j ‖H U_j‖² / ‖H‖_F²` (`0` if `H = 0`). -/
noncomputable def Ytil {n : ℕ} {I : Type} [Fintype I] (H : Matrix (Fin n) (Fin n) ℝ)
    (U : I × Fin n → ℝ) : ℝ :=
  (∑ j : I, BstLean.Part78.nsq (fun i => ∑ l, H i l * U (j, l))) / BstLean.Part78.frobH H

section ytil

variable {n : ℕ} {I : Type} [Fintype I]

theorem frobH_nonneg (H : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ BstLean.Part78.frobH H := by
  unfold BstLean.Part78.frobH
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem Ytil_nonneg (H : Matrix (Fin n) (Fin n) ℝ) (U : I × Fin n → ℝ) : 0 ≤ Ytil H U := by
  unfold Ytil
  refine div_nonneg (Finset.sum_nonneg fun j _ => ?_) (frobH_nonneg H)
  unfold BstLean.Part78.nsq
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem Ytil_continuous (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun U : I × Fin n → ℝ => Ytil H U) := by
  unfold Ytil BstLean.Part78.nsq
  fun_prop

theorem Ytil_measurable (H : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun U : I × Fin n → ℝ => Ytil H U) := (Ytil_continuous H).measurable

/-- The linear form `(H U_j)_i` as a linear form in all coordinates of `U`. -/
theorem lin_eq [DecidableEq I] (H : Matrix (Fin n) (Fin n) ℝ) (j : I) (i : Fin n) (U : I × Fin n → ℝ) :
    ∑ l, H i l * U (j, l) =
      ∑ α : I × Fin n, (if α.1 = j then H i α.2 else 0) * U α := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem coef_sq [DecidableEq I] (H : Matrix (Fin n) (Fin n) ℝ) (j : I) (i : Fin n) :
    ∑ α : I × Fin n, (if α.1 = j then H i α.2 else 0) * (if α.1 = j then H i α.2 else 0) =
      ∑ l, H i l ^ 2 := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
  · simp [sq]
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem term_int (H : Matrix (Fin n) (Fin n) ℝ) (j : I) (i : Fin n) :
    Integrable (fun U : I × Fin n → ℝ => (∑ l, H i l * U (j, l)) ^ 2) (stdGauss (I × Fin n)) ∧
      ∫ U : I × Fin n → ℝ, (∑ l, H i l * U (j, l)) ^ 2 ∂stdGauss (I × Fin n) =
        ∑ l, H i l ^ 2 := by
  classical
  have h := BstLean.Part78.gaussLin (I × Fin n)
    (fun α : I × Fin n => if α.1 = j then H i α.2 else 0)
    (fun α : I × Fin n => if α.1 = j then H i α.2 else 0)
  have hf : (fun U : I × Fin n → ℝ => (∑ l, H i l * U (j, l)) ^ 2) =
      fun U => (∑ α : I × Fin n, (if α.1 = j then H i α.2 else 0) * U α) *
        (∑ α : I × Fin n, (if α.1 = j then H i α.2 else 0) * U α) := by
    funext U; rw [lin_eq H j i U, sq]
  rw [hf]
  exact ⟨h.1, h.2.trans (coef_sq H j i)⟩

theorem num_int (H : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun U : I × Fin n → ℝ =>
        ∑ j : I, BstLean.Part78.nsq (fun i => ∑ l, H i l * U (j, l))) (stdGauss (I × Fin n)) ∧
      ∫ U : I × Fin n → ℝ, ∑ j : I, BstLean.Part78.nsq (fun i => ∑ l, H i l * U (j, l))
          ∂stdGauss (I × Fin n) = (Fintype.card I : ℝ) * BstLean.Part78.frobH H := by
  unfold BstLean.Part78.nsq
  have hi : ∀ j : I, Integrable (fun U : I × Fin n → ℝ => ∑ i, (∑ l, H i l * U (j, l)) ^ 2)
      (stdGauss (I × Fin n)) := fun j => integrable_finsetSum _ fun i _ => (term_int H j i).1
  refine ⟨integrable_finsetSum _ fun j _ => hi j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hi j]
  have : ∀ j : I, ∫ U : I × Fin n → ℝ, ∑ i, (∑ l, H i l * U (j, l)) ^ 2 ∂stdGauss (I × Fin n) =
      BstLean.Part78.frobH H := by
    intro j
    rw [integral_finsetSum _ fun i _ => (term_int H j i).1]
    unfold BstLean.Part78.frobH
    exact Finset.sum_congr rfl fun i _ => (term_int H j i).2
  simp [this]

theorem Ytil_integrable (H : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun U : I × Fin n → ℝ => Ytil H U) (stdGauss (I × Fin n)) := by
  unfold Ytil
  exact (num_int H).1.div_const _

/-- `E Ỹ = card I` if `H ≠ 0`. -/
theorem Ytil_int_eq (H : Matrix (Fin n) (Fin n) ℝ) (hH : BstLean.Part78.frobH H ≠ 0) :
    ∫ U : I × Fin n → ℝ, Ytil H U ∂stdGauss (I × Fin n) = (Fintype.card I : ℝ) := by
  unfold Ytil
  rw [integral_div, (num_int H).2, mul_div_assoc, div_self hH, mul_one]

/-- `E Ỹ = 0` if `‖H‖_F = 0`. -/
theorem Ytil_int_zero (H : Matrix (Fin n) (Fin n) ℝ) (hH : BstLean.Part78.frobH H = 0) :
    ∫ U : I × Fin n → ℝ, Ytil H U ∂stdGauss (I × Fin n) = 0 := by
  unfold Ytil
  simp [hH]

theorem Ytil_int (H : Matrix (Fin n) (Fin n) ℝ) :
    ∫ U : I × Fin n → ℝ, Ytil H U ∂stdGauss (I × Fin n) ≤ (Fintype.card I : ℝ) := by
  by_cases hH : BstLean.Part78.frobH H = 0
  · rw [Ytil_int_zero H hH]; positivity
  · exact (Ytil_int_eq H hH).le

end ytil

/-- `remezBound89` is affine in `cV`. -/
theorem remezBound89_affine (n k : ℕ) (c1 cVa cVb efl a b y : ℝ) :
    remezBound89 n k c1 (cVa + cVb * y) efl a b =
      remezBound89 n k c1 cVa efl a b +
        5 / 2 * (2 * (k : ℝ) + 1) ^ 2 * cVb / ((1 - b) ^ 2 * (1 - efl) ^ 2 * n) * y := by
  unfold remezBound89
  ring

/-- The radius tail: `P(ρ² < (100/101) D) ≤ 20808 / D`. -/
theorem rad_tail (ι : Type) [Fintype ι] (hD : 0 < (Fintype.card ι : ℝ)) :
    stdGauss ι {W : ι → ℝ | radF53 W ^ 2 < 100 / 101 * (Fintype.card ι : ℝ)} ≤
      ENNReal.ofReal (20808 / (Fintype.card ι : ℝ)) := by
  have h := chi_tail_gen ι ((Fintype.card ι : ℝ) / 102) (by positivity)
  have he : 2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) / 102) ^ 2 =
      20808 / (Fintype.card ι : ℝ) := by
    field_simp; ring
  rw [he] at h
  refine le_trans (measure_mono ?_) h
  intro W hW
  simp only [Set.mem_ofPred_eq] at hW ⊢
  have hρ : radF53 W ^ 2 = ∑ β, W β ^ 2 := by
    unfold radF53; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [hρ] at hW
  rw [abs_sub_comm, lt_abs]
  left
  linarith

/-- **The failure bound from the interfaces, with a sphere-step bound affine in `Ỹ(U)`.** -/
theorem failQ_core (m d K : ℕ) (Ct c1 cVa cVb efl a b : ℝ) (t : ℝ) (v : Fin (m + 1) → ℝ)
    (ht : 0 ≤ t) (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (hE : RotE v E)
    (hPol : PolarRed86 m d 2 K) (hTail : TailIface86 (m + 1) d Ct)
    (f0 : ℝ) (T : Tens (m + 1)) (hT : TSymm 2 T) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hc1 : 0 ≤ c1) (hcVa : 0 ≤ cVa) (hcVb : 0 ≤ cVb) (ha : 0 < a) (hb : b < 1) (hefl : efl < 1)
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
        ENNReal.ofReal (remezBound89 (m + 1) 2 c1 (cVa + cVb * Ytil H U) efl a b)) :
    stdGauss (CoefIdxD (m + 1) d) (SphereFail86 (m + 1) d 2 K t v f0 T) ≤
      ENNReal.ofReal (remezBound89 (m + 1) 2 c1 (cVa + cVb * ((d : ℝ) + 1)) efl a b) +
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
  set g : (Fin (d + 1) × Fin (m + 1) → ℝ) → ℝ :=
    fun U => remezBound89 (m + 1) 2 c1 (cVa + cVb * Ytil H U) efl a b with hg
  set C1 : ℝ := 5 / 2 * (2 * ((2 : ℕ) : ℝ) + 1) ^ 2 * cVb /
    ((1 - b) ^ 2 * (1 - efl) ^ 2 * ((m + 1 : ℕ) : ℝ)) with hC1
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  have hgaff : ∀ U, g U = remezBound89 (m + 1) 2 c1 cVa efl a b + C1 * Ytil H U := fun U =>
    remezBound89_affine (m + 1) 2 c1 cVa cVb efl a b (Ytil H U)
  have hg0nn : 0 ≤ remezBound89 (m + 1) 2 c1 cVa efl a b := by
    unfold remezBound89; positivity
  have hgnn : ∀ U, 0 ≤ g U := fun U => by
    rw [hgaff U]; exact add_nonneg hg0nn (mul_nonneg hC1nn (Ytil_nonneg H U))
  have hgint : Integrable g (stdGauss (Fin (d + 1) × Fin (m + 1))) := by
    have : g = fun U => remezBound89 (m + 1) 2 c1 cVa efl a b + C1 * Ytil H U := funext hgaff
    rw [this]
    exact (integrable_const _).add ((Ytil_integrable H).const_mul C1)
  have hgmeas : Measurable g := by
    have : g = fun U => remezBound89 (m + 1) 2 c1 cVa efl a b + C1 * Ytil H U := funext hgaff
    rw [this]
    exact measurable_const.add ((Ytil_measurable H).const_mul C1)
  have hgI : ∫ U, g U ∂stdGauss (Fin (d + 1) × Fin (m + 1)) ≤
      remezBound89 (m + 1) 2 c1 (cVa + cVb * ((d : ℝ) + 1)) efl a b := by
    have : g = fun U => remezBound89 (m + 1) 2 c1 cVa efl a b + C1 * Ytil H U := funext hgaff
    rw [remezBound89_affine, this, integral_add (integrable_const _)
      ((Ytil_integrable H).const_mul C1), integral_const_mul]
    have hc0 : ∫ _U : Fin (d + 1) × Fin (m + 1) → ℝ, remezBound89 (m + 1) 2 c1 cVa efl a b
        ∂stdGauss (Fin (d + 1) × Fin (m + 1)) = remezBound89 (m + 1) 2 c1 cVa efl a b := by simp
    rw [hc0]
    have hY := Ytil_int (I := Fin (d + 1)) H
    rw [Fintype.card_fin] at hY
    push_cast at hY
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hY hC1nn)
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
  calc _ ≤ ENNReal.ofReal (remezBound89 (m + 1) 2 c1 (cVa + cVb * ((d : ℝ) + 1)) efl a b) +
        ENNReal.ofReal (20808 / DWr (m + 1) (JR (m + 1) d)) +
        ENNReal.ofReal (Ct / ((m + 1 : ℕ) : ℝ)) :=
        add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hgI) hrad) hTail
    _ = _ := by ring

end BstLean.Part89

#print axioms BstLean.Part89.Ytil_nonneg
#print axioms BstLean.Part89.Ytil_measurable
#print axioms BstLean.Part89.Ytil_integrable
#print axioms BstLean.Part89.Ytil_int_eq
#print axioms BstLean.Part89.Ytil_int
#print axioms BstLean.Part89.failQ_core
