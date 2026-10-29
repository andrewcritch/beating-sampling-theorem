import BstLean.Part152BM
import BstLean.Part29Index
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Part 152 (file `Tau`): the Prékopa–Leindler property of the standard Gaussian measure

Role: `delegations/statements/p152-spec.md`. For a weight `0 < s < 1`, a measure `μ` and a cost
`c`, `Tau s μ c` is the statement: for all measurable `U, V : X → [0, ∞]` with
`U(x)^s · V(y)^{1−s} ≤ exp(s(1 − s)·c(x, y))` for all `x`, `y`:
`(∫U dμ)^s · (∫V dμ)^{1−s} ≤ 1`.

* `tau_gauss1`: the standard Gaussian measure on `ℝ` has `Tau` with the cost `(x − y)²/2`
  (Prékopa–Leindler on the line, `pl_one`, with `h` the Gaussian density).
* `Tau.prod`: `Tau` tensorizes: the product measure has `Tau` with the sum of the costs.
* **`tau_stdGauss`**: the standard Gaussian measure on `ι → ℝ` has `Tau` with the cost
  `(Σ_i (x_i − y_i)²)/2`, for every `0 < s < 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part152

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)

/-- The Prékopa–Leindler property of a measure `μ` for the weight `s` and the cost `c`. -/
def Tau {X : Type*} [MeasurableSpace X] (s : ℝ) (μ : Measure X) (c : X → X → ℝ) : Prop :=
  ∀ U V : X → ℝ≥0∞, Measurable U → Measurable V →
    (∀ x y, U x ^ s * V y ^ (1 - s) ≤ ENNReal.ofReal (Real.exp (s * (1 - s) * c x y))) →
    (∫⁻ x, U x ∂μ) ^ s * (∫⁻ x, V x ∂μ) ^ (1 - s) ≤ 1

lemma phi_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp [gaussianPDFReal, neg_div]

/-- The identity of the Gaussian density that Prékopa–Leindler needs. -/
lemma phi_mix (s x y : ℝ) :
    gaussianPDFReal 0 1 x ^ s * gaussianPDFReal 0 1 y ^ (1 - s) *
      Real.exp (s * (1 - s) * ((x - y) ^ 2 / 2)) = gaussianPDFReal 0 1 (s * x + (1 - s) * y) := by
  have hC : 0 < (√(2 * Real.pi))⁻¹ := by positivity
  rw [phi_eq, phi_eq, phi_eq, Real.mul_rpow hC.le (Real.exp_pos _).le,
    Real.mul_rpow hC.le (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul]
  have e1 : (√(2 * Real.pi))⁻¹ ^ s * (√(2 * Real.pi))⁻¹ ^ (1 - s) = (√(2 * Real.pi))⁻¹ := by
    rw [← Real.rpow_add hC]
    simp
  calc (√(2 * Real.pi))⁻¹ ^ s * Real.exp (-(x ^ 2 / 2) * s) *
        ((√(2 * Real.pi))⁻¹ ^ (1 - s) * Real.exp (-(y ^ 2 / 2) * (1 - s))) *
        Real.exp (s * (1 - s) * ((x - y) ^ 2 / 2))
      = ((√(2 * Real.pi))⁻¹ ^ s * (√(2 * Real.pi))⁻¹ ^ (1 - s)) *
          (Real.exp (-(x ^ 2 / 2) * s) * Real.exp (-(y ^ 2 / 2) * (1 - s)) *
            Real.exp (s * (1 - s) * ((x - y) ^ 2 / 2))) := by ring
    _ = _ := by
        rw [e1, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- **The standard Gaussian measure on the line has the Prékopa–Leindler property.** -/
theorem tau_gauss1 {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tau s (gaussianReal 0 1) (fun x y => (x - y) ^ 2 / 2) := by
  have h1 : 0 < 1 - s := by linarith
  intro U V hU hV H
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hU,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hV]
  have Z : ∫⁻ x, ENNReal.ofReal (gaussianPDFReal 0 1 x) = 1 :=
    lintegral_gaussianPDF_eq_one 0 one_ne_zero
  rw [← Z]
  refine pl_one hs0 hs1 ((measurable_gaussianPDF 0 1).mul hU) ((measurable_gaussianPDF 0 1).mul hV)
    (measurable_gaussianPDFReal 0 1) (gaussianPDFReal_nonneg 0 1) fun x y => ?_
  have hx := gaussianPDFReal_nonneg 0 1 x
  have hy := gaussianPDFReal_nonneg 0 1 y
  simp only [Pi.mul_apply, gaussianPDF]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ENNReal.mul_rpow_of_nonneg _ _ h1.le,
    ENNReal.ofReal_rpow_of_nonneg hx hs0.le, ENNReal.ofReal_rpow_of_nonneg hy h1.le]
  calc ENNReal.ofReal (gaussianPDFReal 0 1 x ^ s) * U x ^ s *
        (ENNReal.ofReal (gaussianPDFReal 0 1 y ^ (1 - s)) * V y ^ (1 - s))
      = ENNReal.ofReal (gaussianPDFReal 0 1 x ^ s) *
          ENNReal.ofReal (gaussianPDFReal 0 1 y ^ (1 - s)) * (U x ^ s * V y ^ (1 - s)) := by ring
    _ ≤ ENNReal.ofReal (gaussianPDFReal 0 1 x ^ s) *
          ENNReal.ofReal (gaussianPDFReal 0 1 y ^ (1 - s)) *
          ENNReal.ofReal (Real.exp (s * (1 - s) * ((x - y) ^ 2 / 2))) :=
        mul_le_mul' le_rfl (H x y)
    _ = ENNReal.ofReal (gaussianPDFReal 0 1 (s * x + (1 - s) * y)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          phi_mix]

/-- **Tensorization.** -/
theorem Tau.prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] {c : X → X → ℝ}
    {d : Y → Y → ℝ} (hμ : Tau s μ c) (hν : Tau s ν d) :
    Tau s (μ.prod ν) (fun p q => c p.1 q.1 + d p.2 q.2) := by
  have h1 : 0 < 1 - s := by linarith
  intro U V hU hV H
  rw [lintegral_prod _ hU.aemeasurable, lintegral_prod _ hV.aemeasurable]
  refine hμ _ _ hU.lintegral_prod_right' hV.lintegral_prod_right' fun x y => ?_
  set k : ℝ := Real.exp (-(1 - s) * c x y) with hk
  have hk0 : 0 < k := Real.exp_pos _
  have R := hν (fun x2 => ENNReal.ofReal k * U (x, x2)) (fun y2 => V (y, y2))
    ((hU.comp measurable_prodMk_left).const_mul _) (hV.comp measurable_prodMk_left)
    (fun x2 y2 => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ENNReal.ofReal_rpow_of_nonneg hk0.le hs0.le]
      calc ENNReal.ofReal (k ^ s) * U (x, x2) ^ s * V (y, y2) ^ (1 - s)
          = ENNReal.ofReal (k ^ s) * (U (x, x2) ^ s * V (y, y2) ^ (1 - s)) := by ring
        _ ≤ ENNReal.ofReal (k ^ s) *
              ENNReal.ofReal (Real.exp (s * (1 - s) * (c x y + d x2 y2))) :=
            mul_le_mul' le_rfl (H (x, x2) (y, y2))
        _ = ENNReal.ofReal (Real.exp (s * (1 - s) * d x2 y2)) := by
            rw [← ENNReal.ofReal_mul (by positivity), hk, ← Real.exp_mul, ← Real.exp_add]
            congr 2
            ring)
  have eI : ∫⁻ x2, ENNReal.ofReal k * U (x, x2) ∂ν = ENNReal.ofReal k * ∫⁻ x2, U (x, x2) ∂ν :=
    lintegral_const_mul _ (hU.comp measurable_prodMk_left)
  rw [eI, ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ENNReal.ofReal_rpow_of_nonneg hk0.le hs0.le] at R
  have e : ENNReal.ofReal (Real.exp (s * (1 - s) * c x y)) * ENNReal.ofReal (k ^ s) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), hk, ← Real.exp_mul, ← Real.exp_add]
    have : s * (1 - s) * c x y + -(1 - s) * c x y * s = 0 := by ring
    rw [this, Real.exp_zero, ENNReal.ofReal_one]
  calc (∫⁻ y2, U (x, y2) ∂ν) ^ s * (∫⁻ y2, V (y, y2) ∂ν) ^ (1 - s)
      = ENNReal.ofReal (Real.exp (s * (1 - s) * c x y)) *
          (ENNReal.ofReal (k ^ s) * (∫⁻ y2, U (x, y2) ∂ν) ^ s *
            (∫⁻ y2, V (y, y2) ∂ν) ^ (1 - s)) := by
        rw [← mul_assoc, ← mul_assoc, e, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (s * (1 - s) * c x y)) * 1 := mul_le_mul' le_rfl R
    _ = _ := mul_one _

/-- Transport of the property along a measure-preserving map. -/
theorem Tau.map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {s : ℝ} {μ : Measure X}
    {ν : Measure Y} {c : Y → Y → ℝ} {e : X → Y} (he : MeasurePreserving e μ ν)
    (h : Tau s μ (fun x y => c (e x) (e y))) : Tau s ν c := by
  intro U V hU hV H
  rw [← he.lintegral_comp hU, ← he.lintegral_comp hV]
  exact h _ _ (hU.comp he.measurable) (hV.comp he.measurable) (fun x y => H _ _)

/-- The standard Gaussian measure on `Fin n → ℝ`. -/
theorem tau_fin {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    Tau s (stdGauss (Fin n)) (fun x y => (∑ i, (x i - y i) ^ 2) / 2) := by
  induction n with
  | zero =>
    intro U V hU hV H
    rw [lintegral_unique, lintegral_unique, measure_univ, mul_one, mul_one]
    have key : ∀ a b : Fin 0 → ℝ, U a ^ s * V b ^ (1 - s) ≤ 1 := fun a b => by
      have := H a b
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_div, mul_zero, Real.exp_zero,
        ENNReal.ofReal_one] at this
      exact this
    exact key _ _
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0).symm
    refine Tau.map (μ := (gaussianReal 0 1).prod (stdGauss (Fin n))) hp ?_
    have T := Tau.prod hs0 hs1 (tau_gauss1 hs0 hs1) ih
    convert T using 1
    funext p q
    rw [Fin.sum_univ_succ]
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, add_div]

/-- **The standard Gaussian measure on `ι → ℝ` has the Prékopa–Leindler property** with the cost
`(Σ_i (x_i − y_i)²)/2`. -/
theorem tau_stdGauss {ι : Type} [Fintype ι] {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tau s (stdGauss ι) (fun x y => (∑ i, (x i - y i) ^ 2) / 2) := by
  classical
  set f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hf
  have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) f)
      (stdGauss (Fin (Fintype.card ι))) (stdGauss ι) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) f
  refine Tau.map hp ?_
  have hk : ∀ (Z : Fin (Fintype.card ι) → ℝ) (i : ι),
      (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) f) Z i = Z (f.symm i) := by
    intro Z i
    obtain ⟨j, rfl⟩ := f.surjective i
    rw [Equiv.symm_apply_apply]
    exact Equiv.piCongrLeft_apply_apply (P := fun _ : ι => ℝ) f Z j
  have T := tau_fin hs0 hs1 (Fintype.card ι)
  convert T using 1
  funext x y
  simp only [hk]
  rw [Equiv.sum_comp f.symm (fun j => (x j - y j) ^ 2)]

end BstLean.Part152

open BstLean.Part152 in
#print axioms tau_stdGauss
