import BstLean.Part221PlaneOperator
import BstLean.Part221GateIntegral
import BstLean.Part209Active

/-! The actual gated-plane moment from the independent gate array and its count. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part167 BstLean.Part209
open BstLean.Part151 (mask)

noncomputable def planeRows (m : ℕ) : Measure (Fin m → Fin 2 → ℝ) :=
  Measure.pi fun _ : Fin m => stdGauss (Fin 2)

instance (m : ℕ) : IsProbabilityMeasure (planeRows m) := by
  unfold planeRows; infer_instance

lemma planeRows_gaussMat (m : ℕ) : planeRows m = gaussMat m 2 1 := by
  change (Measure.pi (fun _ : Fin m => stdGauss (Fin 2)) :
    Measure (Matrix (Fin m) (Fin 2) ℝ)) = gaussMat m 2 1
  have h := BstLean.Part148.gaussMat_rows_map m 2 1
  change (gaussMat m 2 1).map
    (id : (Fin m → Fin 2 → ℝ) → (Fin m → Fin 2 → ℝ)) = _ at h
  simp only [Real.sqrt_one, one_smul] at h
  change (gaussMat m 2 1).map id =
    Measure.pi (fun _ : Fin m => (stdGauss (Fin 2)).map id) at h
  simp only [Measure.map_id] at h
  exact h.symm

lemma plane_coordinates_map (m : ℕ) :
    (planeRows m).map (fun Z => ((fun i => Z i 0), (fun i => Z i 1))) =
      (stdGauss (Fin m)).prod (stdGauss (Fin m)) := by
  have hrow : (stdGauss (Fin 2)).map (fun z => (z 0, z 1)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) :=
    (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)
  have he : (fun Z : Fin m → Fin 2 → ℝ => ((fun i => Z i 0), (fun i => Z i 1))) =
      e ∘ (fun Z => fun i => (Z i 0, Z i 1)) := rfl
  have hm : Measurable (fun Z : Fin m → Fin 2 → ℝ => fun i => (Z i 0, Z i 1)) := by
    fun_prop
  rw [he, ← Measure.map_map e.measurable hm]
  unfold planeRows
  rw [Measure.pi_map_pi (fun _ => (show Measurable (fun z : Fin 2 → ℝ => (z 0, z 1)) by
    fun_prop).aemeasurable)]
  simp_rw [hrow]
  exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).map_eq

lemma plane_first_map (m : ℕ) :
    (planeRows m).map (fun Z => fun i => Z i 0) = stdGauss (Fin m) := by
  unfold planeRows
  rw [Measure.pi_map_pi (fun _ => (measurable_pi_apply 0).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) 0).map_eq

noncomputable def outerPlaneEigen {m : ℕ} (b : Fin m → Bool)
    (Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  eigenTwo (∑ i, if b i then Q i 0 0 else 0)
    (∑ i, if b i then Q i 0 1 else 0) (∑ i, if b i then Q i 1 1 else 0)

lemma outerPlaneEigen_selected {m : ℕ} (b : Fin m → Bool) (Z : Fin m → Fin 2 → ℝ) :
    outerPlaneEigen b (fun i => outerProduct (Z i)) =
      matrixPlaneEigen (Matrix.diagonal (fun i => if b i then (1 : ℝ) else 0) * Matrix.of Z) := by
  unfold outerPlaneEigen matrixPlaneEigen
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    cases hb : b i <;> simp [outerProduct, Matrix.diagonal_mul, sq, hb]

lemma halfGate_first (z : Fin 2 → ℝ) :
    halfGate ![1, 0] z = (if 0 < z 0 then true else false) := by
  simp [halfGate, dotProduct, Fin.sum_univ_two]

lemma outerPlaneEigen_gated {m : ℕ} (Z : Fin m → Fin 2 → ℝ) :
    outerPlaneEigen (fun i => halfGate ![1,0] (Z i)) (fun i => outerProduct (Z i)) =
      planeEigen (fun i => Z i 0) (fun i => Z i 1) := by
  unfold outerPlaneEigen planeEigen L11 L12 L22
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    simp only [halfGate_first, outerProduct] <;>
    by_cases h : 0 < Z i 0 <;> simp [h, mask, sq]

lemma measurable_outerPlaneEigen {m : ℕ} :
    Measurable (fun z : (Fin m → Bool) × (Fin m → Matrix (Fin 2) (Fin 2) ℝ) =>
      outerPlaneEigen z.1 z.2) := by
  unfold outerPlaneEigen eigenTwo
  have ht (a b : Fin 2) : Measurable
      (fun z : (Fin m → Bool) × (Fin m → Matrix (Fin 2) (Fin 2) ℝ) =>
        ∑ i, if z.1 i then z.2 i a b else 0) := by
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite
    · exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst) measurable_const
    · fun_prop
    · exact measurable_const
  exact ((ht 0 0 |>.add (ht 1 1)).add
    ((((ht 0 0).sub (ht 1 1)).pow_const 2).add ((ht 0 1).pow_const 2 |>.const_mul 4)).sqrt).div_const 2

end BstLean.Part221
