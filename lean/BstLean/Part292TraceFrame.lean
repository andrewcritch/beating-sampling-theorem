import BstLean.Part292GatedChi
import BstLean.Part172Sig
import BstLean.Part167XF

/-! One-reflection coordinates keep the count independent of transverse energy. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part161 BstLean.Part172 BstLean.Part167

noncomputable def traceRow {n : ℕ} (u : Fin n → ℝ)
    (p : ℝ × (Fin (n-1) → ℝ)) : Fin n → ℝ := hhMat u *ᵥ consV p.1 p.2

theorem traceRow_measurable {n : ℕ} (u : Fin n → ℝ) : Measurable (traceRow u) :=
  (measurable_hh u).comp measurable_consV

theorem traceRow_distribution {n : ℕ} (hn : 1 ≤ n) (u : Fin n → ℝ) :
    ((gaussianReal 0 1).prod (stdGauss (Fin (n-1)))).map (traceRow u) =
      stdGauss (Fin n) := by
  change (((gaussianReal 0 1).prod (stdGauss (Fin (n-1)))).map
    ((fun z => hhMat u *ᵥ z) ∘ (fun p => consV p.1 p.2))) = _
  rw [← Measure.map_map (measurable_hh u) measurable_consV, consV_map hn, stdGauss_map_hh]

theorem gaussMat_one_rows (m d : ℕ) :
    gaussMat m d 1 = Measure.pi (fun _ : Fin m => stdGauss (Fin d)) := by
  rw [gaussMat_rows]
  simp only [sqrt_one, one_mul]
  change (Measure.pi (fun _ : Fin m => stdGauss (Fin d))).map id = _
  rw [Measure.map_id]

noncomputable def traceFrame {m n : ℕ} (γ : ℝ) (u : Fin n → ℝ)
    (p : (Fin m → ℝ) × Matrix (Fin m) (Fin (n-1)) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i => sqrt γ • traceRow u (p.1 i, p.2 i)

theorem traceFrame_measurable {m n : ℕ} (γ : ℝ) (u : Fin n → ℝ) :
    Measurable (traceFrame (m := m) γ u) := by
  change Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin (n-1) → ℝ) =>
    fun i => sqrt γ • traceRow u (p.1 i, p.2 i))
  apply measurable_pi_lambda
  intro i
  have hp : Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin (n-1) → ℝ) =>
      (p.1 i, p.2 i)) := by fun_prop
  have hr : Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin (n-1) → ℝ) =>
      traceRow u (p.1 i, p.2 i)) := (traceRow_measurable u).comp hp
  exact hr.const_smul (sqrt γ)

theorem traceFrame_distribution {m n : ℕ} (hn : 1 ≤ n) (γ : ℝ) (u : Fin n → ℝ) :
    ((stdGauss (Fin m)).prod (gaussMat m (n-1) 1)).map (traceFrame γ u) =
      gaussMat m n γ := by
  rw [gaussMat_one_rows]
  change (((stdGauss (Fin m)).prod (Measure.pi fun _ : Fin m => stdGauss (Fin (n-1)))).map
    (fun p : (Fin m → ℝ) × (Fin m → Fin (n-1) → ℝ) =>
      fun i => sqrt γ • traceRow u (p.1 i, p.2 i))) =
    (gaussMat m n γ : Measure (Fin m → Fin n → ℝ))
  let μ := (gaussianReal 0 1).prod (stdGauss (Fin (n-1)))
  let pair : ((Fin m → ℝ) × (Fin m → Fin (n-1) → ℝ)) →
      (Fin m → ℝ × (Fin (n-1) → ℝ)) := fun p i => (p.1 i,p.2 i)
  have hp : Measurable pair := by fun_prop
  have hpair : ((stdGauss (Fin m)).prod
      (Measure.pi fun _ : Fin m => stdGauss (Fin (n-1)))).map pair =
        Measure.pi (fun _ : Fin m => μ) := by
    exact (measurePreserving_arrowProdEquivProdArrow ℝ (Fin (n-1) → ℝ) (Fin m)
      (fun _ => gaussianReal 0 1) (fun _ => stdGauss (Fin (n-1)))).symm.map_eq
  let f : (Fin m → ℝ × (Fin (n-1) → ℝ)) → (Fin m → Fin n → ℝ) :=
    fun W i => traceRow u (W i)
  have hf : Measurable f := measurable_pi_iff.mpr fun i =>
    (traceRow_measurable u).comp (measurable_pi_apply i)
  have hrow : (Measure.pi (fun _ : Fin m => μ)).map f =
      Measure.pi (fun _ : Fin m => stdGauss (Fin n)) := by
    rw [Measure.pi_map_pi (fun _ => (traceRow_measurable u).aemeasurable)]
    simp only [μ, traceRow_distribution hn u]
  let scale : (Fin m → Fin n → ℝ) → (Fin m → Fin n → ℝ) :=
    fun G i => sqrt γ • G i
  have hscale : Measurable scale := by fun_prop
  have he : (fun p : (Fin m → ℝ) × (Fin m → Fin (n-1) → ℝ) =>
      fun i => sqrt γ • traceRow u (p.1 i,p.2 i)) = scale ∘ f ∘ pair := rfl
  rw [he, ← Measure.map_map hscale (hf.comp hp), ← Measure.map_map hf hp, hpair, hrow]
  exact (gaussMat_rows γ).symm

theorem traceRow_read {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1)
    (z : ℝ) (g : Fin (n-1) → ℝ) :
    sg_z u (traceRow u (z,g)) = z ∧ sg_phi2 u (traceRow u (z,g)) = normSq g := by
  have h := sg_Ha0 hn hu (traceRow u (z,g))
  have he : hhMat u *ᵥ traceRow u (z,g) = consV z g := by
    unfold traceRow
    rw [mulVec_mulVec, sg_hh_sq, one_mulVec]
  rw [he, consV_zero hn] at h
  refine ⟨h.symm, ?_⟩
  unfold sg_phi2 traceRow
  rw [hh_normSq, normSq_consV hn]
  change z^2+normSq g-(sg_z u (traceRow u (z,g)))^2 = normSq g
  rw [← h]
  ring

theorem traceFrame_energy_lower {m n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {γ : ℝ} (hγ : 0 < γ)
    (p : (Fin m → ℝ) × Matrix (Fin m) (Fin (n-1)) ℝ) :
    γ*activeEnergy p.1 p.2 ≤ ∑ i, sg_phi1 u (traceFrame γ u p i) := by
  rw [activeEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change γ*(if 0 < p.1 i then normSq (p.2 i) else 0) ≤
    sg_phi1 u (sqrt γ • traceRow u (p.1 i,p.2 i))
  rw [sg_phi1_smul (sqrt_pos.mpr hγ), sq_sqrt hγ.le]
  apply mul_le_mul_of_nonneg_left _ hγ.le
  unfold sg_phi1
  rw [(traceRow_read hn hu _ _).1, (traceRow_read hn hu _ _).2]
  split_ifs <;> first | rfl | exact normSq_nonneg _ | linarith

end BstLean.Part292
