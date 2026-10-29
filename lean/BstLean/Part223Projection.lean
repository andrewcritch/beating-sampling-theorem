import BstLean.Part223Energy
import BstLean.Part172Grad

/-! The transverse replacement kernel is a function of the original matrix. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part170 BstLean.Part202
open BstLean.Part134 (res)
open BstLean.Part167 (perp perp_res perp_plane perp_smul)
open BstLean.Part172 (gr_perp_orth gr_perp_of_orth)

lemma perp_add' {d : ℕ} (b x y : Fin d → ℝ) :
    perp b (x + y) = perp b x + perp b y := by
  unfold perp
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, add_smul]
  abel

noncomputable def transverseProjection {d : ℕ} (h g z : Fin d → ℝ) : Fin d → ℝ :=
  perp h (perp (res h g) z)

lemma transverseProjection_idempotent {d : ℕ} (h g z : Fin d → ℝ) :
    transverseProjection h g (transverseProjection h g z) = transverseProjection h g z := by
  have hr : perp (res h g) (perp h (perp (res h g) z)) = perp h (perp (res h g) z) := by
    apply gr_perp_of_orth
    change perp h (perp (res h g) z) ⬝ᵥ res h g = 0
    rw [perp_dot, perp_res]
    exact gr_perp_orth _ _
  unfold transverseProjection
  rw [hr]
  exact gr_perp_of_orth (gr_perp_orth _ _)

lemma transverseProjection_h {d : ℕ} (h g : Fin d → ℝ) :
    transverseProjection h g h = 0 := by
  have hr : perp (res h g) h = h := by
    apply gr_perp_of_orth
    have he := gr_perp_orth h g
    rw [perp_eq_res] at he
    simpa only [mul_comm] using he
  rw [transverseProjection, hr, perp_self]

lemma transverseProjection_res {d : ℕ} (h g : Fin d → ℝ) :
    transverseProjection h g (res h g) = 0 := by
  rw [transverseProjection, perp_self]
  simp [perp]

lemma transverseProjection_add {d : ℕ} (h g x y : Fin d → ℝ) :
    transverseProjection h g (x + y) =
      transverseProjection h g x + transverseProjection h g y := by
  simp only [transverseProjection, perp_add']

lemma transverseProjection_smul {d : ℕ} (h g z : Fin d → ℝ) (t : ℝ) :
    transverseProjection h g (t • z) = t • transverseProjection h g z := by
  simp only [transverseProjection, perp_smul]

lemma planeAssemble_eq {d : ℕ} (h g : Fin d → ℝ)
    (ξ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (η : Fin d → ℝ) :
    planeAssemble h g (ξ, η) =
      (planeCoefficient h ξ.1 • h + planeCoefficient (res h g) ξ.2 • res h g) +
        transverseProjection h g η := by
  rw [planeAssemble, perp_plane, add_assoc]
  rfl

noncomputable def replaceTransverse {d : ℕ} (h g z η : Fin d → ℝ) : Fin d → ℝ :=
  z - transverseProjection h g z + transverseProjection h g η

/-- Replacing transverse coordinates leaves the retained plane unchanged, also at zero directions. -/
theorem replaceTransverse_assembled {d : ℕ} (h g : Fin d → ℝ)
    (ξ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (η η' : Fin d → ℝ) :
    replaceTransverse h g (planeAssemble h g (ξ, η)) η' = planeAssemble h g (ξ, η') := by
  simp only [replaceTransverse, planeAssemble_eq, transverseProjection_add,
    transverseProjection_smul, transverseProjection_h, transverseProjection_res,
    transverseProjection_idempotent, smul_zero, zero_add]
  abel

lemma continuous_replaceTransverse {d : ℕ} (h g : Fin d → ℝ) :
    Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => replaceTransverse h g p.1 p.2) := by
  have hP : Continuous (transverseProjection h g) :=
    (continuous_perp h).comp (continuous_perp (res h g))
  exact (continuous_fst.sub (hP.comp continuous_fst)).add (hP.comp continuous_snd)

#print axioms replaceTransverse_assembled
end BstLean.Part223
