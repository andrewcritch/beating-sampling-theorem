import BstLean.Part56MomProg_Integrals

/-! Directional moments of the uniform sphere. -/

namespace BstLean.Part56.MomProg

open MeasureTheory
open scoped Pointwise
open BstLean.Part56
open BstLean.Part29 (uniformSphere)

variable {n : ℕ}

theorem uniformSphere_involution
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hR : ∀ x, R (R x) = x) :
    (uniformSphere n).map (fun x => WithLp.ofLp (R (WithLp.toLp 2 x))) = uniformSphere n := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let u : Metric.sphere (0 : E) 1 → (Fin n → ℝ) := fun x => WithLp.ofLp x.1
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun x => WithLp.ofLp (R (WithLp.toLp 2 x))
  have hu : Measurable u := by dsimp [u, E]; fun_prop
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hFu (z : E) : F (WithLp.ofLp z) = WithLp.ofLp (R z) := rfl
  have hcone (s : Set (Fin n → ℝ)) :
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' (F ⁻¹' s))) =
      R ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' s))) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨r, hr, R z.1, ?_, ?_⟩
      · refine ⟨⟨R z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, hFu] using hz
      · exact (R.map_smul r z.1).symm
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hy⟩
      refine ⟨r, hr, R z.1, ?_, ?_⟩
      · refine ⟨⟨R z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, hFu, hR] using hz
      · have hh := congrArg R hy
        simpa only [LinearIsometryEquiv.map_smul, hR] using hh
  apply Measure.ext
  intro s hs
  change ((((volume : Measure E).toSphere Set.univ)⁻¹ •
      ((volume : Measure E).toSphere.map u)).map F) s =
    (((volume : Measure E).toSphere Set.univ)⁻¹ •
      ((volume : Measure E).toSphere.map u)) s
  rw [Measure.map_smul _ hF.aemeasurable, Measure.map_map hF hu]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.map_apply (hF.comp hu) hs, Measure.map_apply hu hs, Set.preimage_comp]
  rw [Measure.toSphere_apply' _ (hu (hF hs)), Measure.toSphere_apply' _ (hu hs), hcone]
  congr 1
  exact R.measurePreserving.measure_preimage_emb R.toHomeomorph.measurableEmbedding _

theorem sphere_directional_moment (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (m : ℕ) :
    (∫ x, (∑ i, v i * x i) ^ (2 * m) ∂uniformSphere n) =
      BstLean.Part29.gaussMom (2 * m) / BstLean.Part36.rhoD n m := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let V : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single a 1
  have hV : ‖V‖ = 1 := by
    have h : ‖V‖ ^ 2 = 1 := by simpa [V, EuclideanSpace.real_norm_sq_eq, UnitV] using hv
    nlinarith [norm_nonneg V]
  have he : ‖e‖ = 1 := by simp [e]
  let R := (ℝ ∙ (V - e))ᗮ.reflection
  have hRV : R V = e := Submodule.reflection_sub (hV.trans he.symm)
  have hRR (x) : R (R x) = x := by
    exact R.symm_apply_apply x
  have hcoord (x : Fin n → ℝ) :
      (WithLp.ofLp (R (WithLp.toLp 2 x))) a = ∑ i, v i * x i := by
    have h := R.inner_map_map V (WithLp.toLp 2 x)
    rw [hRV] at h
    simpa [e, V, PiLp.inner_apply, mul_comm] using h
  have hm := uniformSphere_involution R hRR
  have hi : (∫ x, x a ^ (2 * m) ∂uniformSphere n) =
      ∫ x, (∑ i, v i * x i) ^ (2 * m) ∂uniformSphere n := by
    conv_lhs => rw [← hm]
    rw [integral_map (by fun_prop)
      ((by fun_prop : Continuous (fun x : Fin n → ℝ => x a ^ (2 * m))).aestronglyMeasurable)]
    simp only [hcoord]
  rw [← hi]
  let s : Multiset (Fin n) := Multiset.replicate (2 * m) a
  have hs := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (2 * m) hn) s (by simp [s])).2
  have hmon (x : Fin n → ℝ) : BstLean.Part36.monoVal x s = x a ^ (2 * m) := by
    simp [s, BstLean.Part36.monoVal]
  have hgp : BstLean.Part36.gpm s = BstLean.Part29.gaussMom (2 * m) := by
    unfold BstLean.Part36.gpm
    rw [Finset.prod_eq_single a]
    · simp [s]
    · intro b _ hb
      simp [s, Multiset.count_replicate, Ne.symm hb, BstLean.Part29.gaussMom]
    · simp
  simpa only [hmon, hgp, show s.card / 2 = m by simp [s]] using hs

end BstLean.Part56.MomProg
