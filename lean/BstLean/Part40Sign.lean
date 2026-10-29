import BstLean.Part40Defs
import BstLean.Part37Density

/-!
# Part 40, wave 1: every diagonal Bingham law is sign-symmetric

Paper: Setting and Lemma `A` (last sentence). Specification: `delegations/answers/p40-spec-opus.md`.
Do not use `native_decide` or `axiom` anywhere.

Suggested route: `uniformSphere n` is invariant under `flipAt i` (a linear isometry of
`EuclideanSpace`; compare the sign-flip facts used for `uniformSphere_parity` in `Part29Sphere`),
and `qth θ ∘ flipAt i = qth θ`, so the density of `bingham n θ` is invariant. Probability and the
sphere support follow from `uniformSphere_isProbability`, `uniformSphere_ae_sphere` and
`Part37Law.Zth_pos`.
-/

namespace BstLean.Part40

open MeasureTheory
open scoped Pointwise ENNReal
open BstLean.Part37 (bingham)

variable {n : ℕ}

private noncomputable def reflection (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

private lemma reflection_apply (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp (reflection i x) = flipAt i (WithLp.ofLp x) := by
  classical
  ext j
  change (if j = i then LinearIsometryEquiv.neg ℝ else
    LinearIsometryEquiv.refl ℝ ℝ) (x j) = if j = i then -x j else x j
  split_ifs <;> rfl

private lemma flip_invol (i : Fin n) (x : Fin n → ℝ) : flipAt i (flipAt i x) = x := by
  ext j
  by_cases h : j = i <;> simp [flipAt, h]

private lemma measurable_flip (i : Fin n) : Measurable (flipAt i) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j = i <;> simp only [flipAt, h, ite_true, ite_false] <;> fun_prop

private lemma uniform_flip (i : Fin n) :
    (BstLean.Part29.uniformSphere n).map (flipAt i) = BstLean.Part29.uniformSphere n := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let u : Metric.sphere (0 : E) 1 → (Fin n → ℝ) := fun x => WithLp.ofLp x.1
  have hu : Measurable u := by dsimp [u, E]; fun_prop
  have hf : Measurable (flipAt i) := measurable_flip i
  have he := (reflection i).measurePreserving
  have hinv (x : E) : reflection i (reflection i x) = x := by
    apply WithLp.ofLp_injective 2
    simp only [reflection_apply, flip_invol]
  have hcone (s : Set (Fin n → ℝ)) :
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' (flipAt i ⁻¹' s))) =
      reflection i ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' s))) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨r, hr, reflection i z.1, ?_, ?_⟩
      · refine ⟨⟨reflection i z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, reflection_apply] using hz
      · exact ((reflection i).map_smul r z.1).symm
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hy⟩
      refine ⟨r, hr, reflection i z.1, ?_, ?_⟩
      · refine ⟨⟨reflection i z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, reflection_apply, flip_invol] using hz
      · have hh := congrArg (reflection i) hy
        simpa only [LinearIsometryEquiv.map_smul, hinv] using hh
  apply Measure.ext
  intro s hs
  change ((((volume : Measure E).toSphere Set.univ)⁻¹ •
      ((volume : Measure E).toSphere.map u)).map (flipAt i)) s =
    (((volume : Measure E).toSphere Set.univ)⁻¹ •
      ((volume : Measure E).toSphere.map u)) s
  rw [Measure.map_smul _ hf.aemeasurable]
  rw [Measure.map_map hf hu]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.map_apply (hf.comp hu) hs, Measure.map_apply hu hs]
  rw [Set.preimage_comp]
  rw [Measure.toSphere_apply' _ (hu (hf hs)), Measure.toSphere_apply' _ (hu hs), hcone]
  congr 1
  exact he.measure_preimage_emb (reflection i).toHomeomorph.measurableEmbedding _

/-- `D(θ)` is a sign-symmetric law on the sphere, for every `θ`. -/
theorem bingham_signSym (hn : 1 ≤ n) (θ : Fin n → ℝ) : SignSym n (bingham n θ) := by
  classical
  refine ⟨⟨BstLean.Part37.bingham_isProb hn θ,
    BstLean.Part37.bingham_ae_sphere θ⟩, ?_⟩
  intro i
  have hf : Measurable (flipAt i) := measurable_flip i
  have hq (x : Fin n → ℝ) : BstLean.Part37.qth θ (flipAt i x) =
      BstLean.Part37.qth θ x := by
    unfold BstLean.Part37.qth
    apply Finset.sum_congr rfl
    intro j _
    simp [flipAt]
  let w : (Fin n → ℝ) → ENNReal := fun x =>
    ENNReal.ofReal (Real.exp (BstLean.Part37.qth θ x) / BstLean.Part37.Zth n θ)
  have hw : Measurable w := by unfold w BstLean.Part37.qth; fun_prop
  have hp : MeasurePreserving (flipAt i) (BstLean.Part29.uniformSphere n)
      (BstLean.Part29.uniformSphere n) := ⟨hf, uniform_flip i⟩
  apply Measure.ext
  intro s hs
  change ((BstLean.Part29.uniformSphere n).withDensity w).map (flipAt i) s =
    (BstLean.Part29.uniformSphere n).withDensity w s
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hf hs), ← lintegral_indicator hs]
  have h := hp.lintegral_comp (hw.indicator hs)
  rw [← h]
  apply lintegral_congr
  intro x
  simp only [Set.indicator_apply, Set.mem_preimage, w, hq]

end BstLean.Part40

#print axioms BstLean.Part40.bingham_signSym
