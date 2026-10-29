import BstLean.Part53Polar
import BstLean.Part50Laws
import BstLean.Part46CharFn_Spectral
import BstLean.Part56PropD_Kernel

/-! Gaussian direction and sphere measure for the Bingham polar decomposition. -/
namespace BstLean.Part56

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part53 (unitF53 Wrad53)

/-- Normalizing a standard Gaussian gives the project's uniform sphere law. -/
theorem uniformSphere_lintegral_gauss (n : ℕ) (hn : 1 ≤ n)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂uniformSphere n) = ∫⁻ g, F (unitF53 g) ∂stdGauss (Fin n) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let σ := (volume : Measure E).toSphere
  let ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let W := ∫⁻ r : Set.Ioi (0 : ℝ), Wrad53 (Fin n) r.1 ∂ν
  have hW : Measurable (fun r : Set.Ioi (0 : ℝ) => Wrad53 (Fin n) r.1) := by
    unfold Wrad53
    fun_prop
  have hcoe : Measurable (fun s : Metric.sphere (0 : E) 1 => WithLp.ofLp s.1) := by
    dsimp only [E]
    fun_prop
  have hpolar (H : (Fin n → ℝ) → ℝ≥0∞) (hH : Measurable H) :
      (∫⁻ g, H (unitF53 g) ∂stdGauss (Fin n)) =
        W * ∫⁻ s : Metric.sphere (0 : E) 1, H (WithLp.ofLp s.1) ∂σ := by
    rw [BstLean.Part53.gauss_polar_formula (fun g => H (unitF53 g))
      (hH.comp BstLean.Part53.measurable_unitF)]
    simp_rw [BstLean.Part53.unitF_polar]
    change (∫⁻ p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
      H (WithLp.ofLp p.1.1) * Wrad53 (Fin n) p.2.1 ∂σ.prod ν) = _
    rw [lintegral_prod (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
      H (WithLp.ofLp p.1.1) * Wrad53 (Fin n) p.2.1) ((hH.comp (hcoe.comp measurable_fst)).mul
      (hW.comp measurable_snd)).aemeasurable]
    simp_rw [lintegral_const_mul _ hW]
    rw [lintegral_mul_const (f := fun s : Metric.sphere (0 : E) 1 =>
      H (WithLp.ofLp s.1)) W (hH.comp hcoe), mul_comm]
  have hm := hpolar (fun _ => 1) measurable_const
  simp only [lintegral_const, measure_univ, one_mul] at hm
  have hzero : σ Set.univ ≠ 0 :=
    (Measure.measure_univ_ne_zero).2 (Measure.toSphere_ne_zero volume)
  have htop : σ Set.univ ≠ ⊤ := measure_ne_top σ Set.univ
  have hw : W = (σ Set.univ)⁻¹ := by
    calc
      W = ((σ Set.univ)⁻¹ * σ Set.univ) * W := by
        rw [ENNReal.inv_mul_cancel hzero htop, one_mul]
      _ = (σ Set.univ)⁻¹ * (W * σ Set.univ) := by ac_rfl
      _ = (σ Set.univ)⁻¹ := by rw [← hm, mul_one]
  rw [hpolar F hF, hw]
  unfold uniformSphere
  rw [lintegral_smul_measure, lintegral_map hF hcoe]
  rfl

/-- The rank-one quadratic form depends only on the axial coordinate. -/
theorem rk1_quadratic (t : ℝ) (v x : Fin n → ℝ) :
    BstLean.Part50.qA (rk1 t v) x = t * (∑ i, v i * x i) ^ 2 := by
  classical
  unfold BstLean.Part50.qA rk1
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Bingham law is a weighted normalized Gaussian law. -/
theorem lawRK_lintegral_gauss (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (v : Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂lawRK n t v) =
      ∫⁻ g, F (unitF53 g) * ENNReal.ofReal
        (Real.exp (t * (∑ i, v i * unitF53 g i) ^ 2) /
          BstLean.Part50.ZA n (rk1 t v)) ∂stdGauss (Fin n) := by
  have hweight : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal
      (Real.exp (BstLean.Part50.qA (rk1 t v) x) / BstLean.Part50.ZA n (rk1 t v))) := by
    unfold BstLean.Part50.qA rk1
    fun_prop
  unfold lawRK BstLean.Part50.binghamA
  rw [lintegral_withDensity_eq_lintegral_mul _ hweight hF,
    uniformSphere_lintegral_gauss n hn _ (hweight.mul hF)]
  simp only [Pi.mul_apply, rk1_quadratic, mul_comm]

/-- A unit vector can be the first vector of an orthonormal basis. -/
theorem unit_basis_exists (n : ℕ) (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      b ⟨0, by omega⟩ = WithLp.toLp 2 v := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let V : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hinner : inner ℝ V V = 1 := by
    simpa only [V, UnitV, EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct, ← pow_two]
      using hv
  have ho : Orthonormal ℝ (({i0} : Set (Fin n)).domRestrict (fun _ => V)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp i.2).trans (Set.mem_singleton_iff.mp j.2).symm
    simp only [hij, ite_true, Set.domRestrict_apply]
    exact hinner
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb i0 (Set.mem_singleton i0)⟩

/-- Coordinates in an orthonormal basis, with the Euclidean norm convention. -/
noncomputable def basisCoordinates {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).trans
    (b.repr.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm)

theorem basisCoordinates_preserving {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    MeasurePreserving (basisCoordinates b) (stdGauss (Fin n)) (stdGauss (Fin n)) := by
  exact BstLean.Part46.CharFn.gaussian_basis_preserving b

/-- Split a standard Gaussian into its first coordinate and the remaining coordinates. -/
theorem stdGauss_cons_lintegral (k : ℕ) (F : (Fin (k + 1) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ g, F g ∂stdGauss (Fin (k + 1))) =
      ∫⁻ a, ∫⁻ z, F (Fin.cons a z) ∂stdGauss (Fin k)
        ∂ProbabilityTheory.gaussianReal 0 1 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => ProbabilityTheory.gaussianReal 0 1) 0
  have he : (∫⁻ p : ℝ × (Fin k → ℝ), F (Fin.cons p.1 p.2)
      ∂(ProbabilityTheory.gaussianReal 0 1).prod (stdGauss (Fin k))) =
        ∫⁻ g, F g ∂stdGauss (Fin (k + 1)) := by
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, BstLean.Part29.stdGauss] using
      hp.symm.lintegral_comp_emb e.symm.measurableEmbedding F
  rw [← he]
  exact lintegral_prod (fun p : ℝ × (Fin k → ℝ) => F (Fin.cons p.1 p.2))
    (hF.comp (by fun_prop)).aemeasurable

/-- Rotate the Gaussian and then split off the coordinate along the first basis vector. -/
theorem basis_cons_lintegral {k : ℕ}
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (F : (Fin (k + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F g ∂stdGauss (Fin (k + 1))) =
      ∫⁻ a, ∫⁻ z, F ((basisCoordinates b).symm (Fin.cons a z)) ∂stdGauss (Fin k)
        ∂ProbabilityTheory.gaussianReal 0 1 := by
  have h := (basisCoordinates_preserving b).symm.lintegral_comp_emb
    (basisCoordinates b).symm.measurableEmbedding F
  rw [← h]
  exact stdGauss_cons_lintegral k _ (hF.comp (basisCoordinates b).symm.measurable)

noncomputable def basisReconstruct {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (z : Fin n → ℝ) : Fin n → ℝ := WithLp.ofLp (b.repr.symm (WithLp.toLp 2 z))

theorem basisReconstruct_eq_symm {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (z : Fin n → ℝ) :
    basisReconstruct b z = (basisCoordinates b).symm z := rfl

theorem basisReconstruct_add {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (z z' : Fin n → ℝ) :
    basisReconstruct b (z + z') = basisReconstruct b z + basisReconstruct b z' := by
  simp [basisReconstruct]

theorem basisReconstruct_smul {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (c : ℝ) (z : Fin n → ℝ) :
    basisReconstruct b (c • z) = c • basisReconstruct b z := by
  simp [basisReconstruct]

theorem basisReconstruct_sumsq {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (z : Fin n → ℝ) :
    (∑ i, basisReconstruct b z i ^ 2) = ∑ i, z i ^ 2 := by
  have h := congrArg (fun r : ℝ => r ^ 2) (b.repr.symm.norm_map (WithLp.toLp 2 z))
  simpa only [EuclideanSpace.real_norm_sq_eq, basisReconstruct] using h

theorem basisReconstruct_axial {k : ℕ}
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (z : Fin (k + 1) → ℝ) :
    (∑ i, v i * basisReconstruct b z i) = z 0 := by
  have h := b.repr_apply_apply (b.repr.symm (WithLp.toLp 2 z)) 0
  simp only [LinearIsometryEquiv.apply_symm_apply, hb] at h
  symm
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    basisReconstruct, mul_comm] using h

end BstLean.Part56
